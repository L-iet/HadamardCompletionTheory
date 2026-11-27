/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import PhaseGeometry.DitaBlock
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PhaseGeometry
open scoped Matrix ComplexConjugate

def signPermutationMatrix {ι : Type*} [DecidableEq ι] (s : Equiv.Perm ι) (e : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => if j=s i then e i else 0

def IsSignedPermutation {ι : Type*} [DecidableEq ι] (J : Matrix ι ι ℝ) : Prop :=
  ∃ s : Equiv.Perm ι,∃ e : ι → ℝ,(∀ i,e i=1 ∨ e i= -1) ∧ J=signPermutationMatrix s e

theorem signPermutation_square_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Equiv.Perm ι) (e : ι → ℝ) (i j : ι) :
    (signPermutationMatrix s e*signPermutationMatrix s e) i j=
      if j=s (s i) then e i*e (s i) else 0 := by
  classical
  change (∑ k,(if k=s i then e i else 0)*(if j=s k then e k else 0))=_
  rw [Finset.sum_eq_single (s i)]
  · simp only [if_pos rfl]
    split_ifs <;> simp
  · intro k hk hne
    simp [hne]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))

theorem signed_square_pair_structure {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Equiv.Perm ι) (e : ι → ℝ) (he : ∀ i,e i=1 ∨ e i= -1)
    (hsq : signPermutationMatrix s e*signPermutationMatrix s e= -(1 : Matrix ι ι ℝ)) :
    Function.Involutive s ∧ (∀ i,e (s i)= -e i) ∧ ∀ i,s i ≠ i := by
  have hinv (i : ι) : s (s i)=i := by
    by_contra h
    have hp := congrArg (fun M : Matrix ι ι ℝ => M i (s (s i))) hsq
    rw [signPermutation_square_entry,if_pos rfl] at hp
    have hi : i ≠ s (s i) := Ne.symm h
    simp [Matrix.one_apply,hi] at hp
    rcases he i with h1 | h1 <;> rcases he (s i) with h2 | h2 <;> norm_num [h1,h2] at hp
  have hprod (i : ι) : e i*e (s i)= -1 := by
    have hp := congrArg (fun M : Matrix ι ι ℝ => M i i) hsq
    rw [signPermutation_square_entry,if_pos (hinv i).symm] at hp
    simpa using hp
  have hanti (i : ι) : e (s i)= -e i := by
    have hp := hprod i
    rcases he i with h1 | h1 <;> rcases he (s i) with h2 | h2 <;> norm_num [h1,h2] at hp <;> norm_num [h1,h2]
  refine ⟨hinv,hanti,?_⟩
  intro i hi
  have ha := hanti i
  rw [hi] at ha
  rcases he i with h | h <;> norm_num [h] at ha

theorem signed_pair_bijective {ι : Type*} (s : Equiv.Perm ι) (e : ι → ℝ)
    (he : ∀ i,e i=1 ∨ e i= -1) (hinv : Function.Involutive s) (hanti : ∀ i,e (s i)= -e i) :
    Function.Bijective (Sum.elim (fun p : {i : ι // e i=1} => s p.val) (fun p : {i : ι // e i=1} => p.val)) := by
  constructor
  · intro x y hxy
    rcases x with p | p <;> rcases y with q | q
    · change s p.val=s q.val at hxy
      congr 1
      exact Subtype.ext (s.injective hxy)
    · change s p.val=q.val at hxy
      have h := congrArg e hxy
      rw [hanti p.val,p.property,q.property] at h
      norm_num at h
    · change p.val=s q.val at hxy
      have h := congrArg e hxy
      rw [hanti q.val,p.property,q.property] at h
      norm_num at h
    · change p.val=q.val at hxy
      congr 1
      exact Subtype.ext hxy
  · intro i
    rcases he i with h | h
    · exact ⟨Sum.inr ⟨i,h⟩,rfl⟩
    · refine ⟨Sum.inl ⟨s i,?_⟩,hinv i⟩
      rw [hanti i,h]
      norm_num

noncomputable def signedPairEquiv {ι : Type*} (s : Equiv.Perm ι) (e : ι → ℝ)
    (he : ∀ i,e i=1 ∨ e i= -1) (hinv : Function.Involutive s) (hanti : ∀ i,e (s i)= -e i) :
    ({i : ι // e i=1} ⊕ {i : ι // e i=1}) ≃ ι :=
  Equiv.ofBijective _ (signed_pair_bijective s e he hinv hanti)

theorem positive_sign_card {m : ℕ} (s : Equiv.Perm (Fin (2*m))) (e : Fin (2*m) → ℝ)
    (he : ∀ i,e i=1 ∨ e i= -1) (hinv : Function.Involutive s) (hanti : ∀ i,e (s i)= -e i) :
    Fintype.card {i : Fin (2*m) // e i=1}=m := by
  classical
  have hc := Fintype.card_congr (signedPairEquiv s e he hinv hanti)
  simp only [Fintype.card_sum,Fintype.card_fin] at hc
  omega

theorem signed_pair_coordinates {m : ℕ} (s : Equiv.Perm (Fin (2*m))) (e : Fin (2*m) → ℝ)
    (he : ∀ i,e i=1 ∨ e i= -1) (hinv : Function.Involutive s) (hanti : ∀ i,e (s i)= -e i) :
    ∃ f : (Fin m ⊕ Fin m) ≃ Fin (2*m),∀ a : Fin m,
      e (f (Sum.inl a))= -1 ∧ e (f (Sum.inr a))=1 ∧
      s (f (Sum.inl a))=f (Sum.inr a) ∧ s (f (Sum.inr a))=f (Sum.inl a) := by
  classical
  let P := {i : Fin (2*m) // e i=1}
  have hc : Fintype.card P=m := positive_sign_card s e he hinv hanti
  let p : P ≃ Fin m := (Fintype.equivFin P).trans (finCongr hc)
  let f : (Fin m ⊕ Fin m) ≃ Fin (2*m) :=
    (Equiv.sumCongr p.symm p.symm).trans (signedPairEquiv s e he hinv hanti)
  have hl (a : Fin m) : f (Sum.inl a)=s (p.symm a).val := rfl
  have hr (a : Fin m) : f (Sum.inr a)=(p.symm a).val := rfl
  refine ⟨f,?_⟩
  intro a
  refine ⟨?_,?_,?_,?_⟩
  · rw [hl,hanti,(p.symm a).property]
  · rw [hr]
    exact (p.symm a).property
  · rw [hl,hr,hinv]
  · rw [hl,hr]

theorem signPermutation_left_mul_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Equiv.Perm ι) (e : ι → ℝ) (H : Matrix ι ι ℝ) (i j : ι) :
    (signPermutationMatrix s e*H) i j=e i*H (s i) j := by
  classical
  change (∑ k,(if k=s i then e i else 0)*H k j)=_
  rw [Finset.sum_eq_single (s i)]
  · simp
  · intro k hk hne; simp [hne]
  · intro hnot; exact False.elim (hnot (Finset.mem_univ _))

theorem signPermutation_right_mul_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Equiv.Perm ι) (e : ι → ℝ) (H : Matrix ι ι ℝ)
    (hinv : Function.Involutive s) (i j : ι) :
    (H*signPermutationMatrix s e) i j=H i (s j)*e (s j) := by
  classical
  change (∑ k,H i k*(if j=s k then e k else 0))=_
  rw [Finset.sum_eq_single (s j)]
  · rw [if_pos (hinv j).symm]
  · intro k hk hne
    have heq : j ≠ s k := by
      intro h
      have hh := congrArg s h
      rw [hinv] at hh
      exact hne hh.symm
    simp [heq]
  · intro hnot; exact False.elim (hnot (Finset.mem_univ _))

theorem signed_intertwining_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (sr sc : Equiv.Perm ι) (er ec : ι → ℝ) (H : Matrix ι ι ℝ)
    (hc : Function.Involutive sc)
    (hinter : H*signPermutationMatrix sc ec=signPermutationMatrix sr er*H) (i j : ι) :
    H i (sc j)*ec (sc j)=er i*H (sr i) j := by
  have hh := congrArg (fun M : Matrix ι ι ℝ => M i j) hinter
  simpa only [signPermutation_right_mul_entry sc ec H hc,signPermutation_left_mul_entry] using hh

theorem signed_intertwining_block_form {m : ℕ}
    (H Jr Jc : Matrix (Fin (2*m)) (Fin (2*m)) ℝ)
    (hJr : IsSignedPermutation Jr) (hJc : IsSignedPermutation Jc)
    (hrsq : Jr*Jr= -1) (hcsq : Jc*Jc= -1) (hinter : H*Jc=Jr*H) :
    ∃ fr fc : (Fin m ⊕ Fin m) ≃ Fin (2*m),∀ a b : Fin m,
      H (fr (Sum.inr a)) (fc (Sum.inr b))=H (fr (Sum.inl a)) (fc (Sum.inl b)) ∧
      H (fr (Sum.inl a)) (fc (Sum.inr b))= -H (fr (Sum.inr a)) (fc (Sum.inl b)) := by
  obtain ⟨sr,er,her,rfl⟩ := hJr
  obtain ⟨sc,ec,hec,rfl⟩ := hJc
  obtain ⟨hinvr,hantr,hnfr⟩ := signed_square_pair_structure sr er her hrsq
  obtain ⟨hinvc,hantc,hnfc⟩ := signed_square_pair_structure sc ec hec hcsq
  obtain ⟨fr,hfr⟩ := signed_pair_coordinates sr er her hinvr hantr
  obtain ⟨fc,hfc⟩ := signed_pair_coordinates sc ec hec hinvc hantc
  refine ⟨fr,fc,?_⟩
  intro a b
  obtain ⟨hrneg,hrpos,hrl,hrr⟩ := hfr a
  obtain ⟨hcneg,hcpos,hcl,hcr⟩ := hfc b
  have h1 := signed_intertwining_entry sr sc er ec H hinvc hinter (fr (Sum.inl a)) (fc (Sum.inl b))
  have h2 := signed_intertwining_entry sr sc er ec H hinvc hinter (fr (Sum.inl a)) (fc (Sum.inr b))
  rw [hcl,hcpos,hrneg,hrl] at h1
  rw [hcr,hcneg,hrneg,hrl] at h2
  constructor <;> linarith

def complexRealification {m : ℕ} (Z : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ :=
  Matrix.fromBlocks (fun i j => (Z i j).re) (fun i j => -(Z i j).im)
    (fun i j => (Z i j).im) (fun i j => (Z i j).re)

theorem intertwining_realification_form {m : ℕ}
    (H Jr Jc : Matrix (Fin (2*m)) (Fin (2*m)) ℝ)
    (hJr : IsSignedPermutation Jr) (hJc : IsSignedPermutation Jc)
    (hrsq : Jr*Jr= -1) (hcsq : Jc*Jc= -1) (hinter : H*Jc=Jr*H) :
    ∃ fr fc : (Fin m ⊕ Fin m) ≃ Fin (2*m),∃ Z : Matrix (Fin m) (Fin m) ℂ,
      H.submatrix fr fc=complexRealification Z := by
  obtain ⟨fr,fc,hblock⟩ := signed_intertwining_block_form H Jr Jc hJr hJc hrsq hcsq hinter
  let Z : Matrix (Fin m) (Fin m) ℂ := fun a b =>
    ⟨H (fr (Sum.inl a)) (fc (Sum.inl b)),H (fr (Sum.inr a)) (fc (Sum.inl b))⟩
  refine ⟨fr,fc,Z,?_⟩
  ext i j
  rcases i with a | a <;> rcases j with b | b
  · rfl
  · exact (hblock a b).2
  · rfl
  · exact (hblock a b).1

theorem real_hadamard_entry_sign {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : Matrix.IsHadamard H) (i j : ι) : H i j=1 ∨ H i j= -1 := by
  have hs := (Unitary.mem_iff.mp (hH.apply_mem i j)).1
  have hp : H i j*H i j=1 := by simpa using hs
  have hz : (H i j-1)*(H i j+1)=0 := by nlinarith
  rcases mul_eq_zero.mp hz with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

theorem normalized_sign_pair_fourth_root {a b : ℝ} (ha : a=1 ∨ a= -1) (hb : b=1 ∨ b= -1) :
    IsFourthRoot ((⟨a,b⟩ : ℂ)/(1+Complex.I)) := by
  apply (fourth_root_iff _).mpr
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    norm_num [Complex.ext_iff,div_eq_mul_inv,pow_succ,Complex.inv_def,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]

theorem complexRealification_injective {m : ℕ} : Function.Injective (complexRealification (m := m)) := by
  intro Z W h
  ext a b
  apply Complex.ext
  · exact congrArg (fun M => M (Sum.inl a) (Sum.inl b)) h
  · exact congrArg (fun M => M (Sum.inr a) (Sum.inl b)) h

theorem complexRealification_mul {m : ℕ} (Z W : Matrix (Fin m) (Fin m) ℂ) :
    complexRealification (Z*W)=complexRealification Z*complexRealification W := by
  ext i j
  rcases i with a | a <;> rcases j with b | b <;>
    simp [complexRealification,Matrix.mul_apply,Fintype.sum_sum_type,Complex.re_sum,Complex.im_sum,
      Complex.mul_re,Complex.mul_im,Finset.sum_add_distrib,Finset.sum_sub_distrib,
      Finset.sum_neg_distrib,neg_mul,mul_neg] <;> ring

theorem complexRealification_conjTranspose {m : ℕ} (Z : Matrix (Fin m) (Fin m) ℂ) :
    complexRealification Zᴴ=(complexRealification Z)ᴴ := by
  ext i j
  rcases i with a | a <;> rcases j with b | b <;>
    simp [complexRealification,Matrix.conjTranspose_apply]

theorem complexRealification_nat_smul_one (m k : ℕ) :
    complexRealification ((k : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ))=
      (k : ℝ) • (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) := by
  ext i j
  rcases i with a | a <;> rcases j with b | b <;>
    by_cases hab : a=b <;> simp [complexRealification,Matrix.one_apply,hab]

theorem hadamard_realification_gram {m : ℕ} (Z : Matrix (Fin m) (Fin m) ℂ)
    (hR : Matrix.IsHadamard (complexRealification Z)) :
    Z*Zᴴ=((2*m : ℕ) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) := by
  apply complexRealification_injective
  calc
    _ = complexRealification Z*(complexRealification Z)ᴴ := by rw [complexRealification_mul,complexRealification_conjTranspose]
    _ = ((2*m : ℕ) : ℝ) • (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) := by
      have hc : Fintype.card (Fin m ⊕ Fin m)=2*m := by simp; omega
      have hh := hR.mul_conjTranspose
      rw [hc] at hh
      exact hh
    _ = _ := (complexRealification_nat_smul_one m (2*m)).symm

noncomputable def normalizeComplexMatrix {m : ℕ} (Z : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  (1+Complex.I)⁻¹ • Z

theorem complexRowGram_smul {m : ℕ} (c : ℂ) (Z : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) :
    complexRowGram (c • Z) i j=c*conj c*complexRowGram Z i j := by
  unfold complexRowGram
  simp only [Matrix.smul_apply,smul_eq_mul,map_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem normalized_realification_quaternary {m : ℕ} (Z : Matrix (Fin m) (Fin m) ℂ)
    (hR : Matrix.IsHadamard (complexRealification Z)) : IsQuaternaryHadamard (normalizeComplexMatrix Z) := by
  have hG := hadamard_realification_gram Z hR
  have hZ (i j : Fin m) : complexRowGram Z i j=if i=j then ((2*m : ℕ) : ℂ) else 0 := by
    change (Z*Zᴴ) i j=_
    rw [hG]
    simp [Matrix.one_apply,Matrix.smul_apply,smul_eq_mul]
  have hphi : ((1+Complex.I)⁻¹ : ℂ)*conj ((1+Complex.I)⁻¹)=(1/2 : ℂ) := by
    norm_num [Complex.inv_def,Complex.normSq_apply,Complex.ext_iff,Complex.mul_re,Complex.mul_im]
  refine ⟨?_,?_⟩
  · intro i j
    have ha : (Z i j).re=1 ∨ (Z i j).re= -1 := real_hadamard_entry_sign _ hR (Sum.inl i) (Sum.inl j)
    have hb : (Z i j).im=1 ∨ (Z i j).im= -1 := real_hadamard_entry_sign _ hR (Sum.inr i) (Sum.inl j)
    have he : normalizeComplexMatrix Z i j=(⟨(Z i j).re,(Z i j).im⟩ : ℂ)/(1+Complex.I) := by
      simp only [normalizeComplexMatrix,Matrix.smul_apply,smul_eq_mul,div_eq_mul_inv]
      ring
    rw [he]
    exact normalized_sign_pair_fourth_root ha hb
  · intro i j
    unfold normalizeComplexMatrix
    rw [complexRowGram_smul,hphi,hZ]
    split_ifs
    · push_cast
      ring
    · simp

theorem signed_intertwining_quaternary_forward {m : ℕ}
    (H Jr Jc : Matrix (Fin (2*m)) (Fin (2*m)) ℝ) (hH : Matrix.IsHadamard H)
    (hJr : IsSignedPermutation Jr) (hJc : IsSignedPermutation Jc)
    (hrsq : Jr*Jr= -1) (hcsq : Jc*Jc= -1) (hinter : H*Jc=Jr*H) :
    ∃ fr fc : (Fin m ⊕ Fin m) ≃ Fin (2*m),∃ B : Matrix (Fin m) (Fin m) ℂ,
      IsQuaternaryHadamard B ∧ H.submatrix fr fc=complexRealification ((1+Complex.I) • B) := by
  obtain ⟨fr,fc,Z,hZ⟩ := intertwining_realification_form H Jr Jc hJr hJc hrsq hcsq hinter
  have hR : Matrix.IsHadamard (complexRealification Z) := by
    rw [← hZ]
    exact (Matrix.isHadamard_submatrix_equiv_iff fr fc).mpr hH
  refine ⟨fr,fc,normalizeComplexMatrix Z,normalized_realification_quaternary Z hR,?_⟩
  have hnonzero : (1+Complex.I : ℂ) ≠ 0 := by norm_num [Complex.ext_iff]
  rw [normalizeComplexMatrix,smul_smul,mul_inv_cancel₀ hnonzero,one_smul]
  exact hZ

def canonicalPairSwap (m : ℕ) : Equiv.Perm (Fin m ⊕ Fin m) := Equiv.sumComm _ _
def canonicalPairSign (m : ℕ) : (Fin m ⊕ Fin m) → ℝ := Sum.elim (fun _ => -1) (fun _ => 1)
def canonicalComplexStructure (m : ℕ) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ :=
  signPermutationMatrix (canonicalPairSwap m) (canonicalPairSign m)

theorem canonical_pair_involution (m : ℕ) : Function.Involutive (canonicalPairSwap m) := by
  intro i
  rcases i with a | a <;> rfl

theorem canonicalComplexStructure_signed (m : ℕ) : IsSignedPermutation (canonicalComplexStructure m) := by
  refine ⟨canonicalPairSwap m,canonicalPairSign m,?_,rfl⟩
  intro i
  rcases i with a | a <;> simp [canonicalPairSign]

theorem canonicalComplexStructure_square (m : ℕ) : canonicalComplexStructure m*canonicalComplexStructure m= -1 := by
  ext i j
  change (signPermutationMatrix (canonicalPairSwap m) (canonicalPairSign m)*signPermutationMatrix (canonicalPairSwap m) (canonicalPairSign m)) i j=_
  rw [signPermutation_square_entry,canonical_pair_involution m]
  have hp : canonicalPairSign m i*canonicalPairSign m (canonicalPairSwap m i)= -1 := by
    rcases i with a | a <;> norm_num [canonicalPairSign,canonicalPairSwap]
  rw [hp]
  by_cases h : i=j
  · subst j; simp
  · simp [h,Ne.symm h]

theorem canonicalComplexStructure_intertwines {m : ℕ} (Z : Matrix (Fin m) (Fin m) ℂ) :
    complexRealification Z*canonicalComplexStructure m=canonicalComplexStructure m*complexRealification Z := by
  ext i j
  change (complexRealification Z*signPermutationMatrix (canonicalPairSwap m) (canonicalPairSign m)) i j=
    (signPermutationMatrix (canonicalPairSwap m) (canonicalPairSign m)*complexRealification Z) i j
  rw [signPermutation_right_mul_entry _ _ _ (canonical_pair_involution m),signPermutation_left_mul_entry]
  rcases i with a | a <;> rcases j with b | b <;>
    simp [canonicalPairSwap,canonicalPairSign,complexRealification]

theorem signedPermutation_submatrix {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (J : Matrix ι ι ℝ) (hJ : IsSignedPermutation J) (f : κ ≃ ι) : IsSignedPermutation (J.submatrix f f) := by
  obtain ⟨s,e,he,rfl⟩ := hJ
  refine ⟨(f.trans s).trans f.symm,fun i => e (f i),fun i => he (f i),?_⟩
  ext i j
  change (if f j=s (f i) then e (f i) else 0)=(if j=f.symm (s (f i)) then e (f i) else 0)
  have hi : f j=s (f i) ↔ j=f.symm (s (f i)) := (f.eq_symm_apply).symm
  simp only [hi]

theorem realification_equiv_signed_structures {m : ℕ}
    (H : Matrix (Fin (2*m)) (Fin (2*m)) ℝ)
    (fr fc : (Fin m ⊕ Fin m) ≃ Fin (2*m)) (Z : Matrix (Fin m) (Fin m) ℂ)
    (hH : H.submatrix fr fc=complexRealification Z) :
    ∃ Jr Jc : Matrix (Fin (2*m)) (Fin (2*m)) ℝ,IsSignedPermutation Jr ∧ IsSignedPermutation Jc ∧
      Jr*Jr= -1 ∧ Jc*Jc= -1 ∧ H*Jc=Jr*H := by
  let Jr : Matrix (Fin (2*m)) (Fin (2*m)) ℝ := (canonicalComplexStructure m).submatrix fr.symm fr.symm
  let Jc : Matrix (Fin (2*m)) (Fin (2*m)) ℝ := (canonicalComplexStructure m).submatrix fc.symm fc.symm
  have hh : H=(complexRealification Z).submatrix fr.symm fc.symm := by
    ext i j
    have hv := congrArg (fun M => M (fr.symm i) (fc.symm j)) hH
    simpa only [Matrix.submatrix_apply,Equiv.apply_symm_apply] using hv
  refine ⟨Jr,Jc,signedPermutation_submatrix _ (canonicalComplexStructure_signed m) fr.symm,
    signedPermutation_submatrix _ (canonicalComplexStructure_signed m) fc.symm,?_,?_,?_⟩
  · change (canonicalComplexStructure m).submatrix fr.symm fr.symm*(canonicalComplexStructure m).submatrix fr.symm fr.symm= -1
    rw [Matrix.submatrix_mul_equiv,canonicalComplexStructure_square]
    ext i j
    change -(if fr.symm i=fr.symm j then (1 : ℝ) else 0)= -(if i=j then (1 : ℝ) else 0)
    simp only [fr.symm.injective.eq_iff]
  · change (canonicalComplexStructure m).submatrix fc.symm fc.symm*(canonicalComplexStructure m).submatrix fc.symm fc.symm= -1
    rw [Matrix.submatrix_mul_equiv,canonicalComplexStructure_square]
    ext i j
    change -(if fc.symm i=fc.symm j then (1 : ℝ) else 0)= -(if i=j then (1 : ℝ) else 0)
    simp only [fc.symm.injective.eq_iff]
  · rw [hh]
    change (complexRealification Z).submatrix fr.symm fc.symm*(canonicalComplexStructure m).submatrix fc.symm fc.symm=
      (canonicalComplexStructure m).submatrix fr.symm fr.symm*(complexRealification Z).submatrix fr.symm fc.symm
    rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv,canonicalComplexStructure_intertwines]

theorem signPermutation_transpose {ι : Type*} [DecidableEq ι] (s : Equiv.Perm ι) (e : ι → ℝ) :
    (signPermutationMatrix s e)ᵀ=signPermutationMatrix s.symm (fun i => e (s.symm i)) := by
  ext i j
  change (if i=s j then e j else 0)=(if j=s.symm i then e (s.symm i) else 0)
  by_cases h : j=s.symm i
  · subst j; simp
  · have hi : i ≠ s j := by
      intro hi
      exact h ((s.eq_symm_apply).mpr hi.symm)
    simp [hi,h]

theorem signedPermutation_transpose {ι : Type*} [DecidableEq ι]
    (J : Matrix ι ι ℝ) (hJ : IsSignedPermutation J) : IsSignedPermutation Jᵀ := by
  obtain ⟨s,e,he,rfl⟩ := hJ
  exact ⟨s.symm,fun i => e (s.symm i),fun i => he (s.symm i),signPermutation_transpose s e⟩

theorem signedPermutation_mul_transpose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℝ) (hJ : IsSignedPermutation J) : J*Jᵀ=1 := by
  obtain ⟨s,e,he,rfl⟩ := hJ
  ext i j
  rw [signPermutation_left_mul_entry]
  change e i*(if s i=s j then e j else 0)=(1 : Matrix ι ι ℝ) i j
  by_cases h : i=j
  · subst j
    rcases he i with hi | hi <;> simp [hi]
  · have hs : s i ≠ s j := s.injective.ne h
    simp [hs,h]

theorem signedPermutation_transpose_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℝ) (hJ : IsSignedPermutation J) : Jᵀ*J=1 := by
  simpa only [Matrix.transpose_transpose] using signedPermutation_mul_transpose Jᵀ (signedPermutation_transpose J hJ)

theorem signedPermutation_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J K : Matrix ι ι ℝ) (hJ : IsSignedPermutation J) (hK : IsSignedPermutation K) : IsSignedPermutation (J*K) := by
  obtain ⟨s,e,he,rfl⟩ := hJ
  obtain ⟨t,d,hd,rfl⟩ := hK
  refine ⟨s.trans t,fun i => e i*d (s i),?_,?_⟩
  · intro i
    rcases he i with hi | hi <;> rcases hd (s i) with hj | hj <;> norm_num [hi,hj]
  · ext i j
    rw [signPermutation_left_mul_entry]
    change e i*(if j=t (s i) then d (s i) else 0)=(if j=t (s i) then e i*d (s i) else 0)
    split_ifs <;> simp

theorem signed_structures_under_signed_equivalence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H P Q Jr Jc : Matrix ι ι ℝ) (hP : IsSignedPermutation P) (hQ : IsSignedPermutation Q)
    (hJr : IsSignedPermutation Jr) (hJc : IsSignedPermutation Jc)
    (hrsq : Jr*Jr= -1) (hcsq : Jc*Jc= -1) (hinter : (P*H*Q)*Jc=Jr*(P*H*Q)) :
    ∃ Kr Kc : Matrix ι ι ℝ,IsSignedPermutation Kr ∧ IsSignedPermutation Kc ∧
      Kr*Kr= -1 ∧ Kc*Kc= -1 ∧ H*Kc=Kr*H := by
  let Kr : Matrix ι ι ℝ := Pᵀ*Jr*P
  let Kc : Matrix ι ι ℝ := Q*Jc*Qᵀ
  have hPP := signedPermutation_mul_transpose P hP
  have hPP' := signedPermutation_transpose_mul P hP
  have hQQ := signedPermutation_mul_transpose Q hQ
  have hQQ' := signedPermutation_transpose_mul Q hQ
  refine ⟨Kr,Kc,signedPermutation_mul _ _ (signedPermutation_mul _ _ (signedPermutation_transpose P hP) hJr) hP,
    signedPermutation_mul _ _ (signedPermutation_mul _ _ hQ hJc) (signedPermutation_transpose Q hQ),?_,?_,?_⟩
  · change (Pᵀ*Jr*P)*(Pᵀ*Jr*P)= -1
    calc
      _ = Pᵀ*Jr*(P*Pᵀ)*Jr*P := by simp only [Matrix.mul_assoc]
      _ = Pᵀ*(Jr*Jr)*P := by rw [hPP]; simp only [Matrix.mul_one,Matrix.one_mul,Matrix.mul_assoc]
      _ = -1 := by rw [hrsq]; simp [hPP']
  · change (Q*Jc*Qᵀ)*(Q*Jc*Qᵀ)= -1
    calc
      _ = Q*Jc*(Qᵀ*Q)*Jc*Qᵀ := by simp only [Matrix.mul_assoc]
      _ = Q*(Jc*Jc)*Qᵀ := by rw [hQQ']; simp only [Matrix.mul_one,Matrix.one_mul,Matrix.mul_assoc]
      _ = -1 := by rw [hcsq]; simp [hQQ]
  · have ht := congrArg (fun X : Matrix ι ι ℝ => Pᵀ*X*Qᵀ) hinter
    change H*(Q*Jc*Qᵀ)=(Pᵀ*Jr*P)*H
    have hleft : Pᵀ*((P*H*Q)*Jc)*Qᵀ=H*(Q*Jc*Qᵀ) := by
      calc
        _ = (Pᵀ*P)*H*Q*Jc*Qᵀ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hPP']; simp only [Matrix.one_mul,Matrix.mul_assoc]
    have hright : Pᵀ*(Jr*(P*H*Q))*Qᵀ=(Pᵀ*Jr*P)*H := by
      calc
        _ = Pᵀ*Jr*P*H*(Q*Qᵀ) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hQQ,Matrix.mul_one]
    rw [hleft,hright] at ht
    exact ht

theorem signedPermutation_one {ι : Type*} [DecidableEq ι] : IsSignedPermutation (1 : Matrix ι ι ℝ) := by
  refine ⟨Equiv.refl ι,fun _ => 1,fun _ => Or.inl rfl,?_⟩
  ext i j
  simp [signPermutationMatrix,Matrix.one_apply,eq_comm]

def IsQuaternaryRealificationEquivalent {m : ℕ} (H : Matrix (Fin (2*m)) (Fin (2*m)) ℝ) : Prop :=
  ∃ P Q : Matrix (Fin (2*m)) (Fin (2*m)) ℝ,IsSignedPermutation P ∧ IsSignedPermutation Q ∧
    ∃ fr fc : (Fin m ⊕ Fin m) ≃ Fin (2*m),∃ B : Matrix (Fin m) (Fin m) ℂ,
      IsQuaternaryHadamard B ∧ (P*H*Q).submatrix fr fc=complexRealification ((1+Complex.I) • B)

theorem signed_complex_structure_criterion {m : ℕ}
    (H : Matrix (Fin (2*m)) (Fin (2*m)) ℝ) (hH : Matrix.IsHadamard H) :
    IsQuaternaryRealificationEquivalent H ↔
      ∃ Jr Jc : Matrix (Fin (2*m)) (Fin (2*m)) ℝ,IsSignedPermutation Jr ∧ IsSignedPermutation Jc ∧
        Jr*Jr= -1 ∧ Jc*Jc= -1 ∧ H*Jc=Jr*H := by
  constructor
  · rintro ⟨P,Q,hP,hQ,fr,fc,B,hB,hEq⟩
    obtain ⟨Jr,Jc,hJr,hJc,hrsq,hcsq,hinter⟩ := realification_equiv_signed_structures (P*H*Q) fr fc ((1+Complex.I) • B) hEq
    exact signed_structures_under_signed_equivalence H P Q Jr Jc hP hQ hJr hJc hrsq hcsq hinter
  · rintro ⟨Jr,Jc,hJr,hJc,hrsq,hcsq,hinter⟩
    obtain ⟨fr,fc,B,hB,hEq⟩ := signed_intertwining_quaternary_forward H Jr Jc hH hJr hJc hrsq hcsq hinter
    exact ⟨1,1,signedPermutation_one,signedPermutation_one,fr,fc,B,hB,by simpa only [Matrix.one_mul,Matrix.mul_one] using hEq⟩
end PhaseGeometry
