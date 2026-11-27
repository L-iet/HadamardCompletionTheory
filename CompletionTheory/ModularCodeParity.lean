/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Algebra.Field.ZMod
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Abel
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import CompletionTheory.ModularRowCorrection
public import Mathlib.Data.ZMod.Basic
@[expose] public section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory
open Matrix

theorem integer_sign_dot_max {N : ℕ} (u v : Fin N → ℤ)
    (hu : ∀ j,u j=1 ∨ u j= -1) (hv : ∀ j,v j=1 ∨ v j= -1)
    (hdot : (∑ j,u j*v j)=(N : ℤ)) : u=v := by
  have hsq (j : Fin N) : (u j-v j)^2=2-2*(u j*v j) := by
    rcases hu j with h|h <;> rcases hv j with g|g <;> norm_num [h,g]
  have hsum : (∑ j,(u j-v j)^2)=0 := by
    simp_rw [hsq]
    rw [Finset.sum_sub_distrib,← Finset.mul_sum,hdot]
    simp
    ring
  funext j
  have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (u j-v j))).mp hsum j (Finset.mem_univ j)
  nlinarith

theorem integer_sign_dot_zero_parity {q : ℕ} (u v : Fin (4*q) → ℤ)
    (hu : ∀ j,u j=1 ∨ u j= -1) (hv : ∀ j,v j=1 ∨ v j= -1)
    (hdot : (∑ j,u j*v j)=0) : (∏ j,u j)=(∏ j,v j) := by
  have hsign (j : Fin (4*q)) : u j*v j=1 ∨ u j*v j= -1 := by
    rcases hu j with h|h <;> rcases hv j with g|g <;> simp [h,g]
  have hm := integer_sign_sum_mod_four Finset.univ (fun j => u j*v j) (fun j _ => hsign j)
  have hp := integer_prod_sign Finset.univ (fun j => u j*v j) (fun j _ => hsign j)
  simp only [Finset.card_univ,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat,hdot] at hm
  have hpone : (∏ j,u j*v j)=1 := by
    rcases hp with h|h
    · exact h
    · rw [h] at hm
      omega
  rw [Finset.prod_mul_distrib] at hpone
  rcases integer_prod_sign Finset.univ u (fun j _ => hu j) with h|h <;>
    rcases integer_prod_sign Finset.univ v (fun j _ => hv j) with g|g <;>
    rw [h,g] at hpone ⊢ <;> norm_num at *

theorem modular_class_has_orthogonal_row {q : ℕ} (hq : 0<q) (hodd : q%2=1)
    (P : Matrix (Fin 5) (Fin (4*q)) ℤ)
    (hs : ∀ i j,P i j=1 ∨ P i j= -1)
    (hg : ∀ i j,(∑ k,P i k*P j k)=if i=j then (4*q : ℤ) else 0)
    (v : Fin (4*q) → ℤ) (hv : ∀ k,v k=1 ∨ v k= -1)
    (hm : ∀ i,(q : ℤ)∣∑ k,P i k*v k) : ∃ i,(∑ k,P i k*v k)=0 := by
  rcases modular_five_rows_classification (by decide : 5≤5) hq hodd P hs hg v hv hm with he|⟨i,hi|hi⟩
  · exact ⟨0,he 0⟩
  · obtain ⟨j,hji⟩ := exists_ne i
    refine ⟨j,?_⟩
    rw [hi]
    exact (hg j i).trans (if_neg hji)
  · obtain ⟨j,hji⟩ := exists_ne i
    refine ⟨j,?_⟩
    rw [hi]
    simp only [Pi.neg_apply,mul_neg,Finset.sum_neg_distrib,hg j i,if_neg hji,neg_zero]

theorem partial_frame_row_card_le {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (hN : 0<N) (P : Matrix ι (Fin N) ℝ) (hP : IsPartialHadamard P) : Fintype.card ι≤N := by
  classical
  let j : Fin N := ⟨0,hN⟩
  let f : Fin N → ℝ := fun k => if k=j then 1 else 0
  have hNR : (0 : ℝ)<N := by exact_mod_cast hN
  have hb := rowGram_bessel P (N : ℝ) hNR (by simpa using hP.2) f
  have hrow (i : ι) : (∑ k,P i k*f k)^2=1 := by
    simp only [f,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    exact isSign_sq (hP.1 i j)
  have hnorm : (∑ k,f k^2)=1 := by simp [f]
  simp only [hrow,hnorm,mul_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hb
  exact_mod_cast hb

theorem five_row_modular_family_orthogonal {q : ℕ} (hq : 0<q) (hodd : q%2=1)
    (S : Finset (Fin (4*q) → Bool))
    (hfirst : ∀ x∈S,positiveFirstBit x)
    (hmod : ∀ x∈S,∀ y∈S,(q : ℤ)∣∑ j,modularBitSign (x j)*modularBitSign (y j))
    (a : Fin 5 → Fin (4*q) → Bool) (ha : ∀ i,a i∈S)
    (hgram : ∀ i j,(∑ k,modularBitSign (a i k)*modularBitSign (a j k))=
      if i=j then (4*q : ℤ) else 0) :
    (∀ x∈S,∀ y∈S,x≠y → (∑ j,modularBitSign (x j)*modularBitSign (y j))=0) ∧
      5≤S.card ∧ S.card≤4*q := by
  classical
  let P : Matrix (Fin 5) (Fin (4*q)) ℤ := fun i j => modularBitSign (a i j)
  have hs (i : Fin 5) (j : Fin (4*q)) : P i j=1 ∨ P i j= -1 := modularBitSign_sign _
  have hpar (x : Fin (4*q) → Bool) (hx : x∈S) :
      (∏ j,modularBitSign (x j))=∏ j,P 0 j := by
    obtain ⟨i,hi⟩ := modular_class_has_orthogonal_row hq hodd P hs hgram
      (fun j => modularBitSign (x j)) (fun j => modularBitSign_sign _)
      (fun i => hmod (a i) (ha i) x hx)
    have hp := integer_sign_dot_zero_parity (P i) (fun j => modularBitSign (x j))
      (hs i) (fun j => modularBitSign_sign _) hi
    exact hp.symm.trans (integer_frame_row_parity P hs hgram i 0)
  have hpair (x : Fin (4*q) → Bool) (hx : x∈S) (y : Fin (4*q) → Bool)
      (hy : y∈S) (hne : x≠y) : (∑ j,modularBitSign (x j)*modularBitSign (y j))=0 := by
    have hsg (j : Fin (4*q)) : modularBitSign (x j)*modularBitSign (y j)=1 ∨
        modularBitSign (x j)*modularBitSign (y j)= -1 := by
      rcases modularBitSign_sign (x j) with hh|hh <;>
        rcases modularBitSign_sign (y j) with gg|gg <;> simp [hh,gg]
    have hprod := integer_prod_sign Finset.univ (P 0) (fun j _ => hs 0 j)
    have hprodxy : (∏ j,modularBitSign (x j)*modularBitSign (y j))=1 := by
      rw [Finset.prod_mul_distrib,hpar x hx,hpar y hy]
      rcases hprod with hh|hh <;> rw [hh] <;> norm_num
    have hres := integer_sign_sum_mod_four Finset.univ _ (fun j _ => hsg j)
    simp only [Finset.card_univ,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat,hprodxy] at hres
    have hzerores : (∑ j,modularBitSign (x j)*modularBitSign (y j))%4=0 := by omega
    have hoddZ : (q : ℤ)%2=1 := by exact_mod_cast hodd
    have hhalfmod : (2*(q : ℤ))%4=2 ∧ (-(2*(q : ℤ)))%4=2 := by omega
    have hvals := modular_sign_sum_values hq hodd _ hsg (hmod x hx y hy)
    rcases hvals with hh|hh|hh|hh|hh
    · have hvneg (j : Fin (4*q)) : -modularBitSign (y j)=1 ∨ -modularBitSign (y j)= -1 := by
        rcases modularBitSign_sign (y j) with h|h <;> simp [h]
      have hd : (∑ j,modularBitSign (x j)*(-modularBitSign (y j)))=(4*q : ℤ) := by
        simp only [mul_neg,Finset.sum_neg_distrib,hh,neg_neg]
      have he := integer_sign_dot_max (fun j => modularBitSign (x j))
        (fun j => -modularBitSign (y j)) (fun j => modularBitSign_sign _) hvneg hd
      let j : Fin (4*q) := ⟨0,by omega⟩
      have hxj := hfirst x hx j rfl
      have hyj := hfirst y hy j rfl
      have hej := congrFun he j
      norm_num [hxj,hyj,modularBitSign] at hej
    · rw [hh] at hzerores
      omega
    · exact hh
    · rw [hh] at hzerores
      omega
    · have he := integer_sign_dot_max (fun j => modularBitSign (x j))
        (fun j => modularBitSign (y j)) (fun j => modularBitSign_sign _)
        (fun j => modularBitSign_sign _) hh
      exact (hne (funext (fun j => modularBitSign_injective (congrFun he j)))).elim
  have hainj : Function.Injective a := by
    intro i j hij
    by_contra hne
    have hz := hgram i j
    rw [if_neg hne] at hz
    have hn := hgram i i
    rw [if_pos rfl] at hn
    rw [← hij] at hz
    have hqZ : (0 : ℤ)<q := by exact_mod_cast hq
    omega
  have hlower : 5≤S.card := by
    have hh := Finset.card_le_card (show Finset.univ.image a⊆S from by
      intro x hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact ha i)
    rw [Finset.card_image_of_injective _ hainj] at hh
    simpa using hh
  let W : Matrix S (Fin (4*q)) ℝ := fun x j => (modularBitSign (x.val j) : ℝ)
  have hW : IsPartialHadamard W := by
    constructor
    · intro x j
      rcases modularBitSign_sign (x.val j) with hh|hh <;> simp [W,hh,IsSign]
    · ext x y
      simp only [Matrix.mul_apply,Matrix.transpose_apply,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
      change (∑ j,(modularBitSign (x.val j) : ℝ)*(modularBitSign (y.val j) : ℝ))=
        (4*(q : ℝ))*(if x=y then 1 else 0)
      by_cases hxy : x=y
      · subst y
        rw [if_pos rfl,mul_one]
        have hsquare (j : Fin (4*q)) : (modularBitSign (x.val j) : ℝ)*(modularBitSign (x.val j) : ℝ)=1 := by
          rcases modularBitSign_sign (x.val j) with hh|hh <;> simp [hh]
        simp only [hsquare,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,Nat.cast_mul,Nat.cast_ofNat]
      · rw [if_neg hxy,mul_zero]
        have hv : x.val≠y.val := fun he => hxy (Subtype.ext he)
        exact_mod_cast hpair x.val x.property y.val y.property hv
  have hupper := partial_frame_row_card_le (by omega : 0<4*q) W hW
  exact ⟨hpair,hlower,by simpa using hupper⟩


def IsSelfOrthogonalModularCode {q N : ℕ} (C : Submodule (ZMod q) (Fin N → ZMod q)) : Prop :=
  ∀ u∈C,∀ v∈C,(∑ j,u j*v j)=0

noncomputable def codeSignCandidates {q N : ℕ} (C : Submodule (ZMod q) (Fin N → ZMod q)) :
    Finset (Fin N → Bool) := by
  classical
  exact Finset.univ.filter (fun x => positiveFirstBit x ∧
    (fun j => (modularBitSign (x j) : ZMod q))∈C)

theorem five_rows_remove_code_compatibility {q : ℕ} (hq : 0<q) (hodd : q%2=1)
    (C : Submodule (ZMod q) (Fin (4*q) → ZMod q)) (hC : IsSelfOrthogonalModularCode C)
    (a : Fin 5 → Fin (4*q) → Bool) (ha : ∀ i,a i∈codeSignCandidates C)
    (hgram : ∀ i j,(∑ k,modularBitSign (a i k)*modularBitSign (a j k))=
      if i=j then (4*q : ℤ) else 0) :
    (∀ x∈codeSignCandidates C,∀ y∈codeSignCandidates C,x≠y →
      (∑ j,modularBitSign (x j)*modularBitSign (y j))=0) ∧
      5≤(codeSignCandidates C).card ∧ (codeSignCandidates C).card≤4*q := by
  classical
  apply five_row_modular_family_orthogonal hq hodd (codeSignCandidates C) _ _ a ha hgram
  · intro x hx
    exact (Finset.mem_filter.mp hx).2.1
  · intro x hx y hy
    have hxC := (Finset.mem_filter.mp hx).2.2
    have hyC := (Finset.mem_filter.mp hy).2.2
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
    have hh := hC (fun j => (modularBitSign (x j) : ZMod q)) hxC
      (fun j => (modularBitSign (y j) : ZMod q)) hyC
    simpa only [Int.cast_sum,Int.cast_mul] using hh


theorem same_parity_modular_orthogonal {q : ℕ} (hq : 0<q) (hodd : q%2=1)
    (x y : Fin (4*q) → Bool) (hxfirst : positiveFirstBit x) (hyfirst : positiveFirstBit y)
    (hne : x≠y) (hparity : (∏ j,modularBitSign (x j))=(∏ j,modularBitSign (y j)))
    (hdiv : (q : ℤ)∣∑ j,modularBitSign (x j)*modularBitSign (y j)) :
    (∑ j,modularBitSign (x j)*modularBitSign (y j))=0 := by
  have hsg (j : Fin (4*q)) : modularBitSign (x j)*modularBitSign (y j)=1 ∨
      modularBitSign (x j)*modularBitSign (y j)= -1 := by
    rcases modularBitSign_sign (x j) with hh|hh <;>
      rcases modularBitSign_sign (y j) with gg|gg <;> simp [hh,gg]
  have hprod := integer_prod_sign Finset.univ (fun j => modularBitSign (x j)) (fun j _ => modularBitSign_sign _)
  have hprodxy : (∏ j,modularBitSign (x j)*modularBitSign (y j))=1 := by
    rw [Finset.prod_mul_distrib,← hparity]
    rcases hprod with hh|hh <;> rw [hh] <;> norm_num
  have hres := integer_sign_sum_mod_four Finset.univ _ (fun j _ => hsg j)
  simp only [Finset.card_univ,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat,hprodxy] at hres
  have hzerores : (∑ j,modularBitSign (x j)*modularBitSign (y j))%4=0 := by omega
  have hoddZ : (q : ℤ)%2=1 := by exact_mod_cast hodd
  have hhalfmod : (2*(q : ℤ))%4=2 ∧ (-(2*(q : ℤ)))%4=2 := by omega
  have hvals := modular_sign_sum_values hq hodd _ hsg hdiv
  rcases hvals with hh|hh|hh|hh|hh
  · have hvneg (j : Fin (4*q)) : -modularBitSign (y j)=1 ∨ -modularBitSign (y j)= -1 := by
      rcases modularBitSign_sign (y j) with h|h <;> simp [h]
    have hd : (∑ j,modularBitSign (x j)*(-modularBitSign (y j)))=(4*q : ℤ) := by
      simp only [mul_neg,Finset.sum_neg_distrib,hh,neg_neg]
    have he := integer_sign_dot_max (fun j => modularBitSign (x j))
      (fun j => -modularBitSign (y j)) (fun j => modularBitSign_sign _) hvneg hd
    let j : Fin (4*q) := ⟨0,by omega⟩
    have hxj := hxfirst j rfl
    have hyj := hyfirst j rfl
    have hej := congrFun he j
    norm_num [hxj,hyj,modularBitSign] at hej
  · rw [hh] at hzerores
    omega
  · exact hh
  · rw [hh] at hzerores
    omega
  · have he := integer_sign_dot_max (fun j => modularBitSign (x j))
      (fun j => modularBitSign (y j)) (fun j => modularBitSign_sign _)
      (fun j => modularBitSign_sign _) hh
    exact (hne (funext (fun j => modularBitSign_injective (congrFun he j)))).elim

def signFamilyMatrix {N : ℕ} (S : Finset (Fin N → Bool)) : Matrix S (Fin N) ℝ :=
  fun x j => (modularBitSign (x.val j) : ℝ)

theorem signFamilyMatrix_partial {N : ℕ} (S : Finset (Fin N → Bool))
    (hpair : ∀ x∈S,∀ y∈S,x≠y → (∑ j,modularBitSign (x j)*modularBitSign (y j))=0) :
    IsPartialHadamard (signFamilyMatrix S) := by
  classical
  constructor
  · intro x j
    rcases modularBitSign_sign (x.val j) with hh|hh <;> simp [signFamilyMatrix,hh,IsSign]
  · ext x y
    simp only [Matrix.mul_apply,Matrix.transpose_apply,Fintype.card_fin]
    change (∑ j,(modularBitSign (x.val j) : ℝ)*(modularBitSign (y.val j) : ℝ))=
      (N : ℝ)*(if x=y then 1 else 0)
    by_cases hxy : x=y
    · subst y
      rw [if_pos rfl,mul_one]
      have hsquare (j : Fin N) : (modularBitSign (x.val j) : ℝ)*(modularBitSign (x.val j) : ℝ)=1 := by
        rcases modularBitSign_sign (x.val j) with hh|hh <;> simp [hh]
      simp only [hsquare,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    · rw [if_neg hxy,mul_zero]
      have hv : x.val≠y.val := fun he => hxy (Subtype.ext he)
      exact_mod_cast hpair x.val x.property y.val y.property hv

theorem opposite_parity_class_card_le_four {q : ℕ} (hq : 0<q) (hodd : q%2=1)
    (A : Finset (Fin (4*q) → Bool)) (hfirst : ∀ x∈A,positiveFirstBit x)
    (hmod : ∀ x∈A,∀ y∈A,(q : ℤ)∣∑ j,modularBitSign (x j)*modularBitSign (y j))
    (v : Fin (4*q) → Bool)
    (hcross : ∀ x∈A,(q : ℤ)∣∑ j,modularBitSign (x j)*modularBitSign (v j))
    (hopposite : ∀ x∈A,(∏ j,modularBitSign (x j))≠∏ j,modularBitSign (v j)) : A.card≤4 := by
  classical
  have hprod (x : Fin (4*q) → Bool) : (∏ j,modularBitSign (x j))=1 ∨
      (∏ j,modularBitSign (x j))= -1 := integer_prod_sign Finset.univ _ (fun j _ => modularBitSign_sign _)
  have hequal (x : Fin (4*q) → Bool) (hx : x∈A) (y : Fin (4*q) → Bool) (hy : y∈A) :
      (∏ j,modularBitSign (x j))=∏ j,modularBitSign (y j) := by
    have hxv := hopposite x hx
    have hyv := hopposite y hy
    rcases hprod x with hh|hh <;> rcases hprod y with gg|gg <;>
      rcases hprod v with vv|vv <;> omega
  have hpair (x : Fin (4*q) → Bool) (hx : x∈A) (y : Fin (4*q) → Bool) (hy : y∈A)
      (hne : x≠y) : (∑ j,modularBitSign (x j)*modularBitSign (y j))=0 :=
    same_parity_modular_orthogonal hq hodd x y (hfirst x hx) (hfirst y hy) hne
      (hequal x hx y hy) (hmod x hx y hy)
  have hdot (x : Fin (4*q) → Bool) (hx : x∈A) :
      (∑ j,modularBitSign (x j)*modularBitSign (v j))^2=4*(q : ℤ)^2 := by
    have hsg (j : Fin (4*q)) : modularBitSign (x j)*modularBitSign (v j)=1 ∨
        modularBitSign (x j)*modularBitSign (v j)= -1 := by
      rcases modularBitSign_sign (x j) with hh|hh <;>
        rcases modularBitSign_sign (v j) with gg|gg <;> simp [hh,gg]
    have hp : (∏ j,modularBitSign (x j)*modularBitSign (v j))= -1 := by
      rw [Finset.prod_mul_distrib]
      have hxv := hopposite x hx
      rcases hprod x with hh|hh <;> rcases hprod v with vv|vv <;>
        rw [hh,vv] <;> omega
    have hm := integer_sign_sum_mod_four Finset.univ _ (fun j _ => hsg j)
    simp only [Finset.card_univ,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat,hp] at hm
    have hres : (∑ j,modularBitSign (x j)*modularBitSign (v j))%4=2 := by omega
    have hvv := modular_sign_sum_values hq hodd _ hsg (hcross x hx)
    rcases hvv with hh|hh|hh|hh|hh <;> rw [hh] at hres ⊢ <;> first | nlinarith | omega
  have hpartial := signFamilyMatrix_partial A hpair
  have hqR : (0 : ℝ)<q := by exact_mod_cast hq
  have hgram : signFamilyMatrix A*(signFamilyMatrix A)ᵀ=(4*(q : ℝ)) • 1 := by
    simpa only [Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] using hpartial.2
  have hb := rowGram_bessel (signFamilyMatrix A) (4*(q : ℝ)) (by positivity) hgram
    (fun j => (modularBitSign (v j) : ℝ))
  have hnorm (j : Fin (4*q)) : (modularBitSign (v j) : ℝ)^2=1 := by
    rcases modularBitSign_sign (v j) with hh|hh <;> simp [hh]
  have hinner (x : A) :
      (∑ j,signFamilyMatrix A x j*(modularBitSign (v j) : ℝ))^2=4*(q : ℝ)^2 := by
    have hh : ((∑ j,modularBitSign (x.val j)*modularBitSign (v j) : ℤ) : ℝ)^2=4*(q : ℝ)^2 := by
      exact_mod_cast hdot x.val x.property
    simpa only [Int.cast_sum,Int.cast_mul,signFamilyMatrix] using hh
  simp only [hinner,hnorm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_mul,Nat.cast_ofNat] at hb
  have hc : (Fintype.card A : ℝ)≤4 := by
    by_contra hnot
    have hgt : (4 : ℝ)<Fintype.card A := lt_of_not_ge hnot
    have hp := mul_lt_mul_of_pos_right hgt (show 0<4*(q : ℝ)^2 by positivity)
    nlinarith
  have hcN : Fintype.card A≤4 := by exact_mod_cast hc
  simpa only [Fintype.card_coe] using hcN


noncomputable def signParityClass {N : ℕ} (S : Finset (Fin N → Bool)) (ε : ℤ) :
    Finset (Fin N → Bool) := by
  classical
  exact S.filter (fun x => (∏ j,modularBitSign (x j))=ε)

theorem modular_two_parity_bounds {q : ℕ} (hq : 3≤q) (hodd : q%2=1)
    (S : Finset (Fin (4*q) → Bool))
    (hfirst : ∀ x∈S,positiveFirstBit x)
    (hmod : ∀ x∈S,∀ y∈S,(q : ℤ)∣∑ j,modularBitSign (x j)*modularBitSign (y j)) :
    (∀ x∈S,∀ y∈S,x≠y → (∏ j,modularBitSign (x j))=(∏ j,modularBitSign (y j)) →
      (∑ j,modularBitSign (x j)*modularBitSign (y j))=0) ∧
    ((∃ x∈S,∃ y∈S,(∏ j,modularBitSign (x j))≠∏ j,modularBitSign (y j)) →
      (∀ ε : ℤ,(signParityClass S ε).card≤4) ∧ S.card≤8) ∧
    (9≤S.card → ∀ x∈S,∀ y∈S,x≠y →
      (∑ j,modularBitSign (x j)*modularBitSign (y j))=0) ∧ S.card≤4*q := by
  classical
  have hqp : 0<q := by omega
  have hsame (x : Fin (4*q) → Bool) (hx : x∈S) (y : Fin (4*q) → Bool)
      (hy : y∈S) (hne : x≠y) (hp : (∏ j,modularBitSign (x j))=∏ j,modularBitSign (y j)) :
      (∑ j,modularBitSign (x j)*modularBitSign (y j))=0 :=
    same_parity_modular_orthogonal hqp hodd x y (hfirst x hx) (hfirst y hy) hne hp (hmod x hx y hy)
  have hmixed (hmix : ∃ x∈S,∃ y∈S,(∏ j,modularBitSign (x j))≠∏ j,modularBitSign (y j)) :
      (∀ ε : ℤ,(signParityClass S ε).card≤4) ∧ S.card≤8 := by
    obtain ⟨x,hx,y,hy,hxy⟩ := hmix
    have hclass (ε : ℤ) : (signParityClass S ε).card≤4 := by
      let A := signParityClass S ε
      have hsub : A⊆S := Finset.filter_subset _ _
      have hAf (z : Fin (4*q) → Bool) (hz : z∈A) : positiveFirstBit z := hfirst z (hsub hz)
      have hAm (z : Fin (4*q) → Bool) (hz : z∈A) (w : Fin (4*q) → Bool) (hw : w∈A) :=
        hmod z (hsub hz) w (hsub hw)
      by_cases he : ε=∏ j,modularBitSign (x j)
      · apply opposite_parity_class_card_le_four hqp hodd A hAf hAm y
          (fun z hz => hmod z (hsub hz) y hy)
        intro z hz
        have hzε := (Finset.mem_filter.mp hz).2
        rw [hzε,he]
        exact hxy
      · apply opposite_parity_class_card_le_four hqp hodd A hAf hAm x
          (fun z hz => hmod z (hsub hz) x hx)
        intro z hz
        have hzε := (Finset.mem_filter.mp hz).2
        rw [hzε]
        exact he
    refine ⟨hclass,?_⟩
    have hcard := Finset.card_filter_add_card_filter_not (s := S) (fun x => (∏ j,modularBitSign (x j))=(1 : ℤ))
    have hneg : S.filter (fun x => ¬ (∏ j,modularBitSign (x j))=(1 : ℤ))=signParityClass S (-1) := by
      ext z
      have hp := integer_prod_sign Finset.univ (fun j => modularBitSign (z j)) (fun j _ => modularBitSign_sign _)
      simp only [signParityClass,Finset.mem_filter]
      rcases hp with hh|hh <;> simp [hh]
    rw [hneg] at hcard
    change (signParityClass S 1).card+(signParityClass S (-1)).card=S.card at hcard
    have := hclass 1
    have := hclass (-1)
    omega
  have hlarge (h9 : 9≤S.card) (x : Fin (4*q) → Bool) (hx : x∈S)
      (y : Fin (4*q) → Bool) (hy : y∈S) (hne : x≠y) :
      (∑ j,modularBitSign (x j)*modularBitSign (y j))=0 := by
    apply hsame x hx y hy hne
    by_contra hn
    have hh := (hmixed ⟨x,hx,y,hy,hn⟩).2
    omega
  refine ⟨hsame,hmixed,hlarge,?_⟩
  by_cases hmix : ∃ x∈S,∃ y∈S,(∏ j,modularBitSign (x j))≠∏ j,modularBitSign (y j)
  · have := (hmixed hmix).2
    omega
  · have horth (x : Fin (4*q) → Bool) (hx : x∈S) (y : Fin (4*q) → Bool) (hy : y∈S)
        (hne : x≠y) : (∑ j,modularBitSign (x j)*modularBitSign (y j))=0 := by
      apply hsame x hx y hy hne
      by_contra hn
      exact hmix ⟨x,hx,y,hy,hn⟩
    have hh := partial_frame_row_card_le (by omega : 0<4*q) (signFamilyMatrix S) (signFamilyMatrix_partial S horth)
    simpa only [Fintype.card_coe] using hh


def eightClassSeed (u : Fin 3 → Bool) : Fin 4 → Bool := Fin.cases false u

def repeatFourCode {q : ℕ} (u : Fin 3 → Bool) : Fin (4*q) → Bool :=
  fun j => eightClassSeed u (finProdFinEquiv.symm j).1

theorem repeatFourCode_injective {q : ℕ} (hq : 0<q) :
    Function.Injective (repeatFourCode (q := q)) := by
  intro u v huv
  funext i
  let j := finProdFinEquiv (i.succ,(⟨0,hq⟩ : Fin q))
  have hh := congrFun huv j
  simpa only [repeatFourCode,j,Equiv.symm_apply_apply,eightClassSeed,Fin.cases_succ] using hh

theorem repeatFourCode_first {q : ℕ} (hq : 0<q) (u : Fin 3 → Bool) :
    positiveFirstBit (repeatFourCode (q := q) u) := by
  intro j hj
  have hj0 : j=finProdFinEquiv ((0 : Fin 4),(⟨0,hq⟩ : Fin q)) := by
    apply Fin.ext
    simpa [finProdFinEquiv] using hj
  rw [hj0]
  simp only [repeatFourCode,Equiv.symm_apply_apply,eightClassSeed,Fin.cases_zero]

theorem repeatFourCode_inner {q : ℕ} (u v : Fin 3 → Bool) :
    (∑ j,modularBitSign (repeatFourCode (q := q) u j)*modularBitSign (repeatFourCode v j))=
      (q : ℤ)*(∑ i,modularBitSign (eightClassSeed u i)*modularBitSign (eightClassSeed v i)) := by
  have hh := Equiv.sum_comp (finProdFinEquiv : Fin 4×Fin q ≃ Fin (4*q))
    (fun j => modularBitSign (repeatFourCode u j)*modularBitSign (repeatFourCode v j))
  simp only [repeatFourCode,Equiv.symm_apply_apply] at hh
  simp only [repeatFourCode]
  rw [← hh,Fintype.sum_prod_type]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [← Finset.mul_sum]

theorem repeatFourCode_product {q : ℕ} (u : Fin 3 → Bool) :
    (∏ j,modularBitSign (repeatFourCode (q := q) u j))=
      (∏ i,modularBitSign (eightClassSeed u i))^q := by
  have hh := Equiv.prod_comp (finProdFinEquiv : Fin 4×Fin q ≃ Fin (4*q))
    (fun j => modularBitSign (repeatFourCode u j))
  simp only [repeatFourCode,Equiv.symm_apply_apply] at hh
  simp only [repeatFourCode]
  rw [← hh,Fintype.prod_prod_type]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [Finset.prod_pow]

theorem repeatFourCode_odd_product {q : ℕ} (hodd : q%2=1) (u : Fin 3 → Bool) :
    (∏ j,modularBitSign (repeatFourCode (q := q) u j))=
      ∏ i,modularBitSign (eightClassSeed u i) := by
  rw [repeatFourCode_product]
  have hp := integer_prod_sign Finset.univ (fun i => modularBitSign (eightClassSeed u i))
    (fun i _ => modularBitSign_sign _)
  rcases hp with hp|hp
  · rw [hp,one_pow]
  · rw [hp,neg_one_pow_eq_ite]
    have he : ¬ Even q := by
      rintro ⟨k,hk⟩
      omega
    simp [he]

theorem modular_two_parity_bound_sharp (q : ℕ) (hq : 0<q) (hodd : q%2=1) :
    ∃ S : Finset (Fin (4*q) → Bool),S.card=8 ∧
      (∀ x∈S,positiveFirstBit x) ∧
      (∀ x∈S,∀ y∈S,(q : ℤ)∣∑ j,modularBitSign (x j)*modularBitSign (y j)) ∧
      (signParityClass S 1).card=4 ∧ (signParityClass S (-1)).card=4 := by
  classical
  let S := Finset.univ.image (repeatFourCode (q := q))
  have hcard : S.card=8 := by
    rw [Finset.card_image_of_injective _ (repeatFourCode_injective hq)]
    simp
  have hparity (ε : ℤ) : signParityClass S ε=
      (Finset.univ.filter (fun u : Fin 3 → Bool =>
        (∏ i,modularBitSign (eightClassSeed u i))=ε)).image (repeatFourCode (q := q)) := by
    ext x
    simp only [signParityClass,S,Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨⟨u,rfl⟩,hu⟩
      exact ⟨u,by simpa only [repeatFourCode_odd_product hodd] using hu,rfl⟩
    · rintro ⟨u,hu,rfl⟩
      exact ⟨⟨u,rfl⟩,by simpa only [repeatFourCode_odd_product hodd] using hu⟩
  have hp1 : (Finset.univ.filter (fun u : Fin 3 → Bool =>
      (∏ i,modularBitSign (eightClassSeed u i))=(1 : ℤ))).card=4 := by decide +kernel
  have hpn : (Finset.univ.filter (fun u : Fin 3 → Bool =>
      (∏ i,modularBitSign (eightClassSeed u i))=(-1 : ℤ))).card=4 := by decide +kernel
  refine ⟨S,hcard,?_,?_,?_,?_⟩
  · intro x hx
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hx
    exact repeatFourCode_first hq u
  · intro x hx y hy
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hy
    rw [repeatFourCode_inner]
    exact dvd_mul_right _ _
  · rw [hparity,Finset.card_image_of_injective _ (repeatFourCode_injective hq)]
    exact hp1
  · rw [hparity,Finset.card_image_of_injective _ (repeatFourCode_injective hq)]
    exact hpn


section Pivot
open Module Submodule

def bilinearPivotHyperplane {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (C : Submodule K V) (v : V) : Submodule K V :=
  C ⊓ LinearMap.ker (B v)

def bilinearCodePivot {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (C : Submodule K V) (v : V) : Submodule K V :=
  bilinearPivotHyperplane B C v ⊔ K ∙ v

theorem self_dual_bilinear_pivot {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (hnd : B.Nondegenerate) (C : Submodule K V) (hC : C=B.orthogonal C)
    (v : V) (hv : v∉C) (hvv : B v v=0) :
    bilinearCodePivot B C v=B.orthogonal (bilinearCodePivot B C v) ∧
      finrank K (bilinearPivotHyperplane B C v)+1=finrank K C ∧
      C ⊓ bilinearCodePivot B C v=bilinearPivotHyperplane B C v ∧
      finrank K (bilinearCodePivot B C v)=finrank K C ∧ v∈bilinearCodePivot B C v := by
  classical
  let H := bilinearPivotHyperplane B C v
  let D := bilinearCodePivot B C v
  let f : Module.Dual K C := (B v).comp C.subtype
  have hfn : f≠0 := by
    intro hf
    apply hv
    rw [hC]
    intro c hc
    have hh := LinearMap.congr_fun hf ⟨c,hc⟩
    change B v c=0 at hh
    rw [hB.eq c v]
    exact hh
  have hmap : (LinearMap.ker f).map C.subtype=H := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y.property,hy⟩
    · rintro ⟨hxC,hx0⟩
      exact ⟨⟨x,hxC⟩,hx0,rfl⟩
  have hHrank : finrank K H+1=finrank K C := by
    have hh := Module.Dual.finrank_ker_add_one_of_ne_zero hfn
    rw [← Submodule.finrank_map_subtype_eq C (LinearMap.ker f),hmap] at hh
    exact hh
  have hv0 : v≠0 := by intro hh; exact hv (hh ▸ C.zero_mem)
  have hinf : H ⊓ K ∙ v=⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hx.2
    by_cases ha0 : a=0
    · rw [ha0,zero_smul] at ha
      exact ha.symm ▸ (Submodule.zero_mem _)
    · have hh : a • v∈C := ha.symm ▸ hx.1.1
      have hvc : v∈C := by
        have hc := C.smul_mem a⁻¹ hh
        simpa only [smul_smul,inv_mul_cancel₀ ha0,one_smul] using hc
      exact (hv hvc).elim
  have hDrank : finrank K D=finrank K C := by
    have hh := Submodule.finrank_sup_add_finrank_inf_eq H (K ∙ v)
    rw [hinf,finrank_bot,add_zero,finrank_span_singleton hv0] at hh
    change finrank K D=finrank K H+1 at hh
    omega
  have hDorth : D≤B.orthogonal D := by
    intro x hx y hy
    obtain ⟨h1,hh1,z1,hz1,rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hz1
    obtain ⟨h2,hh2,z2,hz2,rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨b,hb⟩ := Submodule.mem_span_singleton.mp hz2
    rw [← ha,← hb]
    have h12 : B h2 h1=0 := by
      have hh : h1∈B.orthogonal C := hC ▸ hh1.1
      exact hh h2 hh2.1
    have h1v : B v h1=0 := hh1.2
    have h2v : B h2 v=0 := by rw [hB.eq h2 v]; exact hh2.2
    simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,h12,h1v,h2v,hvv,mul_zero,zero_mul,add_zero]
  have hCdim : finrank K C+finrank K C=finrank K V := by
    have hh := B.finrank_add_finrank_orthogonal' C
    rw [← hC,hnd.ker_eq_bot,inf_bot_eq,finrank_bot,add_zero] at hh
    exact hh
  have horthRank : finrank K (B.orthogonal D)=finrank K D := by
    rw [B.finrank_orthogonal hnd D,hDrank]
    omega
  have hself : D=B.orthogonal D := Submodule.eq_of_le_of_finrank_le hDorth horthRank.le
  have hinter : C ⊓ D=H := by
    apply le_antisymm
    · intro x hx
      obtain ⟨h,hh,z,hz,heq⟩ := Submodule.mem_sup.mp hx.2
      obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hz
      by_cases ha0 : a=0
      · rw [ha0,zero_smul] at ha
        have hxH : h=x := by rw [← ha,add_zero] at heq; exact heq
        exact hxH ▸ hh
      · have hc : a • v∈C := by
          rw [ha]
          have hz' : z=x-h := by rw [← heq]; abel
          rw [hz']
          exact C.sub_mem hx.1 hh.1
        have hvc : v∈C := by
          have hi := C.smul_mem a⁻¹ hc
          simpa only [smul_smul,inv_mul_cancel₀ ha0,one_smul] using hi
        exact (hv hvc).elim
    · intro x hx
      exact ⟨hx.1,Submodule.mem_sup_left hx⟩
  exact ⟨hself,hHrank,hinter,hDrank,Submodule.mem_sup_right (Submodule.mem_span_singleton.mpr ⟨1,one_smul _ _⟩)⟩

def coordinateDotForm (K : Type*) [Field K] (N : ℕ) : LinearMap.BilinForm K (Fin N → K) :=
  dotProductBilin K K

theorem coordinateDotForm_symm (K : Type*) [Field K] (N : ℕ) :
    (coordinateDotForm K N).IsSymm := ⟨fun x y => dotProduct_comm x y⟩

theorem coordinateDotForm_nondegenerate (K : Type*) [Field K] (N : ℕ) :
    (coordinateDotForm K N).Nondegenerate := by
  classical
  constructor
  · intro u hu
    funext i
    have hh := hu (Pi.single i 1)
    simpa [coordinateDotForm,dotProduct,Pi.single_apply,mul_ite] using hh
  · intro u hu
    funext i
    have hh := hu (Pi.single i 1)
    simpa [coordinateDotForm,dotProduct,Pi.single_apply,ite_mul] using hh

theorem self_dual_coordinate_pivot {K : Type*} [Field K] {N : ℕ}
    (C : Submodule K (Fin N → K)) (hC : C=(coordinateDotForm K N).orthogonal C)
    (v : Fin N → K) (hv : v∉C) (hvv : (∑ j,v j*v j)=0) :
    bilinearCodePivot (coordinateDotForm K N) C v=
      (coordinateDotForm K N).orthogonal (bilinearCodePivot (coordinateDotForm K N) C v) ∧
      finrank K ↥(C ⊓ bilinearCodePivot (coordinateDotForm K N) C v)=N/2-1 ∧
      v∈bilinearCodePivot (coordinateDotForm K N) C v ∧
      bilinearCodePivot (coordinateDotForm K N) C v≠C := by
  have hh := self_dual_bilinear_pivot (coordinateDotForm K N) (coordinateDotForm_symm K N)
    (coordinateDotForm_nondegenerate K N) C hC v hv hvv
  have hdim : finrank K C+finrank K C=N := by
    have hc := (coordinateDotForm K N).finrank_add_finrank_orthogonal' C
    rw [← hC,(coordinateDotForm_nondegenerate K N).ker_eq_bot,inf_bot_eq,finrank_bot,add_zero] at hc
    simpa only [Module.finrank_pi_fintype,Module.finrank_self,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,Nat.cast_id] using hc
  refine ⟨hh.1,?_,hh.2.2.2.2,?_⟩
  · rw [hh.2.2.1]
    omega
  · intro heq
    have hvD := hh.2.2.2.2
    rw [heq] at hvD
    exact hv hvD


end Pivot


noncomputable def signCodePivot {p : ℕ} [Fact p.Prime]
    (C : Submodule (ZMod p) (Fin (4*p) → ZMod p)) (v : Fin (4*p) → Bool) :
    Submodule (ZMod p) (Fin (4*p) → ZMod p) :=
  bilinearCodePivot (coordinateDotForm (ZMod p) (4*p)) C (fun j => (modularBitSign (v j) : ZMod p))

theorem self_dual_sign_code_pivot {p : ℕ} [Fact p.Prime]
    (C : Submodule (ZMod p) (Fin (4*p) → ZMod p))
    (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C)
    (v : Fin (4*p) → Bool) (hfirst : positiveFirstBit v)
    (hv : (fun j => (modularBitSign (v j) : ZMod p))∉C)
    (horth : ∀ x∈codeSignCandidates C,(∑ j,modularBitSign (x j)*modularBitSign (v j))=0) :
    signCodePivot C v=(coordinateDotForm (ZMod p) (4*p)).orthogonal (signCodePivot C v) ∧
      Module.finrank (ZMod p) ↥(C ⊓ signCodePivot C v)=2*p-1 ∧
      codeSignCandidates C ⊂ codeSignCandidates (signCodePivot C v) := by
  classical
  let w : Fin (4*p) → ZMod p := fun j => (modularBitSign (v j) : ZMod p)
  have hw : (∑ j,w j*w j)=0 := by
    have hs (j : Fin (4*p)) : modularBitSign (v j)*modularBitSign (v j)=1 := by
      rcases modularBitSign_sign (v j) with h|h <;> simp [h]
    simp only [w,← Int.cast_mul,hs,Int.cast_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul,mul_one,Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_self,mul_zero]
  have hh := self_dual_coordinate_pivot C hC w hv hw
  have hnew : v∈codeSignCandidates (signCodePivot C v) := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,hfirst,hh.2.2.1⟩
  have hnot : v∉codeSignCandidates C := by
    intro hvC
    exact hv (Finset.mem_filter.mp hvC).2.2
  have hsub : codeSignCandidates C⊆codeSignCandidates (signCodePivot C v) := by
    intro x hx
    obtain ⟨hxfirst,hxC⟩ := (Finset.mem_filter.mp hx).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,hxfirst,?_⟩
    apply Submodule.mem_sup_left
    refine ⟨hxC,?_⟩
    change (∑ j,(modularBitSign (v j) : ZMod p)*(modularBitSign (x j) : ZMod p))=0
    have hi := horth x hx
    have hi' : ((∑ j,modularBitSign (x j)*modularBitSign (v j) : ℤ) : ZMod p)=0 := by rw [hi,Int.cast_zero]
    simpa only [Int.cast_sum,Int.cast_mul,mul_comm] using hi'
  refine ⟨hh.1,?_,?_⟩
  · change Module.finrank (ZMod p) ↥(C ⊓ bilinearCodePivot (coordinateDotForm (ZMod p) (4*p)) C w)=2*p-1
    rw [hh.2.1]
    omega
  · apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hsub,?_⟩
    intro heq
    rw [← heq] at hnew
    exact hnot hnew

theorem terminal_code_preserving_no_new_signs {q : ℕ} (hq : 0<q) (hodd : q%2=1)
    (C : Submodule (ZMod q) (Fin (4*q) → ZMod q))
    (a : Fin 5 → Fin (4*q) → Bool) (ha : ∀ i,a i∈codeSignCandidates C)
    (hgram : ∀ i j,(∑ k,modularBitSign (a i k)*modularBitSign (a j k))=
      if i=j then (4*q : ℤ) else 0)
    (hterminal : ¬∃ v : Fin (4*q) → Bool,positiveFirstBit v ∧ v∉codeSignCandidates C ∧
      ∀ x∈codeSignCandidates C,(∑ j,modularBitSign (x j)*modularBitSign (v j))=0) :
    ∀ D : Submodule (ZMod q) (Fin (4*q) → ZMod q),IsSelfOrthogonalModularCode D →
      codeSignCandidates C⊆codeSignCandidates D → codeSignCandidates D=codeSignCandidates C := by
  classical
  intro D hD hsub
  have haD (i : Fin 5) : a i∈codeSignCandidates D := hsub (ha i)
  have hpair := (five_rows_remove_code_compatibility hq hodd D hD a haD hgram).1
  apply Finset.Subset.antisymm _ hsub
  intro v hv
  by_contra hn
  apply hterminal
  refine ⟨v,(Finset.mem_filter.mp hv).2.1,hn,?_⟩
  intro x hx
  have hxv : x≠v := by intro heq; exact hn (heq ▸ hx)
  exact hpair x (hsub hx) v hv hxv

end CompletionTheory
