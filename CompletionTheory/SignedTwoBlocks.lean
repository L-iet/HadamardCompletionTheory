/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Fintype.Card
@[expose] public section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace CompletionTheory
open Matrix

abbrev SignedTwoState := Bool×Bool×Bool

def signedTwoInt (d : SignedTwoState) : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j => if j=(if d.1 then Fin.rev i else i) then
    (if (if i=0 then d.2.1 else d.2.2) then -1 else 1) else 0

theorem signedTwoInt_orthogonal : ∀ d : SignedTwoState,
    signedTwoInt d*(signedTwoInt d).transpose=1 ∧
    (signedTwoInt d).transpose*signedTwoInt d=1 := by decide +kernel

theorem signedTwoInt_injective : Function.Injective signedTwoInt := by decide +kernel

theorem signedTwoInt_product_closed : ∀ a b : SignedTwoState,∃ c : SignedTwoState,
    signedTwoInt c=signedTwoInt a*signedTwoInt b := by decide +kernel

theorem signedTwoInt_transpose_closed : ∀ a : SignedTwoState,∃ b : SignedTwoState,
    signedTwoInt b=(signedTwoInt a).transpose := by decide +kernel

theorem signedTwoInt_neg_closed : ∀ a : SignedTwoState,∃ b : SignedTwoState,
    signedTwoInt b= -(signedTwoInt a) := by decide +kernel

theorem signedTwoState_card : Nat.card SignedTwoState=8 := by
  simp [Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_bool]

theorem two_block_cross_forces_state (A B R S : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : A.transpose*A=1) (hcross : A*S.transpose+R*B.transpose=0) :
    S= -B*R.transpose*A := by
  have ht := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.transpose) hcross
  simp only [Matrix.transpose_add,Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_zero] at ht
  have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M*A) ht
  simp only [Matrix.add_mul,Matrix.zero_mul,Matrix.mul_assoc,hA,Matrix.mul_one] at hh
  have heq := eq_neg_of_add_eq_zero_left hh
  simpa only [Matrix.neg_mul,Matrix.mul_assoc] using heq

def IsSignedTwoSolution {ι : Type*} (A : ι → ι → SignedTwoState) (R : ι → SignedTwoState) : Prop :=
  ∀ i j,i≠j → signedTwoInt (A i j)*(signedTwoInt (R j)).transpose+
    signedTwoInt (R i)*(signedTwoInt (A j i)).transpose=0

def forcedSignedTwo {ι : Type*} [DecidableEq ι] (A : ι → ι → SignedTwoState)
    (root : ι) (d : SignedTwoState) (i : ι) : Matrix (Fin 2) (Fin 2) ℤ :=
  if i=root then signedTwoInt d else
    -(signedTwoInt (A i root))*(signedTwoInt d).transpose*signedTwoInt (A root i)

theorem signed_two_solution_forced {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (R : ι → SignedTwoState) (hR : IsSignedTwoSolution A R)
    (root i : ι) : signedTwoInt (R i)=forcedSignedTwo A root (R root) i := by
  by_cases hi : i=root
  · subst i;simp [forcedSignedTwo]
  · rw [forcedSignedTwo,if_neg hi]
    exact two_block_cross_forces_state _ _ _ _ (signedTwoInt_orthogonal (A root i)).2
      (hR root i (Ne.symm hi))

theorem signed_two_solution_root_injective {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) :
    Function.Injective (fun R : {R : ι → SignedTwoState // IsSignedTwoSolution A R} => R.val root) := by
  intro R S hroot
  change R.val root=S.val root at hroot
  apply Subtype.ext
  funext i
  apply signedTwoInt_injective
  rw [signed_two_solution_forced A R.val R.property root i,
    signed_two_solution_forced A S.val S.property root i,hroot]

theorem signed_two_solution_count_le_eight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) :
    Nat.card {R : ι → SignedTwoState // IsSignedTwoSolution A R}≤8 := by
  have hh := Nat.card_le_card_of_injective
    (fun R : {R : ι → SignedTwoState // IsSignedTwoSolution A R} => R.val root)
    (signed_two_solution_root_injective A root)
  simpa only [signedTwoState_card] using hh

theorem forcedSignedTwo_is_state {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root i : ι) (d : SignedTwoState) :
    ∃ c : SignedTwoState,forcedSignedTwo A root d i=signedTwoInt c := by
  by_cases hi : i=root
  · exact ⟨d,by simp [forcedSignedTwo,hi]⟩
  · obtain ⟨a,ha⟩ := signedTwoInt_neg_closed (A i root)
    obtain ⟨b,hb⟩ := signedTwoInt_transpose_closed d
    obtain ⟨c,hc⟩ := signedTwoInt_product_closed a b
    obtain ⟨e,he⟩ := signedTwoInt_product_closed c (A root i)
    refine ⟨e,?_⟩
    rw [he,hc,ha,hb]
    simp only [forcedSignedTwo,if_neg hi]

def SignedTwoConsistent {ι : Type*} (A : ι → ι → SignedTwoState)
    (R : ι → Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  ∀ i j,i≠j → signedTwoInt (A i j)*(R j).transpose+R i*(signedTwoInt (A j i)).transpose=0

def IsSignedTwoMatrixSolution {ι : Type*} (A : ι → ι → SignedTwoState)
    (R : ι → Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  (∀ i,∃ d : SignedTwoState,R i=signedTwoInt d) ∧ SignedTwoConsistent A R

theorem signed_two_matrix_solutions_by_roots {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (R : ι → Matrix (Fin 2) (Fin 2) ℤ) :
    IsSignedTwoMatrixSolution A R ↔
      ∃ d : SignedTwoState,R=forcedSignedTwo A root d ∧ SignedTwoConsistent A (forcedSignedTwo A root d) := by
  constructor
  · rintro ⟨hStates,hCross⟩
    obtain ⟨d,hd⟩ := hStates root
    have heq : R=forcedSignedTwo A root d := by
      funext i
      by_cases hi : i=root
      · subst i;simp [forcedSignedTwo,hd]
      · rw [forcedSignedTwo,if_neg hi,← hd]
        exact two_block_cross_forces_state _ _ _ _ (signedTwoInt_orthogonal (A root i)).2
          (hCross root i (Ne.symm hi))
    exact ⟨d,heq,heq ▸ hCross⟩
  · rintro ⟨d,rfl,hCross⟩
    exact ⟨fun i => forcedSignedTwo_is_state A root i d,hCross⟩

instance decidableSignedTwoConsistent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (R : ι → Matrix (Fin 2) (Fin 2) ℤ) :
    Decidable (SignedTwoConsistent A R) := by
  unfold SignedTwoConsistent
  infer_instance

def acceptedTwoRoots {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) : Finset SignedTwoState :=
  Finset.univ.filter (fun d => SignedTwoConsistent A (forcedSignedTwo A root d))

def eightRootFillings {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) : Finset (ι → Matrix (Fin 2) (Fin 2) ℤ) :=
  (acceptedTwoRoots A root).image (fun d => forcedSignedTwo A root d)

theorem eightRootFillings_exact {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (R : ι → Matrix (Fin 2) (Fin 2) ℤ) :
    R∈eightRootFillings A root ↔ IsSignedTwoMatrixSolution A R := by
  constructor
  · intro h
    obtain ⟨d,hd,heq⟩ := Finset.mem_image.mp h
    change d∈Finset.univ.filter (fun d => SignedTwoConsistent A (forcedSignedTwo A root d)) at hd
    have hc := (Finset.mem_filter.mp hd).2
    exact (signed_two_matrix_solutions_by_roots A root R).mpr ⟨d,heq.symm,hc⟩
  · intro h
    obtain ⟨d,heq,hc⟩ := (signed_two_matrix_solutions_by_roots A root R).mp h
    have hd : d∈acceptedTwoRoots A root := by
      change d∈Finset.univ.filter (fun d => SignedTwoConsistent A (forcedSignedTwo A root d))
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩
    exact Finset.mem_image.mpr ⟨d,hd,heq.symm⟩

theorem eightRootFillings_card_le_eight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) : (eightRootFillings A root).card≤8 := by
  calc
    _≤(acceptedTwoRoots A root).card := Finset.card_image_le
    _≤Fintype.card SignedTwoState := Finset.card_le_card (Finset.subset_univ _)
    _=8 := by decide

theorem eight_root_pair_test_slots {ι : Type*} [Fintype ι] :
    Fintype.card (SignedTwoState×ι×ι)=8*(Fintype.card ι)^2 := by
  norm_num [Fintype.card_prod,Fintype.card_bool,pow_two]

def walshTwoInt : Matrix (Fin 2) (Fin 2) ℤ := !![1,1;1,-1]

def signTwoInt (b : Fin 2 → Fin 2 → Bool) : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j => if b i j then -1 else 1

theorem signTwoInt_factor : ∀ b : Fin 2 → Fin 2 → Bool,
    signTwoInt b*(signTwoInt b).transpose=(2 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) →
    ∃ d : SignedTwoState,signedTwoInt d*walshTwoInt=signTwoInt b := by decide +kernel

noncomputable def signedTwoReal (d : SignedTwoState) : Matrix (Fin 2) (Fin 2) ℝ :=
  (signedTwoInt d).map (Int.castRingHom ℝ)

noncomputable def walshTwoReal : Matrix (Fin 2) (Fin 2) ℝ :=
  walshTwoInt.map (Int.castRingHom ℝ)

theorem sign_two_by_two_factor (S : Matrix (Fin 2) (Fin 2) ℝ) (hSign : IsSignMatrix S)
    (hgram : S*S.transpose=(2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    ∃ d : SignedTwoState,S=signedTwoReal d*walshTwoReal := by
  classical
  have hbits (i j : Fin 2) : ∃ b : Bool,S i j=if b then (-1 : ℝ) else 1 := by
    rcases hSign i j with h|h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  choose b hb using hbits
  have hcast : (signTwoInt b).map (Int.castRingHom ℝ)=S := by
    ext i j
    simpa [signTwoInt] using (hb i j).symm
  have hInt : signTwoInt b*(signTwoInt b).transpose=(2 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
    ext i j
    have hh := congrArg (fun M => M i j) hgram
    rw [← hcast] at hh
    simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.map_apply,Matrix.smul_apply,
      smul_eq_mul,Matrix.one_apply] at hh ⊢
    change (∑ k : Fin 2,(signTwoInt b i k : ℝ)*(signTwoInt b j k : ℝ))=(2 : ℝ)*(if i=j then 1 else 0) at hh
    exact_mod_cast hh
  obtain ⟨d,hd⟩ := signTwoInt_factor b hInt
  have hm := congrArg (fun M => M.map (Int.castRingHom ℝ)) hd
  rw [Matrix.map_mul,hcast] at hm
  exact ⟨d,hm.symm⟩

def twoBlock {ι : Type*} (M : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) (i j : ι) :
    Matrix (Fin 2) (Fin 2) ℝ := fun a b => M (a,i) (b,j)

theorem mul_blockDiagonal_transpose_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) (S : ι → Matrix (Fin 2) (Fin 2) ℝ)
    (i j : ι) (a b : Fin 2) :
    (W*(Matrix.blockDiagonal S).transpose) (a,i) (b,j)=(twoBlock W i j*(S j).transpose) a b := by
  simp [Matrix.mul_apply,Matrix.transpose_apply,Matrix.blockDiagonal_apply,Fintype.sum_prod_type,
    mul_ite,twoBlock,eq_comm]

theorem blockDiagonal_mul_transpose_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) (S : ι → Matrix (Fin 2) (Fin 2) ℝ)
    (i j : ι) (a b : Fin 2) :
    (Matrix.blockDiagonal S*W.transpose) (a,i) (b,j)=(S i*(twoBlock W j i).transpose) a b := by
  simp [Matrix.mul_apply,Matrix.transpose_apply,Matrix.blockDiagonal_apply,Fintype.sum_prod_type,
    ite_mul,twoBlock,eq_comm]

theorem blockDiagonal_gram_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Matrix (Fin 2) (Fin 2) ℝ) (i j : ι) (a b : Fin 2) :
    (Matrix.blockDiagonal S*(Matrix.blockDiagonal S).transpose) (a,i) (b,j)=
      if i=j then (S i*(S i).transpose) a b else 0 := by
  rw [Matrix.blockDiagonal_transpose,← Matrix.blockDiagonal_mul]
  rfl

theorem diagonal_patch_gram_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) (S : ι → Matrix (Fin 2) (Fin 2) ℝ)
    (i j : ι) (a b : Fin 2) :
    ((W+Matrix.blockDiagonal S)*(W+Matrix.blockDiagonal S).transpose) (a,i) (b,j)=
      (W*W.transpose) (a,i) (b,j)+(twoBlock W i j*(S j).transpose) a b+
        (S i*(twoBlock W j i).transpose) a b+(if i=j then (S i*(S i).transpose) a b else 0) := by
  rw [Matrix.transpose_add,Matrix.add_mul,Matrix.mul_add,Matrix.mul_add]
  simp only [Matrix.add_apply]
  rw [mul_blockDiagonal_transpose_entry,blockDiagonal_mul_transpose_entry,blockDiagonal_gram_entry]
  ring

theorem diagonal_patch_gram_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) (S : ι → Matrix (Fin 2) (Fin 2) ℝ) (n : ℝ)
    (hZero : ∀ i,twoBlock W i i=0)
    (hW : W*W.transpose=(n-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ)) :
    (W+Matrix.blockDiagonal S)*(W+Matrix.blockDiagonal S).transpose=n • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) ↔
      (∀ i,S i*(S i).transpose=(2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
      ∀ i j,i≠j → twoBlock W i j*(S j).transpose+S i*(twoBlock W j i).transpose=0 := by
  constructor
  · intro hH
    constructor
    · intro i
      ext a b
      have hh := congrArg (fun M => M (a,i) (b,i)) hH
      rw [diagonal_patch_gram_entry,hW,hZero i] at hh
      simp only [Matrix.zero_mul,Matrix.mul_zero,Matrix.zero_apply,add_zero,ite_true] at hh
      by_cases hab : a=b <;>
        simp [Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,hab] at hh ⊢ <;> linarith
    · intro i j hij
      ext a b
      have hh := congrArg (fun M => M (a,i) (b,j)) hH
      rw [diagonal_patch_gram_entry,hW] at hh
      simp [Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,hij] at hh
      simpa only [Matrix.add_apply,Matrix.zero_apply] using hh
  · rintro ⟨hS,hCross⟩
    ext ⟨a,i⟩ ⟨b,j⟩
    rw [diagonal_patch_gram_entry,hW]
    by_cases hij : i=j
    · subst j
      rw [hZero i,hS i]
      by_cases hab : a=b <;>
        simp [Matrix.zero_mul,Matrix.mul_zero,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,hab] <;> ring
    · have hc := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M a b) (hCross i j hij)
      simp only [Matrix.add_apply,Matrix.zero_apply] at hc
      simpa [Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,hij] using hc

theorem int_matrix_gram_cast {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (M : Matrix α β ℤ) (q : ℤ) (hM : M*M.transpose=q • (1 : Matrix α α ℤ)) :
    M.map (Int.castRingHom ℝ)*(M.map (Int.castRingHom ℝ)).transpose=
      (q : ℝ) • (1 : Matrix α α ℝ) := by
  ext i j
  have hh := congrArg (fun A => A i j) hM
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.map_apply,Matrix.smul_apply,
    smul_eq_mul,Matrix.one_apply] at hh ⊢
  change (∑ k,(M i k : ℝ)*(M j k : ℝ))=(q : ℝ)*(if i=j then 1 else 0)
  exact_mod_cast hh

theorem signedTwo_walsh_int_gram : ∀ d : SignedTwoState,
    (signedTwoInt d*walshTwoInt)*(signedTwoInt d*walshTwoInt).transpose=
      (2 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by decide +kernel

theorem signedTwo_walsh_int_sign : ∀ d : SignedTwoState,∀ i j,
    (signedTwoInt d*walshTwoInt) i j=1 ∨ (signedTwoInt d*walshTwoInt) i j= -1 := by decide +kernel

theorem signedTwo_walsh_real_gram (d : SignedTwoState) :
    (signedTwoReal d*walshTwoReal)*(signedTwoReal d*walshTwoReal).transpose=
      (2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hh := int_matrix_gram_cast _ 2 (signedTwo_walsh_int_gram d)
  simpa only [Matrix.map_mul,signedTwoReal,walshTwoReal,Int.cast_ofNat] using hh

theorem signedTwo_walsh_real_sign (d : SignedTwoState) (i j : Fin 2) :
    IsSign ((signedTwoReal d*walshTwoReal) i j) := by
  have hh := signedTwo_walsh_int_sign d i j
  change ((signedTwoInt d).map (Int.castRingHom ℝ)*walshTwoInt.map (Int.castRingHom ℝ)) i j=1 ∨
    ((signedTwoInt d).map (Int.castRingHom ℝ)*walshTwoInt.map (Int.castRingHom ℝ)) i j= -1
  rw [← Matrix.map_mul]
  change (((signedTwoInt d*walshTwoInt) i j : ℤ) : ℝ)=1 ∨
    (((signedTwoInt d*walshTwoInt) i j : ℤ) : ℝ)= -1
  exact_mod_cast hh

def normalizedTwoInt {ι : Type*} [DecidableEq ι] (A : ι → ι → SignedTwoState) :
    Matrix (Fin 2×ι) (Fin 2×ι) ℤ :=
  fun i j => if i.2=j.2 then 0 else (signedTwoInt (A i.2 j.2)*walshTwoInt) i.1 j.1

noncomputable def normalizedTwoReal {ι : Type*} [DecidableEq ι] (A : ι → ι → SignedTwoState) :
    Matrix (Fin 2×ι) (Fin 2×ι) ℝ := (normalizedTwoInt A).map (Int.castRingHom ℝ)

theorem normalizedTwoReal_diagonal {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (i : ι) : twoBlock (normalizedTwoReal A) i i=0 := by
  ext a b
  simp [twoBlock,normalizedTwoReal,normalizedTwoInt]

theorem normalizedTwoReal_offdiagonal {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (i j : ι) (hij : i≠j) :
    twoBlock (normalizedTwoReal A) i j=signedTwoReal (A i j)*walshTwoReal := by
  change twoBlock ((normalizedTwoInt A).map (Int.castRingHom ℝ)) i j=
    (signedTwoInt (A i j)).map (Int.castRingHom ℝ)*walshTwoInt.map (Int.castRingHom ℝ)
  rw [← Matrix.map_mul]
  ext a b
  simp [twoBlock,normalizedTwoInt,hij]

theorem walshTwoReal_gram : walshTwoReal*walshTwoReal.transpose=
    (2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hh := int_matrix_gram_cast walshTwoInt 2 (by decide +kernel)
  simpa only [walshTwoReal,Int.cast_ofNat] using hh

theorem walsh_product_cross (A B R S : Matrix (Fin 2) (Fin 2) ℝ) :
    (A*walshTwoReal)*(S*walshTwoReal).transpose+
      (R*walshTwoReal)*(B*walshTwoReal).transpose=
    (2 : ℝ) • (A*S.transpose+R*B.transpose) := by
  simp only [Matrix.transpose_mul]
  calc
    _=(A*(walshTwoReal*walshTwoReal.transpose))*S.transpose+
      (R*(walshTwoReal*walshTwoReal.transpose))*B.transpose := by simp only [Matrix.mul_assoc]
    _=_ := by
      rw [walshTwoReal_gram]
      simp [Matrix.mul_smul,Matrix.smul_mul,smul_add]

def filledTwoInt {ι : Type*} [DecidableEq ι] (A : ι → ι → SignedTwoState)
    (R : ι → Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2×ι) (Fin 2×ι) ℤ :=
  normalizedTwoInt A+Matrix.blockDiagonal (fun i => R i*walshTwoInt)

noncomputable def filledTwoReal {ι : Type*} [DecidableEq ι] (A : ι → ι → SignedTwoState)
    (R : ι → Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2×ι) (Fin 2×ι) ℝ :=
  (filledTwoInt A R).map (Int.castRingHom ℝ)

theorem filledTwoReal_patch {ι : Type*} [DecidableEq ι] (A : ι → ι → SignedTwoState)
    (R : ι → Matrix (Fin 2) (Fin 2) ℤ) :
    filledTwoReal A R=normalizedTwoReal A+
      Matrix.blockDiagonal (fun i => (R i).map (Int.castRingHom ℝ)*walshTwoReal) := by
  unfold filledTwoReal filledTwoInt
  rw [Matrix.map_add (Int.castRingHom ℝ) (map_add (Int.castRingHom ℝ)),Matrix.blockDiagonal_map _ _ (map_zero _)]
  simp only [Matrix.map_mul]
  rfl

theorem normalized_two_cross_cast {ι : Type*} [DecidableEq ι] (A : ι → ι → SignedTwoState)
    (R : ι → Matrix (Fin 2) (Fin 2) ℤ) (i j : ι) (hij : i≠j) :
    twoBlock (normalizedTwoReal A) i j*((R j).map (Int.castRingHom ℝ)*walshTwoReal).transpose+
      ((R i).map (Int.castRingHom ℝ)*walshTwoReal)*(twoBlock (normalizedTwoReal A) j i).transpose=
    (2 : ℝ) • ((signedTwoInt (A i j)*(R j).transpose+R i*(signedTwoInt (A j i)).transpose).map (Int.castRingHom ℝ)) := by
  rw [normalizedTwoReal_offdiagonal A i j hij,normalizedTwoReal_offdiagonal A j i (Ne.symm hij),walsh_product_cross]
  simp only [Matrix.map_add (Int.castRingHom ℝ) (map_add (Int.castRingHom ℝ)),Matrix.map_mul,Matrix.transpose_map,signedTwoReal]

theorem filledTwoReal_block {ι : Type*} [DecidableEq ι] (A : ι → ι → SignedTwoState)
    (R : ι → Matrix (Fin 2) (Fin 2) ℤ) (i j : ι) :
    twoBlock (filledTwoReal A R) i j=
      if i=j then (R i).map (Int.castRingHom ℝ)*walshTwoReal else twoBlock (normalizedTwoReal A) i j := by
  ext a b
  by_cases hij : i=j
  · subst j
    simp [filledTwoReal_patch,twoBlock,Matrix.blockDiagonal_apply,normalizedTwoReal,normalizedTwoInt]
  · simp [filledTwoReal_patch,twoBlock,Matrix.blockDiagonal_apply,hij]

theorem two_block_solution_hadamard {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : ι → ι → SignedTwoState)
    (hW : normalizedTwoReal A*(normalizedTwoReal A).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (R : ι → Matrix (Fin 2) (Fin 2) ℤ) (hR : IsSignedTwoMatrixSolution A R) :
    Matrix.IsHadamard (filledTwoReal A R) := by
  let S : ι → Matrix (Fin 2) (Fin 2) ℝ := fun i => (R i).map (Int.castRingHom ℝ)*walshTwoReal
  have hS : ∀ i,S i*(S i).transpose=(2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    intro i
    obtain ⟨d,hd⟩ := hR.1 i
    change ((R i).map (Int.castRingHom ℝ)*walshTwoReal)*
      ((R i).map (Int.castRingHom ℝ)*walshTwoReal).transpose=_
    rw [hd]
    exact signedTwo_walsh_real_gram d
  have hCross : ∀ i j,i≠j → twoBlock (normalizedTwoReal A) i j*(S j).transpose+
      S i*(twoBlock (normalizedTwoReal A) j i).transpose=0 := by
    intro i j hij
    change twoBlock (normalizedTwoReal A) i j*((R j).map (Int.castRingHom ℝ)*walshTwoReal).transpose+
      ((R i).map (Int.castRingHom ℝ)*walshTwoReal)*(twoBlock (normalizedTwoReal A) j i).transpose=0
    rw [normalized_two_cross_cast A R i j hij,hR.2 i j hij]
    ext a b
    simp
  have hGram := (diagonal_patch_gram_iff (normalizedTwoReal A) S
    (Fintype.card (Fin 2×ι) : ℝ) (normalizedTwoReal_diagonal A) hW).mpr ⟨hS,hCross⟩
  apply isHadamard_mathlib
  constructor
  · intro ⟨a,i⟩ ⟨b,j⟩
    change IsSign ((twoBlock (filledTwoReal A R) i j) a b)
    rw [filledTwoReal_block]
    by_cases hij : i=j
    · subst j
      rw [if_pos rfl]
      obtain ⟨d,hd⟩ := hR.1 i
      rw [hd]
      exact signedTwo_walsh_real_sign d a b
    · rw [if_neg hij,normalizedTwoReal_offdiagonal A i j hij]
      exact signedTwo_walsh_real_sign (A i j) a b
  · rw [filledTwoReal_patch]
    exact hGram

def IsZeroBlockHadamardFilling {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) : Prop :=
  Matrix.IsHadamard H ∧ ∀ p q,p.2≠q.2 → H p q=W p q

theorem zeroBlockFilling_patch {ι : Type*} [DecidableEq ι]
    (W H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) (hZero : ∀ i,twoBlock W i i=0)
    (hRet : ∀ p q,p.2≠q.2 → H p q=W p q) :
    H=W+Matrix.blockDiagonal (fun i => twoBlock H i i) := by
  ext ⟨a,i⟩ ⟨b,j⟩
  by_cases hij : i=j
  · subst j
    have hz := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M a b) (hZero i)
    change W (a,i) (b,i)=0 at hz
    simp [Matrix.add_apply,Matrix.blockDiagonal_apply,hz,twoBlock]
  · simp only [Matrix.add_apply,Matrix.blockDiagonal_apply,if_neg hij,add_zero]
    exact hRet (a,i) (b,j) hij

theorem filledTwoReal_retains_offdiagonal {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (R : ι → Matrix (Fin 2) (Fin 2) ℤ)
    (p q : Fin 2×ι) (hpq : p.2≠q.2) : filledTwoReal A R p q=normalizedTwoReal A p q := by
  have hh := filledTwoReal_block A R p.2 q.2
  rw [if_neg hpq] at hh
  exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M p.1 q.1) hh

theorem eight_root_actual_fillings_exact {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι)
    (hW : normalizedTwoReal A*(normalizedTwoReal A).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) :
    IsZeroBlockHadamardFilling (normalizedTwoReal A) H ↔
      ∃ R∈eightRootFillings A root,H=filledTwoReal A R := by
  classical
  letI : Nonempty ι := ⟨root⟩
  constructor
  · rintro ⟨hHad,hRet⟩
    let S : ι → Matrix (Fin 2) (Fin 2) ℝ := fun i => twoBlock H i i
    have hPatch : H=normalizedTwoReal A+Matrix.blockDiagonal S :=
      zeroBlockFilling_patch _ H (normalizedTwoReal_diagonal A) hRet
    have hGram := hHad.mul_conjTranspose
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at hGram
    rw [hPatch] at hGram
    have hCrit := (diagonal_patch_gram_iff (normalizedTwoReal A) S
      (Fintype.card (Fin 2×ι) : ℝ) (normalizedTwoReal_diagonal A) hW).mp hGram
    have hSign (i : ι) : IsSignMatrix (S i) := fun a b =>
      Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hHad.apply_mem (a,i) (b,i))
    choose d hd using (fun i => sign_two_by_two_factor (S i) (hSign i) (hCrit.1 i))
    let R : ι → Matrix (Fin 2) (Fin 2) ℤ := fun i => signedTwoInt (d i)
    have hSmap : S=(fun i => (R i).map (Int.castRingHom ℝ)*walshTwoReal) := by
      funext i
      exact hd i
    have hCons : SignedTwoConsistent A R := by
      intro i j hij
      let C := signedTwoInt (A i j)*(R j).transpose+R i*(signedTwoInt (A j i)).transpose
      have hc := hCrit.2 i j hij
      rw [hSmap] at hc
      rw [normalized_two_cross_cast A R i j hij] at hc
      change C=0
      ext a b
      have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M a b) hc
      change (2 : ℝ)*(C a b : ℝ)=0 at he
      have hz : (C a b : ℝ)=0 := by linarith
      exact_mod_cast hz
    have hSol : IsSignedTwoMatrixSolution A R := ⟨fun i => ⟨d i,rfl⟩,hCons⟩
    refine ⟨R,(eightRootFillings_exact A root R).mpr hSol,?_⟩
    rw [filledTwoReal_patch,← hSmap]
    exact hPatch
  · rintro ⟨R,hR,rfl⟩
    exact ⟨two_block_solution_hadamard A hW R ((eightRootFillings_exact A root R).mp hR),
      filledTwoReal_retains_offdiagonal A R⟩

def twoZeroHadamardCandidates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) : Finset (Matrix (Fin 2×ι) (Fin 2×ι) ℤ) :=
  (eightRootFillings A root).image (filledTwoInt A)

theorem twoZeroHadamardCandidates_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) : (twoZeroHadamardCandidates A root).card≤8 :=
  Finset.card_image_le.trans (eightRootFillings_card_le_eight A root)

theorem twoZeroHadamardCandidates_exact {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι)
    (hW : normalizedTwoReal A*(normalizedTwoReal A).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) :
    IsZeroBlockHadamardFilling (normalizedTwoReal A) H ↔
      ∃ K∈twoZeroHadamardCandidates A root,H=K.map (Int.castRingHom ℝ) := by
  rw [eight_root_actual_fillings_exact A root hW H]
  constructor
  · rintro ⟨R,hR,hEq⟩
    exact ⟨filledTwoInt A R,Finset.mem_image.mpr ⟨R,hR,rfl⟩,hEq⟩
  · rintro ⟨K,hK,hEq⟩
    obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hK
    exact ⟨R,hR,hEq⟩

def IsNormalizedTwoZeroWeighing {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) : Prop :=
  (∀ i,twoBlock W i i=0) ∧
  (∀ i j,i≠j → IsSignMatrix (twoBlock W i j) ∧
    twoBlock W i j*(twoBlock W i j).transpose=(2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
  W*W.transpose=((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ)

theorem normalized_two_zero_encoding {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) (hW : IsNormalizedTwoZeroWeighing W) :
    ∃ A : ι → ι → SignedTwoState,normalizedTwoReal A=W := by
  classical
  have hx (i j : ι) : ∃ d : SignedTwoState,i≠j → twoBlock W i j=signedTwoReal d*walshTwoReal := by
    by_cases hij : i=j
    · exact ⟨(false,false,false),fun h => False.elim (h hij)⟩
    · obtain ⟨d,hd⟩ := sign_two_by_two_factor _ (hW.2.1 i j hij).1 (hW.2.1 i j hij).2
      exact ⟨d,fun _ => hd⟩
  choose A hA using hx
  refine ⟨A,?_⟩
  ext ⟨a,i⟩ ⟨b,j⟩
  by_cases hij : i=j
  · subst j
    have h0 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M a b) (hW.1 i)
    have h1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M a b) (normalizedTwoReal_diagonal A i)
    exact h1.trans h0.symm
  · have heq := (normalizedTwoReal_offdiagonal A i j hij).trans (hA i j hij).symm
    exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M a b) heq

theorem normalized_two_zero_fillings_list {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) (hW : IsNormalizedTwoZeroWeighing W) (root : ι) :
    ∃ A : ι → ι → SignedTwoState,normalizedTwoReal A=W ∧
      (twoZeroHadamardCandidates A root).card≤8 ∧
      ∀ H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ,IsZeroBlockHadamardFilling W H ↔
        ∃ K∈twoZeroHadamardCandidates A root,H=K.map (Int.castRingHom ℝ) := by
  obtain ⟨A,hA⟩ := normalized_two_zero_encoding W hW
  refine ⟨A,hA,twoZeroHadamardCandidates_card A root,?_⟩
  intro H
  have hg : normalizedTwoReal A*(normalizedTwoReal A).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) := by
    rw [hA];exact hW.2.2
  rw [← hA]
  exact twoZeroHadamardCandidates_exact A root hg H

inductive IntegerCircuit where
  | lit : ℤ → IntegerCircuit
  | add : IntegerCircuit → IntegerCircuit → IntegerCircuit
  | mul : IntegerCircuit → IntegerCircuit → IntegerCircuit
  | neg : IntegerCircuit → IntegerCircuit
  | divTwo : IntegerCircuit → IntegerCircuit

def IntegerCircuit.eval : IntegerCircuit → ℤ
  | .lit a => a
  | .add a b => a.eval+b.eval
  | .mul a b => a.eval*b.eval
  | .neg a => -a.eval
  | .divTwo a => a.eval/2

def IntegerCircuit.opCount : IntegerCircuit → ℕ
  | .lit _ => 0
  | .add a b => a.opCount+b.opCount+1
  | .mul a b => a.opCount+b.opCount+1
  | .neg a => a.opCount+1
  | .divTwo a => a.opCount+1

abbrev TwoCircuit := Matrix (Fin 2) (Fin 2) IntegerCircuit

def twoCircuitLit (M : Matrix (Fin 2) (Fin 2) ℤ) : TwoCircuit := fun i j => .lit (M i j)
def twoCircuitAdd (A B : TwoCircuit) : TwoCircuit := fun i j => .add (A i j) (B i j)
def twoCircuitNeg (A : TwoCircuit) : TwoCircuit := fun i j => .neg (A i j)
def twoCircuitMul (A B : TwoCircuit) : TwoCircuit := fun i j =>
  .add (.mul (A i 0) (B 0 j)) (.mul (A i 1) (B 1 j))
def twoCircuitEval (A : TwoCircuit) : Matrix (Fin 2) (Fin 2) ℤ := fun i j => (A i j).eval

theorem twoCircuitEval_lit (M : Matrix (Fin 2) (Fin 2) ℤ) : twoCircuitEval (twoCircuitLit M)=M := rfl
theorem twoCircuitEval_add (A B : TwoCircuit) : twoCircuitEval (twoCircuitAdd A B)=twoCircuitEval A+twoCircuitEval B := rfl
theorem twoCircuitEval_neg (A : TwoCircuit) : twoCircuitEval (twoCircuitNeg A)= -twoCircuitEval A := rfl
theorem twoCircuitEval_transpose (A : TwoCircuit) : twoCircuitEval A.transpose=(twoCircuitEval A).transpose := rfl

theorem twoCircuitEval_mul (A B : TwoCircuit) : twoCircuitEval (twoCircuitMul A B)=twoCircuitEval A*twoCircuitEval B := by
  ext i j
  simp [twoCircuitEval,twoCircuitMul,IntegerCircuit.eval,Matrix.mul_apply,Fin.sum_univ_succ]

theorem twoCircuitMul_cost (A B : TwoCircuit) (a b : ℕ)
    (hA : ∀ i j,(A i j).opCount≤a) (hB : ∀ i j,(B i j).opCount≤b) :
    ∀ i j,(twoCircuitMul A B i j).opCount≤2*a+2*b+3 := by
  intro i j
  have h₁ := hA i 0
  have h₂ := hA i 1
  have h₃ := hB 0 j
  have h₄ := hB 1 j
  dsimp [twoCircuitMul,IntegerCircuit.opCount]
  omega

def forcedTwoCircuit {ι : Type*} [DecidableEq ι] (A : ι → ι → SignedTwoState)
    (root : ι) (d : SignedTwoState) (i : ι) : TwoCircuit :=
  if i=root then twoCircuitLit (signedTwoInt d) else
    twoCircuitMul (twoCircuitMul (twoCircuitNeg (twoCircuitLit (signedTwoInt (A i root))))
      (twoCircuitLit (signedTwoInt d)).transpose) (twoCircuitLit (signedTwoInt (A root i)))

theorem forcedTwoCircuit_eval {ι : Type*} [DecidableEq ι] (A : ι → ι → SignedTwoState)
    (root : ι) (d : SignedTwoState) (i : ι) :
    twoCircuitEval (forcedTwoCircuit A root d i)=forcedSignedTwo A root d i := by
  by_cases hi : i=root
  · simp [forcedTwoCircuit,forcedSignedTwo,hi,twoCircuitEval_lit]
  · simp only [forcedTwoCircuit,forcedSignedTwo,if_neg hi,twoCircuitEval_mul,
      twoCircuitEval_neg,twoCircuitEval_transpose,twoCircuitEval_lit]

theorem forcedTwoCircuit_cost {ι : Type*} [DecidableEq ι] (A : ι → ι → SignedTwoState)
    (root : ι) (d : SignedTwoState) (i : ι) :
    ∀ a b,(forcedTwoCircuit A root d i a b).opCount≤13 := by
  by_cases hi : i=root
  · intro a b;simp [forcedTwoCircuit,hi,twoCircuitLit,IntegerCircuit.opCount]
  · rw [forcedTwoCircuit,if_neg hi]
    apply twoCircuitMul_cost _ _ 5 0
    · apply twoCircuitMul_cost _ _ 1 0
      · intro a b;simp [twoCircuitNeg,twoCircuitLit,IntegerCircuit.opCount]
      · intro a b;rfl
    · intro a b;rfl

def crossTwoCircuit {ι : Type*} [DecidableEq ι] (A : ι → ι → SignedTwoState)
    (root : ι) (d : SignedTwoState) (i j : ι) : TwoCircuit :=
  twoCircuitAdd
    (twoCircuitMul (twoCircuitLit (signedTwoInt (A i j))) (forcedTwoCircuit A root d j).transpose)
    (twoCircuitMul (forcedTwoCircuit A root d i) (twoCircuitLit (signedTwoInt (A j i))).transpose)

theorem crossTwoCircuit_eval {ι : Type*} [DecidableEq ι] (A : ι → ι → SignedTwoState)
    (root : ι) (d : SignedTwoState) (i j : ι) :
    twoCircuitEval (crossTwoCircuit A root d i j)=
      signedTwoInt (A i j)*(forcedSignedTwo A root d j).transpose+
        forcedSignedTwo A root d i*(signedTwoInt (A j i)).transpose := by
  simp only [crossTwoCircuit,twoCircuitEval_add,twoCircuitEval_mul,twoCircuitEval_transpose,
    twoCircuitEval_lit,forcedTwoCircuit_eval]

theorem crossTwoCircuit_cost {ι : Type*} [DecidableEq ι] (A : ι → ι → SignedTwoState)
    (root : ι) (d : SignedTwoState) (i j : ι) :
    ∀ a b,(crossTwoCircuit A root d i j a b).opCount≤59 := by
  have hL := twoCircuitMul_cost (twoCircuitLit (signedTwoInt (A i j)))
    (forcedTwoCircuit A root d j).transpose 0 13 (fun _ _ => by rfl)
    (fun a b => forcedTwoCircuit_cost A root d j b a)
  have hR := twoCircuitMul_cost (forcedTwoCircuit A root d i)
    (twoCircuitLit (signedTwoInt (A j i))).transpose 13 0
    (forcedTwoCircuit_cost A root d i) (fun _ _ => by rfl)
  intro a b
  have h₁ := hL a b
  have h₂ := hR a b
  dsimp only [crossTwoCircuit,twoCircuitAdd,IntegerCircuit.opCount]
  omega

def filledEntryCircuit {ι : Type*} [DecidableEq ι] (A : ι → ι → SignedTwoState)
    (root : ι) (d : SignedTwoState) (p q : Fin 2×ι) : IntegerCircuit :=
  .add (if p.2=q.2 then .lit 0 else
    twoCircuitMul (twoCircuitLit (signedTwoInt (A p.2 q.2))) (twoCircuitLit walshTwoInt) p.1 q.1)
    (if p.2=q.2 then twoCircuitMul (forcedTwoCircuit A root d p.2) (twoCircuitLit walshTwoInt) p.1 q.1 else .lit 0)

theorem filledEntryCircuit_eval {ι : Type*} [DecidableEq ι] (A : ι → ι → SignedTwoState)
    (root : ι) (d : SignedTwoState) (p q : Fin 2×ι) :
    (filledEntryCircuit A root d p q).eval=filledTwoInt A (forcedSignedTwo A root d) p q := by
  by_cases hpq : p.2=q.2
  · simp only [filledEntryCircuit,if_pos hpq,IntegerCircuit.eval]
    change 0+twoCircuitEval (twoCircuitMul (forcedTwoCircuit A root d p.2) (twoCircuitLit walshTwoInt)) p.1 q.1=_
    rw [twoCircuitEval_mul,forcedTwoCircuit_eval,twoCircuitEval_lit]
    simp [filledTwoInt,normalizedTwoInt,Matrix.blockDiagonal_apply,hpq]
  · simp only [filledEntryCircuit,if_neg hpq,IntegerCircuit.eval]
    change twoCircuitEval (twoCircuitMul (twoCircuitLit (signedTwoInt (A p.2 q.2))) (twoCircuitLit walshTwoInt)) p.1 q.1+0=_
    rw [twoCircuitEval_mul,twoCircuitEval_lit,twoCircuitEval_lit]
    simp [filledTwoInt,normalizedTwoInt,Matrix.blockDiagonal_apply,hpq]

theorem filledEntryCircuit_cost {ι : Type*} [DecidableEq ι] (A : ι → ι → SignedTwoState)
    (root : ι) (d : SignedTwoState) (p q : Fin 2×ι) :
    (filledEntryCircuit A root d p q).opCount≤33 := by
  have hW := twoCircuitMul_cost (twoCircuitLit (signedTwoInt (A p.2 q.2)))
    (twoCircuitLit walshTwoInt) 0 0 (fun _ _ => by rfl) (fun _ _ => by rfl)
  have hS := twoCircuitMul_cost (forcedTwoCircuit A root d p.2)
    (twoCircuitLit walshTwoInt) 13 0 (forcedTwoCircuit_cost A root d p.2) (fun _ _ => by rfl)
  have h₁ := hW p.1 q.1
  have h₂ := hS p.1 q.1
  by_cases hpq : p.2=q.2
  · rw [hpq] at h₂
    simp only [filledEntryCircuit,hpq,ite_true,IntegerCircuit.opCount]
    omega
  · simp only [filledEntryCircuit,if_neg hpq,IntegerCircuit.opCount]
    omega

def crossTwoCircuitBlockCost {ι : Type*} [DecidableEq ι] (A : ι → ι → SignedTwoState)
    (root : ι) (d : SignedTwoState) (i j : ι) : ℕ :=
  ∑ a : Fin 2,∑ b : Fin 2,(crossTwoCircuit A root d i j a b).opCount

theorem crossTwoCircuitBlockCost_le {ι : Type*} [DecidableEq ι] (A : ι → ι → SignedTwoState)
    (root : ι) (d : SignedTwoState) (i j : ι) : crossTwoCircuitBlockCost A root d i j≤236 := by
  calc
    _≤∑ _ : Fin 2,∑ _ : Fin 2,(59 : ℕ) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact crossTwoCircuit_cost A root d i j a b
    _=236 := by decide

def twoRootCrossArithmeticCost {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) : ℕ :=
  ∑ d : SignedTwoState,∑ i : ι,∑ j : ι,crossTwoCircuitBlockCost A root d i j

def twoRootOutputArithmeticCost {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) : ℕ :=
  ∑ d : SignedTwoState,∑ p : Fin 2×ι,∑ q : Fin 2×ι,(filledEntryCircuit A root d p q).opCount

theorem twoRootCrossArithmeticCost_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) : twoRootCrossArithmeticCost A root≤1888*(Fintype.card ι)^2 := by
  calc
    _≤∑ _ : SignedTwoState,∑ _ : ι,∑ _ : ι,(236 : ℕ) := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact crossTwoCircuitBlockCost_le A root d i j
    _=_ := by simp [Fintype.card_prod,Fintype.card_bool,pow_two];ring

theorem twoRootOutputArithmeticCost_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) : twoRootOutputArithmeticCost A root≤1056*(Fintype.card ι)^2 := by
  calc
    _≤∑ _ : SignedTwoState,∑ _ : Fin 2×ι,∑ _ : Fin 2×ι,(33 : ℕ) := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      exact filledEntryCircuit_cost A root d p q
    _=_ := by simp [Fintype.card_prod,Fintype.card_bool,pow_two];ring

theorem two_root_quadratic_arithmetic_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) :
    twoRootCrossArithmeticCost A root+twoRootOutputArithmeticCost A root≤2944*(Fintype.card ι)^2 := by
  have h₁ := twoRootCrossArithmeticCost_le A root
  have h₂ := twoRootOutputArithmeticCost_le A root
  omega

def acceptedTwoCircuitRoots {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) : Finset SignedTwoState :=
  Finset.univ.filter (fun d => ∀ i j,i≠j → ∀ a b : Fin 2,(crossTwoCircuit A root d i j a b).eval=0)

theorem acceptedTwoCircuitRoots_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) : acceptedTwoCircuitRoots A root=acceptedTwoRoots A root := by
  ext d
  simp only [acceptedTwoCircuitRoots,acceptedTwoRoots,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro h i j hij
    rw [← crossTwoCircuit_eval A root d i j]
    ext a b
    exact h i j hij a b
  · intro h i j hij a b
    have hh := crossTwoCircuit_eval A root d i j
    rw [h i j hij] at hh
    exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M a b) hh

def twoZeroCircuitCandidates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) : Finset (Matrix (Fin 2×ι) (Fin 2×ι) ℤ) :=
  (acceptedTwoCircuitRoots A root).image (fun d => fun p q => (filledEntryCircuit A root d p q).eval)

theorem twoZeroCircuitCandidates_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) : twoZeroCircuitCandidates A root=twoZeroHadamardCandidates A root := by
  unfold twoZeroCircuitCandidates twoZeroHadamardCandidates eightRootFillings
  rw [acceptedTwoCircuitRoots_eq,Finset.image_image]
  have heq : (fun d : SignedTwoState => fun p q => (filledEntryCircuit A root d p q).eval)=
      (fun d : SignedTwoState => filledTwoInt A (forcedSignedTwo A root d)) := by
    funext d p q
    exact filledEntryCircuit_eval A root d p q
  rw [heq]
  rfl

theorem two_root_quadratic_order_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) :
    twoRootCrossArithmeticCost A root+twoRootOutputArithmeticCost A root≤736*(Fintype.card (Fin 2×ι))^2 := by
  calc
    _≤2944*(Fintype.card ι)^2 := two_root_quadratic_arithmetic_bound A root
    _=_ := by simp only [Fintype.card_prod,Fintype.card_fin];ring

theorem normalized_two_zero_quadratic_algorithm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) (hW : IsNormalizedTwoZeroWeighing W) (root : ι) :
    ∃ A : ι → ι → SignedTwoState,normalizedTwoReal A=W ∧
      (twoZeroCircuitCandidates A root).card≤8 ∧
      (∀ H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ,IsZeroBlockHadamardFilling W H ↔
        ∃ K∈twoZeroCircuitCandidates A root,H=K.map (Int.castRingHom ℝ)) ∧
      Fintype.card (SignedTwoState×ι×ι)=8*(Fintype.card ι)^2 ∧
      twoRootCrossArithmeticCost A root+twoRootOutputArithmeticCost A root≤736*(Fintype.card (Fin 2×ι))^2 := by
  obtain ⟨A,hA,hCard,hExact⟩ := normalized_two_zero_fillings_list W hW root
  refine ⟨A,hA,?_,?_,eight_root_pair_test_slots,two_root_quadratic_order_bound A root⟩
  · simpa only [twoZeroCircuitCandidates_eq] using hCard
  · intro H
    simpa only [twoZeroCircuitCandidates_eq] using hExact H

def intTwoBlock {ι : Type*} (M : Matrix (Fin 2×ι) (Fin 2×ι) ℤ) (i j : ι) :
    Matrix (Fin 2) (Fin 2) ℤ := fun a b => M (a,i) (b,j)

def normalizationEntryCircuit (B : Matrix (Fin 2) (Fin 2) ℤ) (a b : Fin 2) : IntegerCircuit :=
  .divTwo (twoCircuitMul (twoCircuitLit B) (twoCircuitLit walshTwoInt.transpose) a b)

theorem normalizationEntryCircuit_eval (B : Matrix (Fin 2) (Fin 2) ℤ) (a b : Fin 2) :
    (normalizationEntryCircuit B a b).eval=(B*walshTwoInt.transpose) a b/2 := by
  change twoCircuitEval (twoCircuitMul (twoCircuitLit B) (twoCircuitLit walshTwoInt.transpose)) a b/2=_
  rw [twoCircuitEval_mul,twoCircuitEval_lit,twoCircuitEval_lit]

theorem normalizationEntryCircuit_cost (B : Matrix (Fin 2) (Fin 2) ℤ) (a b : Fin 2) :
    (normalizationEntryCircuit B a b).opCount≤4 := by
  have hh := twoCircuitMul_cost (twoCircuitLit B) (twoCircuitLit walshTwoInt.transpose) 0 0
    (fun _ _ => by rfl) (fun _ _ => by rfl) a b
  dsimp only [normalizationEntryCircuit,IntegerCircuit.opCount]
  omega

theorem signedTwoInt_recovery : ∀ d : SignedTwoState,∀ a b,
    ((signedTwoInt d*walshTwoInt)*walshTwoInt.transpose) a b/2=signedTwoInt d a b := by
  have hf : walshTwoInt*walshTwoInt.transpose=(2 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by decide +kernel
  intro d a b
  rw [Matrix.mul_assoc,hf,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_apply,smul_eq_mul]
  omega

theorem normalizationEntryCircuit_recovers_state {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (i j : ι) (hij : i≠j) (a b : Fin 2) :
    (normalizationEntryCircuit (intTwoBlock (normalizedTwoInt A) i j) a b).eval=signedTwoInt (A i j) a b := by
  have hB : intTwoBlock (normalizedTwoInt A) i j=signedTwoInt (A i j)*walshTwoInt := by
    ext u v
    simp [intTwoBlock,normalizedTwoInt,hij]
  rw [normalizationEntryCircuit_eval,hB]
  exact signedTwoInt_recovery (A i j) a b

def twoRootNormalizationArithmeticCost {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) : ℕ :=
  ∑ i : ι,∑ j : ι,∑ a : Fin 2,∑ b : Fin 2,
    (normalizationEntryCircuit (intTwoBlock (normalizedTwoInt A) i j) a b).opCount

theorem twoRootNormalizationArithmeticCost_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) : twoRootNormalizationArithmeticCost A≤16*(Fintype.card ι)^2 := by
  calc
    _≤∑ _ : ι,∑ _ : ι,∑ _ : Fin 2,∑ _ : Fin 2,(4 : ℕ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact normalizationEntryCircuit_cost _ a b
    _=_ := by simp [pow_two];ring

theorem two_root_preprocessing_and_arithmetic_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) :
    twoRootNormalizationArithmeticCost A+twoRootCrossArithmeticCost A root+twoRootOutputArithmeticCost A root≤
      740*(Fintype.card (Fin 2×ι))^2 := by
  have h₁ := twoRootNormalizationArithmeticCost_le A
  have h₂ := two_root_quadratic_arithmetic_bound A root
  have hn : 740*(Fintype.card (Fin 2×ι))^2=2960*(Fintype.card ι)^2 := by
    simp only [Fintype.card_prod,Fintype.card_fin]
    ring
  rw [hn]
  omega

def IsEntryPreservingHadamardFilling {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) : Prop :=
  Matrix.IsHadamard H ∧ ∀ p q,W p q≠0 → H p q=W p q

theorem normalized_filling_preservation_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) (hW : IsNormalizedTwoZeroWeighing W) :
    IsEntryPreservingHadamardFilling W H ↔ IsZeroBlockHadamardFilling W H := by
  constructor
  · rintro ⟨hH,hRet⟩
    refine ⟨hH,?_⟩
    rintro ⟨a,i⟩ ⟨b,j⟩ hij
    apply hRet
    have hs := (hW.2.1 i j hij).1 a b
    change IsSign (W (a,i) (b,j)) at hs
    rcases hs with hs|hs <;> simp [hs]
  · rintro ⟨hH,hRet⟩
    refine ⟨hH,?_⟩
    rintro ⟨a,i⟩ ⟨b,j⟩ hNZ
    by_cases hij : i=j
    · subst j
      have hz := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M a b) (hW.1 i)
      exact False.elim (hNZ hz)
    · exact hRet (a,i) (b,j) hij

theorem all_sign_fillings_quadratic_time {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) (hW : IsNormalizedTwoZeroWeighing W) (root : ι) :
    ∃ A : ι → ι → SignedTwoState,normalizedTwoReal A=W ∧
      (twoZeroCircuitCandidates A root).card≤8 ∧
      (∀ H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ,IsEntryPreservingHadamardFilling W H ↔
        ∃ K∈twoZeroCircuitCandidates A root,H=K.map (Int.castRingHom ℝ)) ∧
      (∀ i j,i≠j → ∀ a b : Fin 2,
        (normalizationEntryCircuit (intTwoBlock (normalizedTwoInt A) i j) a b).eval=signedTwoInt (A i j) a b) ∧
      Fintype.card (SignedTwoState×ι×ι)=8*(Fintype.card ι)^2 ∧
      twoRootNormalizationArithmeticCost A+twoRootCrossArithmeticCost A root+twoRootOutputArithmeticCost A root≤
        740*(Fintype.card (Fin 2×ι))^2 := by
  obtain ⟨A,hA,hCard,hExact,hSlots,hCost⟩ := normalized_two_zero_quadratic_algorithm W hW root
  refine ⟨A,hA,hCard,?_,normalizationEntryCircuit_recovers_state A,hSlots,two_root_preprocessing_and_arithmetic_bound A root⟩
  intro H
  rw [normalized_filling_preservation_iff W H hW]
  exact hExact H

end CompletionTheory
