/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joshua Mark
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.Basic.Real.Star
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace CompletionTheory

open Matrix

/-- A real sign is exactly `1` or `-1`. -/
def IsSign (x : ℝ) : Prop := x = 1 ∨ x = -1

/-- Every entry is a real sign. -/
def IsSignMatrix {ι κ : Type*} (A : Matrix ι κ ℝ) : Prop :=
  ∀ i j, IsSign (A i j)

/-- Orthogonal sign rows with their actual squared row norm. -/
def IsPartialHadamard {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : Matrix ι κ ℝ) : Prop :=
  IsSignMatrix A ∧ A * Aᵀ = (Fintype.card κ : ℝ) • (1 : Matrix ι ι ℝ)

/-- A square sign matrix with its genuine Hadamard Gram identity. -/
def IsHadamard {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : Prop := IsPartialHadamard A

/-- A weighing matrix, with its entry alphabet and exact Gram weight. -/
def IsWeighing {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (weight : ℝ) : Prop :=
  (∀ i j, A i j = 0 ∨ IsSign (A i j)) ∧ A * Aᵀ = weight • 1

theorem isSign_sq {x : ℝ} (h : IsSign x) : x ^ 2 = 1 := by
  rcases h with rfl | rfl <;> norm_num

theorem isSign_neg_iff (x : ℝ) : IsSign (-x) ↔ IsSign x := by
  constructor <;> intro h <;> rcases h with h | h
  · right; linarith
  · left; linarith
  · right; linarith
  · left; linarith

/-- Horizontal concatenation, with a sum type retaining both column sets. -/
def concatenate {ι κ ν : Type*} (A : Matrix ι κ ℝ) (B : Matrix ι ν ℝ) :
    Matrix ι (κ ⊕ ν) ℝ := fun i j => Sum.elim (A i) (B i) j

theorem concatenate_sign {ι κ ν : Type*} {A : Matrix ι κ ℝ} {B : Matrix ι ν ℝ}
    (hA : IsSignMatrix A) (hB : IsSignMatrix B) :
    IsSignMatrix (concatenate A B) := by
  intro i j
  cases j with
  | inl j => exact hA i j
  | inr j => exact hB i j

/-- Exact Gram addition, the algebraic step in the conditional half-frame construction. -/
theorem concatenate_gram {ι κ ν : Type*} [Fintype κ] [Fintype ν]
    (A : Matrix ι κ ℝ) (B : Matrix ι ν ℝ) :
    concatenate A B * (concatenate A B)ᵀ = A * Aᵀ + B * Bᵀ := by
  ext i j
  simp [Matrix.mul_apply, concatenate, Fintype.sum_sum_type]

theorem concatenate_partialHadamard {ι κ ν : Type*}
    [Fintype ι] [Fintype κ] [Fintype ν] [DecidableEq ι]
    {A : Matrix ι κ ℝ} {B : Matrix ι ν ℝ}
    (hA : IsPartialHadamard A) (hB : IsPartialHadamard B) :
    IsPartialHadamard (concatenate A B) := by
  refine ⟨concatenate_sign hA.1 hB.1, ?_⟩
  rw [concatenate_gram, hA.2, hB.2]
  simp [Fintype.card_sum, Nat.cast_add, add_smul]

/-- Any orthogonal row transformation preserves the exact weighing Gram identity. -/
theorem orthogonal_row_transform {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q W : Matrix ι ι ℝ) (weight : ℝ)
    (hQ : Q * Qᵀ = 1) (hW : W * Wᵀ = weight • 1) :
    (Q * W) * (Q * W)ᵀ = weight • 1 := by
  calc
    (Q * W) * (Q * W)ᵀ = Q * (W * Wᵀ) * Qᵀ := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = weight • (Q * Qᵀ) := by rw [hW]; simp
    _ = weight • 1 := by rw [hQ]

/-- The orthogonal-design cross identity is sufficient for exact Gram filling. -/
theorem orthogonal_design_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W X : Matrix ι ι ℝ) (k d : ℝ)
    (hW : W * Wᵀ = k • 1) (hX : X * Xᵀ = d • 1)
    (hcross : W * Xᵀ + X * Wᵀ = 0) :
    (W + X) * (W + X)ᵀ = (k + d) • 1 := by
  calc
    (W + X) * (W + X)ᵀ =
        W * Wᵀ + X * Xᵀ + (W * Xᵀ + X * Wᵀ) := by
      simp only [Matrix.transpose_add, add_mul, mul_add]
      abel
    _ = (k + d) • 1 := by rw [hW, hX, hcross]; simp [add_smul]

/-- Disjoint sign supports give actual sign entries after filling. -/
theorem disjoint_fill_sign {ι : Type*} (W X : Matrix ι ι ℝ)
    (h : ∀ i j, (W i j = 0 ∧ IsSign (X i j)) ∨
      (X i j = 0 ∧ IsSign (W i j))) : IsSignMatrix (W + X) := by
  intro i j
  rcases h i j with ⟨hw, hx⟩ | ⟨hx, hw⟩
  · simpa [hw] using hx
  · simpa [hx] using hw

/-- A complete, sign-valued orthogonal-design filling theorem. -/
theorem orthogonal_design_hadamard {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W X : Matrix ι ι ℝ) (k d : ℝ)
    (hW : W * Wᵀ = k • 1) (hX : X * Xᵀ = d • 1)
    (hcross : W * Xᵀ + X * Wᵀ = 0)
    (hweight : k + d = Fintype.card ι)
    (hsupport : ∀ i j, (W i j = 0 ∧ IsSign (X i j)) ∨
      (X i j = 0 ∧ IsSign (W i j))) : IsHadamard (W + X) := by
  refine ⟨disjoint_fill_sign W X hsupport, ?_⟩
  rw [orthogonal_design_gram W X k d hW hX hcross, hweight]

/-- The sign/row-Gram predicate gives mathlib's full two-sided Hadamard predicate. -/
theorem isHadamard_mathlib {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {A : Matrix ι ι ℝ} (hA : IsHadamard A) : Matrix.IsHadamard A := by
  apply Matrix.IsHadamard.of_mul_conjTranspose
  · intro i j
    exact Unitary.mem_iff_eq_one_or_eq_neg_one.mpr (hA.1 i j)
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.2
  · apply isRegular_iff_ne_zero.mpr
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)

/-- Orthogonal-design filling with the exact standard mathlib conclusion. -/
theorem orthogonal_design_mathlib_hadamard {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (W X : Matrix ι ι ℝ) (k d : ℝ)
    (hW : W * Wᵀ = k • 1) (hX : X * Xᵀ = d • 1)
    (hcross : W * Xᵀ + X * Wᵀ = 0)
    (hweight : k + d = Fintype.card ι)
    (hsupport : ∀ i j, (W i j = 0 ∧ IsSign (X i j)) ∨
      (X i j = 0 ∧ IsSign (W i j))) : Matrix.IsHadamard (W + X) := by
  exact isHadamard_mathlib
    (orthogonal_design_hadamard W X k d hW hX hcross hweight hsupport)

/-- The normalized four-row Walsh matrix used in the support-moving switch. -/
noncomputable def walshFour : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(1/2:ℝ), 1/2, 1/2, 1/2;
      1/2, -1/2, 1/2, -1/2;
      1/2, 1/2, -1/2, -1/2;
      1/2, -1/2, -1/2, 1/2]

theorem walshFour_orthogonal : walshFour * walshFourᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [walshFour, Matrix.mul_apply, Fin.sum_univ_succ]

/-- A fully occupied column stays sign-valued exactly in the negative parity class. -/
theorem walshFour_sign_iff (v : Fin 4 → ℝ) (hv : ∀ i, IsSign (v i)) :
    (∀ i, IsSign ((walshFour.mulVec v) i)) ↔ (∏ i, v i) = -1 := by
  rcases hv 0 with h0 | h0 <;> rcases hv 1 with h1 | h1 <;>
    rcases hv 2 with h2 | h2 <;> rcases hv 3 with h3 | h3 <;>
    norm_num [Fin.forall_fin_succ, walshFour, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Fin.prod_univ_succ, IsSign, h0, h1, h2, h3]

/-- A column with zeros in the first row pair remains in the weighing alphabet. -/
theorem walshFour_first_pair_zero (v : Fin 4 → ℝ)
    (h0 : v 0 = 0) (h1 : v 1 = 0) (h2 : IsSign (v 2)) (h3 : IsSign (v 3)) :
    ∀ i, (walshFour.mulVec v) i = 0 ∨ IsSign ((walshFour.mulVec v) i) := by
  rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    norm_num [Fin.forall_fin_succ, walshFour, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, IsSign, h0, h1, h2, h3]

/-- The analogous exact alphabet result for zeros in the second row pair. -/
theorem walshFour_second_pair_zero (v : Fin 4 → ℝ)
    (h0 : IsSign (v 0)) (h1 : IsSign (v 1)) (h2 : v 2 = 0) (h3 : v 3 = 0) :
    ∀ i, (walshFour.mulVec v) i = 0 ∨ IsSign ((walshFour.mulVec v) i) := by
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    norm_num [Fin.forall_fin_succ, walshFour, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, IsSign, h0, h1, h2, h3]

/-- Exactly the three column cases needed by the four-row support-moving switch. -/
def WalshAdmissible (v : Fin 4 → ℝ) : Prop :=
  (v 0 = 0 ∧ v 1 = 0 ∧ IsSign (v 2) ∧ IsSign (v 3)) ∨
  (IsSign (v 0) ∧ IsSign (v 1) ∧ v 2 = 0 ∧ v 3 = 0) ∨
  ((∀ i, IsSign (v i)) ∧ (∏ i, v i) = -1)

theorem walshFour_admissible_alphabet (v : Fin 4 → ℝ) (hv : WalshAdmissible v) :
    ∀ i, (walshFour.mulVec v) i = 0 ∨ IsSign ((walshFour.mulVec v) i) := by
  rcases hv with ⟨h0,h1,h2,h3⟩ | ⟨h0,h1,h2,h3⟩ | ⟨h,hprod⟩
  · exact walshFour_first_pair_zero v h0 h1 h2 h3
  · exact walshFour_second_pair_zero v h0 h1 h2 h3
  · intro i
    exact Or.inr (((walshFour_sign_iff v h).mpr hprod) i)

/-- The four-row Walsh operation extended by the identity on all remaining rows. -/
noncomputable def walshLift (ν : Type*) [DecidableEq ν] :
    Matrix (Fin 4 ⊕ ν) (Fin 4 ⊕ ν) ℝ :=
  Matrix.fromBlocks walshFour 0 0 1

theorem walshLift_orthogonal (ν : Type*) [Fintype ν] [DecidableEq ν] :
    walshLift ν * (walshLift ν)ᵀ = 1 := by
  simp [walshLift, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    walshFour_orthogonal, Matrix.fromBlocks_one]

theorem walshLift_mul_top {ν : Type*} [Fintype ν] [DecidableEq ν]
    (W : Matrix (Fin 4 ⊕ ν) (Fin 4 ⊕ ν) ℝ) (i : Fin 4) (j : Fin 4 ⊕ ν) :
    (walshLift ν * W) (Sum.inl i) j =
      (walshFour.mulVec (fun k => W (Sum.inl k) j)) i := by
  simp [walshLift, Matrix.mul_apply, Matrix.fromBlocks, Fintype.sum_sum_type,
    Matrix.mulVec, dotProduct]

theorem walshLift_mul_bottom {ν : Type*} [Fintype ν] [DecidableEq ν]
    (W : Matrix (Fin 4 ⊕ ν) (Fin 4 ⊕ ν) ℝ) (i : ν) (j : Fin 4 ⊕ ν) :
    (walshLift ν * W) (Sum.inr i) j = W (Sum.inr i) j := by
  simp [walshLift, Matrix.mul_apply, Matrix.fromBlocks, Fintype.sum_sum_type,
    Matrix.one_apply]

/-- A complete four-row weighing switch, retaining every unselected row. -/
theorem walshLift_weighing {ν : Type*} [Fintype ν] [DecidableEq ν]
    (W : Matrix (Fin 4 ⊕ ν) (Fin 4 ⊕ ν) ℝ) (weight : ℝ)
    (hW : IsWeighing W weight)
    (hcols : ∀ j, WalshAdmissible (fun i => W (Sum.inl i) j)) :
    IsWeighing (walshLift ν * W) weight := by
  refine ⟨?_, orthogonal_row_transform (walshLift ν) W weight
    (walshLift_orthogonal ν) hW.2⟩
  intro i j
  cases i with
  | inl i =>
    rw [walshLift_mul_top]
    exact walshFour_admissible_alphabet _ (hcols j) i
  | inr i =>
    rw [walshLift_mul_bottom]
    exact hW.1 (Sum.inr i) j


/-- Exact alphabet criterion on a fully occupied column. -/
theorem walshFour_alphabet_iff (v : Fin 4 → ℝ) (hv : ∀ i, IsSign (v i)) :
    (∀ i, (walshFour.mulVec v) i = 0 ∨ IsSign ((walshFour.mulVec v) i)) ↔
      (∏ i, v i) = -1 := by
  rcases hv 0 with h0 | h0 <;> rcases hv 1 with h1 | h1 <;>
    rcases hv 2 with h2 | h2 <;> rcases hv 3 with h3 | h3 <;>
    norm_num [Fin.forall_fin_succ, walshFour, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Fin.prod_univ_succ, IsSign, h0, h1, h2, h3]

/-- The complete switch criterion for two selected zero-row pairs. -/
theorem walshLift_switch_iff {ν : Type*} [Fintype ν] [DecidableEq ν]
    (W : Matrix (Fin 4 ⊕ ν) (Fin 4 ⊕ ν) ℝ) (weight : ℝ)
    (Z : (Fin 4 ⊕ ν) → Prop) (hW : IsWeighing W weight)
    (hzero : ∀ j, Z j →
      (W (Sum.inl 0) j = 0 ∧ W (Sum.inl 1) j = 0 ∧
        IsSign (W (Sum.inl 2) j) ∧ IsSign (W (Sum.inl 3) j)) ∨
      (IsSign (W (Sum.inl 0) j) ∧ IsSign (W (Sum.inl 1) j) ∧
        W (Sum.inl 2) j = 0 ∧ W (Sum.inl 3) j = 0))
    (hfull : ∀ j, ¬ Z j → ∀ i : Fin 4, IsSign (W (Sum.inl i) j)) :
    IsWeighing (walshLift ν * W) weight ↔
      ∀ j, ¬ Z j → (∏ i : Fin 4, W (Sum.inl i) j) = -1 := by
  constructor
  · intro h j hj
    apply (walshFour_alphabet_iff _ (hfull j hj)).mp
    intro i
    simpa only [walshLift_mul_top] using h.1 (Sum.inl i) j
  · intro h
    apply walshLift_weighing W weight hW
    intro j
    by_cases hj : Z j
    · rcases hzero j hj with hp | hp
      · exact Or.inl hp
      · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr ⟨hfull j hj, h j hj⟩)

/-- Successful switching does not create or remove zeros outside selected pairs. -/
theorem walshLift_support_motion {ν : Type*} [Fintype ν] [DecidableEq ν]
    (W : Matrix (Fin 4 ⊕ ν) (Fin 4 ⊕ ν) ℝ)
    (Z : (Fin 4 ⊕ ν) → Prop)
    (hfull : ∀ j, ¬ Z j → ∀ i : Fin 4, IsSign (W (Sum.inl i) j))
    (hprod : ∀ j, ¬ Z j → (∏ i : Fin 4, W (Sum.inl i) j) = -1) :
    ∀ i j, ¬ (∃ k : Fin 4, i = Sum.inl k ∧ Z j) →
      ((walshLift ν * W) i j = 0 ↔ W i j = 0) := by
  intro i j hout
  cases i with
  | inr i => simp only [walshLift_mul_bottom]
  | inl i =>
    have hj : ¬ Z j := fun hz => hout ⟨i, rfl, hz⟩
    have hold := hfull j hj i
    have hnew := ((walshFour_sign_iff _ (hfull j hj)).mpr (hprod j hj)) i
    rw [walshLift_mul_top]
    rcases hold with hold | hold <;> rcases hnew with hnew | hnew <;>
      simp [hold, hnew]

end CompletionTheory

