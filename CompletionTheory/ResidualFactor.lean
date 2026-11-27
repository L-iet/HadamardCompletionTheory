module

public import CompletionTheory.RealExtension
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Exact residual Gram factorization and retained-row completion -/

@[expose] public section
namespace CompletionTheory
open scoped ComplexOrder

def residualGram {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (P : Matrix ι κ ℝ) : Matrix κ κ ℝ :=
  (Fintype.card κ : ℝ) • 1 - P.transpose * P

theorem sign_factor_gives_completion {δ ι : Type*}
    [Fintype δ] [Fintype ι] [DecidableEq δ] [DecidableEq ι] [Nonempty δ]
    (P : Matrix ι (δ ⊕ ι) ℝ) (B : Matrix δ (δ ⊕ ι) ℝ)
    (hP : IsSignMatrix P) (hB : IsSignMatrix B)
    (hfactor : B.transpose * B = residualGram P) :
    Matrix.IsHadamard (Matrix.fromRows B P) := by
  have hsign : IsSignMatrix (Matrix.fromRows B P).transpose := by
    intro i j
    cases j with
    | inl j => exact hB j i
    | inr j => exact hP j i
  have hgram : (Matrix.fromRows B P).transpose * Matrix.fromRows B P =
      (Fintype.card (δ ⊕ ι) : ℝ) • 1 := by
    rw [Matrix.transpose_fromRows, Matrix.fromCols_mul_fromRows, hfactor]
    unfold residualGram
    abel
  have h := isHadamard_mathlib (A := (Matrix.fromRows B P).transpose)
    ⟨hsign, by simpa only [Matrix.transpose_transpose] using hgram⟩
  exact Matrix.isHadamard_transpose_iff.mp h

theorem completion_gives_sign_factor {δ ι : Type*}
    [Fintype δ] [Fintype ι] [DecidableEq δ] [DecidableEq ι]
    (P : Matrix ι (δ ⊕ ι) ℝ) (H : Matrix (δ ⊕ ι) (δ ⊕ ι) ℝ)
    (hH : Matrix.IsHadamard H) (hret : ∀ i j, H (Sum.inr i) j = P i j) :
    ∃ B : Matrix δ (δ ⊕ ι) ℝ, IsSignMatrix B ∧ B.transpose * B = residualGram P := by
  let B := H.submatrix Sum.inl id
  have hsplit : H = Matrix.fromRows B P := by
    ext i j
    cases i with
    | inl i => rfl
    | inr i => exact hret i j
  refine ⟨B, ?_, ?_⟩
  · intro i j
    exact Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hH.apply_mem (Sum.inl i) j)
  · have h := hH.conjTranspose_mul
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hsplit,
      Matrix.transpose_fromRows, Matrix.fromCols_mul_fromRows] at h
    unfold residualGram
    rw [← h]
    abel

theorem residual_factor_completion_iff {δ ι : Type*}
    [Fintype δ] [Fintype ι] [DecidableEq δ] [DecidableEq ι] [Nonempty δ]
    (P : Matrix ι (δ ⊕ ι) ℝ) (hP : IsSignMatrix P) :
    (∃ B : Matrix δ (δ ⊕ ι) ℝ, IsSignMatrix B ∧ B.transpose * B = residualGram P) ↔
    ∃ H : Matrix (δ ⊕ ι) (δ ⊕ ι) ℝ, Matrix.IsHadamard H ∧
      ∀ i j, H (Sum.inr i) j = P i j := by
  constructor
  · rintro ⟨B, hB, hfactor⟩
    exact ⟨Matrix.fromRows B P, sign_factor_gives_completion P B hP hB hfactor,
      fun _ _ => rfl⟩
  · rintro ⟨H, hH, hret⟩
    exact completion_gives_sign_factor P H hH hret

theorem real_residual_factor {δ ι : Type*}
    [Fintype δ] [Fintype ι] [DecidableEq δ] [DecidableEq ι] [Nonempty δ]
    (P : Matrix ι (δ ⊕ ι) ℝ) (hP : IsPartialHadamard P) :
    ∃ B : Matrix δ (δ ⊕ ι) ℝ, B.transpose * B = residualGram P ∧
      B * B.transpose = (Fintype.card (δ ⊕ ι) : ℝ) • 1 := by
  obtain ⟨H, hrow, hcol, hret⟩ := real_frame_extension P hP.2
  let B := H.submatrix Sum.inl id
  have hsplit : H = Matrix.fromRows B P := by
    ext i j
    cases i with
    | inl i => rfl
    | inr i => exact hret i j
  refine ⟨B, ?_, ?_⟩
  · rw [hsplit, Matrix.transpose_fromRows, Matrix.fromCols_mul_fromRows] at hcol
    unfold residualGram
    rw [← hcol]
    abel
  · ext i j
    have h := congrArg (fun M => M (Sum.inl i) (Sum.inl j)) hrow
    simpa [Matrix.mul_apply, Matrix.transpose_apply, B, Matrix.smul_apply,
      Matrix.one_apply] using h

theorem residualGram_structure {δ ι : Type*}
    [Fintype δ] [Fintype ι] [DecidableEq δ] [DecidableEq ι] [Nonempty δ]
    (P : Matrix ι (δ ⊕ ι) ℝ) (hP : IsPartialHadamard P) :
    (residualGram P).PosSemidef ∧ (residualGram P).rank = Fintype.card δ ∧
      residualGram P * residualGram P =
        (Fintype.card (δ ⊕ ι) : ℝ) • residualGram P := by
  obtain ⟨B, hfactor, hrow⟩ := real_residual_factor P hP
  have hN : (Fintype.card (δ ⊕ ι) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (δ ⊕ ι) ≠ 0)
  refine ⟨?_, ?_, ?_⟩
  · rw [← hfactor]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self B
  · rw [← hfactor, Matrix.rank_transpose_mul_self, ← Matrix.rank_self_mul_transpose B, hrow]
    apply Matrix.rank_of_det_ne_zero
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ hN
  · rw [← hfactor]
    calc
      (B.transpose * B) * (B.transpose * B) = B.transpose * (B * B.transpose) * B := by
        simp only [Matrix.mul_assoc]
      _ = (Fintype.card (δ ⊕ ι) : ℝ) • (B.transpose * B) := by
        rw [hrow]
        simp

theorem residualGram_diagonal {δ ι : Type*}
    [Fintype δ] [Fintype ι] [DecidableEq δ] [DecidableEq ι]
    (P : Matrix ι (δ ⊕ ι) ℝ) (hP : IsSignMatrix P) (j : δ ⊕ ι) :
    residualGram P j j = Fintype.card δ := by
  have hsum : (∑ i, P i j * P i j) = (Fintype.card ι : ℝ) := by
    calc
      (∑ i, P i j * P i j) = ∑ _i : ι, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        nlinarith [isSign_sq (hP i j)]
      _ = _ := by simp
  simp [residualGram, Matrix.mul_apply, Matrix.transpose_apply, hsum,
    Fintype.card_sum, Nat.cast_add]

theorem residualGram_offDiagonal_parity {δ ι : Type*}
    [Fintype δ] [Fintype ι] [DecidableEq δ] [DecidableEq ι]
    (P : Matrix ι (δ ⊕ ι) ℝ) (hP : IsSignMatrix P)
    (heven : Even (Fintype.card (δ ⊕ ι))) (i j : δ ⊕ ι) (hij : i ≠ j) :
    ∃ z : ℤ, residualGram P i j = (Fintype.card δ : ℝ) + 2 * z := by
  classical
  have hsign : ∀ a, ∃ z : ℤ, P a i * P a j = 1 + 2 * z := by
    intro a
    rcases hP a i with hi | hi <;> rcases hP a j with hj | hj
    · exact ⟨0, by norm_num [hi, hj]⟩
    · exact ⟨-1, by norm_num [hi, hj]⟩
    · exact ⟨-1, by norm_num [hi, hj]⟩
    · exact ⟨0, by norm_num [hi, hj]⟩
  choose f hf using hsign
  obtain ⟨k, hk⟩ := heven
  have hcard : (Fintype.card δ : ℝ) + Fintype.card ι = 2 * (k : ℝ) := by
    have hk' : Fintype.card δ + Fintype.card ι = k + k := by
      simpa only [Fintype.card_sum] using hk
    exact_mod_cast (by omega : Fintype.card δ + Fintype.card ι = 2 * k)
  have hsum : (∑ a, P a i * P a j) = (Fintype.card ι : ℝ) + 2 * (∑ a, (f a : ℝ)) := by
    simp_rw [hf]
    simp [Finset.sum_add_distrib, ← Finset.mul_sum]
  refine ⟨-(k : ℤ) - ∑ a, f a, ?_⟩
  simp only [residualGram, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    ite_eq_right hij, smul_eq_mul, mul_zero, zero_sub, Matrix.mul_apply, Matrix.transpose_apply]
  push_cast
  rw [hsum]
  linarith

end CompletionTheory
