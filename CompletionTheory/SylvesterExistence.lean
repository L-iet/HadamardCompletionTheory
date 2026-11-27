/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.EncodedFrames
public import CompletionTheory.TensorExchange
@[expose] public section
namespace CompletionTheory
open Matrix

theorem mathlib_hadamard_to_partial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : Matrix.IsHadamard H) : IsHadamard H := by
  constructor
  · intro i j
    exact Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hH.apply_mem i j)
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hH.mul_conjTranspose

theorem exists_hadamard_power_two (a : ℕ) :
    ∃ H : Matrix (Fin (2 ^ a)) (Fin (2 ^ a)) ℝ, IsHadamard H := by
  have htwo : IsHadamard (encodedRealFrame (n := 2) (![0, 2] : Fin 2 → ℕ)) := by
    apply encodedRealFrame_partialHadamard
    decide +kernel
  induction a with
  | zero =>
    refine ⟨encodedRealFrame (![0] : Fin 1 → ℕ), ?_⟩
    apply encodedRealFrame_partialHadamard
    decide +kernel
  | succ a ih =>
    obtain ⟨H, hH⟩ := ih
    let T := tensorFrame H (encodedRealFrame (n := 2) (![0, 2] : Fin 2 → ℕ))
    have hT : IsHadamard T := tensorFrame_partialHadamard _ _ hH htwo
    have hc : Fintype.card (Fin (2 ^ a) × Fin 2) = 2 ^ (a + 1) := by
      simp [pow_succ]
    let e := Fintype.equivFinOfCardEq hc
    refine ⟨Matrix.reindex e e T, ?_⟩
    apply mathlib_hadamard_to_partial
    exact (isHadamard_mathlib hT).reindex e e

end CompletionTheory
