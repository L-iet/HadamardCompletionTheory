/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24AllPairs
public import CompletionTheory.SignCorrelationRigidity
public import CompletionTheory.SylvesterExistence
@[expose] public section
namespace CompletionTheory

theorem base24_ordered_pair_patterns (i j : Fin 16) (hij : i < j) :
    ∃ σ : ℝ, IsSign σ ∧ ∀ x, OriginalCandidate base24Frame {i,j} x →
      HalfCorrelationPattern 24 σ (∑ k, base24Frame i k * x k) (∑ k, base24Frame j k * x k) := by
  fin_cases i
  · fin_cases j
    · norm_num at hij
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_00_01_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_00_02_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_00_03_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_00_04_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_00_05_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_00_06_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_00_07_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_00_08_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_00_09_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_00_10_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_00_11_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_00_12_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_00_13_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_00_14_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_00_15_correlations⟩
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_01_02_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_01_03_correlations⟩
    · exact ⟨rationalRealCast (-1), by norm_num [IsSign, rationalRealCast], pair24_01_04_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_01_05_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_01_06_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_01_07_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_01_08_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_01_09_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_01_10_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_01_11_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_01_12_correlations⟩
    · exact ⟨rationalRealCast (-1), by norm_num [IsSign, rationalRealCast], pair24_01_13_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_01_14_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_01_15_correlations⟩
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_02_03_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_02_04_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_02_05_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_02_06_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_02_07_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_02_08_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_02_09_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_02_10_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_02_11_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_02_12_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_02_13_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_02_14_correlations⟩
    · exact ⟨rationalRealCast (-1), by norm_num [IsSign, rationalRealCast], pair24_02_15_correlations⟩
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_03_04_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_03_05_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_03_06_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_03_07_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_03_08_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_03_09_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_03_10_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_03_11_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_03_12_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_03_13_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_03_14_correlations⟩
    · exact ⟨rationalRealCast (-1), by norm_num [IsSign, rationalRealCast], pair24_03_15_correlations⟩
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · exact ⟨rationalRealCast (-1), by norm_num [IsSign, rationalRealCast], pair24_04_05_correlations⟩
    · exact ⟨rationalRealCast (-1), by norm_num [IsSign, rationalRealCast], pair24_04_06_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_04_07_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_04_08_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_04_09_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_04_10_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_04_11_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_04_12_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_04_13_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_04_14_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_04_15_correlations⟩
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_05_06_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_05_07_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_05_08_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_05_09_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_05_10_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_05_11_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_05_12_correlations⟩
    · exact ⟨rationalRealCast (-1), by norm_num [IsSign, rationalRealCast], pair24_05_13_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_05_14_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_05_15_correlations⟩
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_06_07_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_06_08_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_06_09_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_06_10_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_06_11_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_06_12_correlations⟩
    · exact ⟨rationalRealCast (-1), by norm_num [IsSign, rationalRealCast], pair24_06_13_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_06_14_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_06_15_correlations⟩
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_07_08_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_07_09_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_07_10_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_07_11_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_07_12_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_07_13_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_07_14_correlations⟩
    · exact ⟨rationalRealCast (-1), by norm_num [IsSign, rationalRealCast], pair24_07_15_correlations⟩
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_08_09_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_08_10_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_08_11_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_08_12_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_08_13_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_08_14_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_08_15_correlations⟩
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_09_10_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_09_11_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_09_12_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_09_13_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_09_14_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_09_15_correlations⟩
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_10_11_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_10_12_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_10_13_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_10_14_correlations⟩
    · exact ⟨rationalRealCast (-1), by norm_num [IsSign, rationalRealCast], pair24_10_15_correlations⟩
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_11_12_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_11_13_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_11_14_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_11_15_correlations⟩
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_12_13_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_12_14_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_12_15_correlations⟩
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_13_14_correlations⟩
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_13_15_correlations⟩
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · exact ⟨rationalRealCast (1), by norm_num [IsSign, rationalRealCast], pair24_14_15_correlations⟩
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij

theorem base24_pair_patterns (i j : Fin 16) (hij : i ≠ j) :
    ∃ σ : ℝ, IsSign σ ∧ ∀ x, OriginalCandidate base24Frame {i,j} x →
      HalfCorrelationPattern 24 σ (∑ k, base24Frame i k * x k) (∑ k, base24Frame j k * x k) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact base24_ordered_pair_patterns i j h
  · obtain ⟨σ, hσ, hp⟩ := base24_ordered_pair_patterns j i h
    refine ⟨σ, hσ, ?_⟩
    intro x hx
    apply halfCorrelationPattern_symm _ _ _ _ hσ
    exact hp x (by simpa only [Finset.pair_comm] using hx)

theorem base24_singleton_candidates (i : Fin 16) (x : Fin 24 → ℝ)
    (hx : OriginalCandidate base24Frame {i} x) : SameSignLine x (base24Frame i) :=
  singleton_line_of_pair_patterns base24Frame base24Frame_partialHadamard
    (by simpa using base24_pair_patterns) i x hx

theorem base24_half_overlap_conditions : HalfOverlapCorrelationConditions base24Frame := by
  refine ⟨base24Frame_noSignExtension, ?_, ?_⟩
  · intro i x hx
    have hrow : base24Frame i ∈ LinearMap.range base24Frame.transpose.mulVecLin := by
      rw [Matrix.range_mulVecLin]
      change base24Frame i ∈ Submodule.span ℝ (Set.range base24Frame)
      exact Submodule.subset_span ⟨i, rfl⟩
    rcases base24_singleton_candidates i x hx with rfl | rfl
    · exact hrow
    · exact Submodule.neg_mem _ hrow
  · simpa using base24_pair_patterns

theorem base24_no_exchange_le_two (k : ℕ) (hk : k ≤ 2) :
    ¬ HasAugmentingExchange base24Frame k :=
  correlation_conditions_exclude_base_exchange base24Frame base24Frame_partialHadamard
    base24_half_overlap_conditions k hk

theorem base24_exchangeCost_eq_three : exchangeCost base24Frame = 3 :=
  correlation_conditions_base_cost_three base24Frame base24Frame_partialHadamard
    base24_half_overlap_conditions base24_exchangeCost_le_three

theorem base24_tensor_exchangeCost_eq_three {τ : Type*}
    [Fintype τ] [DecidableEq τ] [Nonempty τ] (H : Matrix τ τ ℝ) (hH : IsHadamard H) :
    exchangeCost (tensorFrame base24Frame H) = 3 :=
  correlation_conditions_tensor_cost_three base24Frame base24Frame_partialHadamard H hH
    base24_half_overlap_conditions base24_exchangeCost_le_three

theorem base24_sylvester_family (a : ℕ) :
    ∃ H : Matrix (Fin (2 ^ a)) (Fin (2 ^ a)) ℝ, IsHadamard H ∧
      IsPartialHadamard (tensorFrame base24Frame H) ∧
      NoSignExtension (tensorFrame base24Frame H) ∧
      exchangeCost (tensorFrame base24Frame H) = 3 := by
  obtain ⟨H, hH⟩ := exists_hadamard_power_two a
  exact ⟨H, hH, base24_tensor_partialHadamard H hH,
    base24_tensor_noSignExtension H hH, base24_tensor_exchangeCost_eq_three H hH⟩

end CompletionTheory
