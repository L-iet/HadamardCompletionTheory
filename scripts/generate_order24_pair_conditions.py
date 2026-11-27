# SPDX-License-Identifier: Apache-2.0
"""Assemble finite pair cases; each case uses a Lean-checked certificate."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
source = '''/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
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
'''
for i in range(16):
    source += "  · fin_cases j\n"
    for j in range(16):
        if j <= i:
            source += "    · norm_num at hij\n"
        else:
            text = (ROOT / f"CompletionTheory/Order24Pairs/P{i:02}_{j:02}.lean").read_text(encoding="utf-8")
            sigma = re.search(r"RationalHalfCorrelationPattern 24 \((-?1)\)", text).group(1)
            source += (f"    · exact ⟨rationalRealCast ({sigma}), by norm_num [IsSign, rationalRealCast], "
                       f"pair24_{i:02}_{j:02}_correlations⟩\n")
source += '''
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
'''
(ROOT / "CompletionTheory/Order24PairConditions.lean").write_text(source, encoding="utf-8")
