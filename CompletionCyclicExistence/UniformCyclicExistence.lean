/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCyclicExistence.UniformCyclicSharp
public import CompletionCyclicExistence.FixedSumSquareInterface
@[expose] public section
namespace CompletionTheory.ThreeSquares
open scoped BigOperators

 theorem uniform_family_iff_threshold {m : ℕ} [NeZero m] (hm : Odd m) (t : ℤ) (ht : Odd t) :
    UniformFamilySolution m t ↔ (m:ℤ)^2+3≤4*t := by
  constructor
  · exact uniform_family_necessary_threshold hm t ht
  · intro hlarge
    have hmZ : Odd (m:ℤ) := by exact_mod_cast hm
    obtain ⟨x,hs,hn⟩ := four_squares_fixed_sum_api m t hmZ ht hlarge
    exact ⟨x,uniform_family_of_fixed_sum x t hs hn⟩

 theorem uniform_large_energy_existence {m : ℕ} [NeZero m] (hm : Odd m) (t : ℤ)
    (ht : Odd t) (hlarge : (m:ℤ)^2+3≤4*t) :
    UniformFamilySolution m t ∧ CyclicNormSolution m t := by
  have h := (uniform_family_iff_threshold hm t ht).mpr hlarge
  exact ⟨h,uniform_family_actual_solution h⟩

 theorem small_cyclic_orders_all_odd_energy {m : ℕ} [NeZero m]
    (hm : m=1 ∨ m=3) (t : ℤ) (ht : Odd t) (hT : (m:ℤ)≤t) :
    CyclicNormSolution m t := by
  have hmOdd : Odd m := by rcases hm with rfl | rfl <;> decide
  have hlarge : (m:ℤ)^2+3≤4*t := by
    rcases hm with rfl | rfl <;> norm_num at * <;> omega
  exact (uniform_large_energy_existence hmOdd t ht hlarge).2

end CompletionTheory.ThreeSquares
