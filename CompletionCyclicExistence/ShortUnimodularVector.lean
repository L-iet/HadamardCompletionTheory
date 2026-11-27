/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCyclicExistence.UnimodularFundamentalVolume
public import CompletionCyclicExistence.SmallBallVolumes
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
public import Mathlib.LinearAlgebra.Countable
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
@[expose] public section
namespace CompletionTheory.ThreeSquares
open Module MeasureTheory Metric
open scoped BigOperators

 theorem short_integer_combination_of_ball_volume {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b : Basis ι ℝ E)
    (hdet : (Matrix.gram ℝ b).det=1)
    (hvol : (2:ENNReal)^finrank ℝ E<volume (Metric.ball (0:E) (Real.sqrt 2))) :
    ∃ z : ι → ℤ,(∑ i,z i • b i)≠0 ∧ ‖∑ i,z i • b i‖^2<2 := by
  classical
  let L : AddSubgroup E := (Submodule.span ℤ (Set.range b)).toAddSubgroup
  letI : Countable L := inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  have hmeasure : volume (ZSpan.fundamentalDomain b)*(2:ENNReal)^finrank ℝ E<
      volume (Metric.ball (0:E) (Real.sqrt 2)) := by
    rw [unimodular_gram_fundamental_volume b hdet,one_mul]
    exact hvol
  have hsymm : ∀ x∈Metric.ball (0:E) (Real.sqrt 2),-x∈Metric.ball (0:E) (Real.sqrt 2) := by
    intro x hx
    simpa only [Metric.mem_ball,dist_zero_right,norm_neg] using hx
  obtain ⟨x,hx0,hx⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      (ZSpan.isAddFundamentalDomain' b volume) hsymm (convex_ball (0:E) (Real.sqrt 2)) hmeasure
  have hx0' : (x:E)≠0 := by
    intro he
    apply hx0
    apply Subtype.ext
    exact he
  have hxmem : (x:E)∈Submodule.span ℤ (Set.range b) := x.property
  obtain ⟨z,hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hxmem
  refine ⟨z,?_,?_⟩
  · rw [hz]
    exact hx0'
  · rw [hz]
    have hnorm : ‖(x:E)‖<Real.sqrt 2 := by simpa only [Metric.mem_ball,dist_zero_right] using hx
    nlinarith [norm_nonneg (x:E),Real.sqrt_nonneg (2:ℝ),Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]

 theorem short_integer_combination_rank_three {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b : Basis (Fin 3) ℝ E)
    (hdet : (Matrix.gram ℝ b).det=1) :
    ∃ z : Fin 3 → ℤ,(∑ i,z i • b i)≠0 ∧ ‖∑ i,z i • b i‖^2<2 := by
  have hd : finrank ℝ E=3 := by simpa using Module.finrank_eq_card_basis b
  exact short_integer_combination_of_ball_volume b hdet (ball_sqrt_two_volume_dim_three hd)

 theorem short_integer_combination_rank_two {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b : Basis (Fin 2) ℝ E)
    (hdet : (Matrix.gram ℝ b).det=1) :
    ∃ z : Fin 2 → ℤ,(∑ i,z i • b i)≠0 ∧ ‖∑ i,z i • b i‖^2<2 := by
  have hd : finrank ℝ E=2 := by simpa using Module.finrank_eq_card_basis b
  exact short_integer_combination_of_ball_volume b hdet (ball_sqrt_two_volume_dim_two hd)

end CompletionTheory.ThreeSquares
