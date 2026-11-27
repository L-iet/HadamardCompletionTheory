/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCyclicExistence.ShortUnimodularVector
public import Mathlib.Algebra.Module.NatInt
@[expose] public section
namespace CompletionTheory.ThreeSquares
open Module
open scoped BigOperators InnerProductSpace

 def integerGramValue {ι : Type*} [Fintype ι] (A : Matrix ι ι ℤ) (z : ι → ℤ) : ℤ :=
  ∑ i,∑ j,z i*A i j*z j

 theorem integer_combination_norm_square {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (b : ι → E) (A : Matrix ι ι ℤ)
    (hGram : ∀ i j,⟪b i,b j⟫_ℝ=(A i j:ℝ)) (z : ι → ℤ) :
    ‖∑ i,z i • b i‖^2=(integerGramValue A z:ℝ) := by
  rw [←real_inner_self_eq_norm_sq]
  simp only [←Int.cast_smul_eq_zsmul ℝ,sum_inner,inner_sum,inner_smul_left,
    inner_smul_right,star_trivial,hGram,integerGramValue,Int.cast_sum,Int.cast_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hs : (A j i : ℝ) = (A i j : ℝ) := by
    rw [←hGram, ←hGram]
    exact real_inner_comm (b i) (b j)
  simp only [starRingEnd_apply, star_trivial]
  rw [hs]
  ring

 theorem integral_gram_det_real {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (b : ι → E) (A : Matrix ι ι ℤ)
    (hGram : ∀ i j,⟪b i,b j⟫_ℝ=(A i j:ℝ)) (hdet : A.det=1) :
    (Matrix.gram ℝ b).det=1 := by
  have hm : Matrix.gram ℝ b=A.map (fun a : ℤ => (a:ℝ)) := by
    ext i j
    exact hGram i j
  rw [hm]
  calc
    _=(A.det:ℝ) := (Int.cast_det (R:=ℝ) A).symm
    _=1 := by rw [hdet,Int.cast_one]

 theorem integral_unit_value_of_short_vector {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (b : ι → E) (A : Matrix ι ι ℤ)
    (hGram : ∀ i j,⟪b i,b j⟫_ℝ=(A i j:ℝ)) (z : ι → ℤ)
    (hne : (∑ i,z i • b i)≠0) (hshort : ‖∑ i,z i • b i‖^2<2) :
    integerGramValue A z=1 := by
  have he := integer_combination_norm_square b A hGram z
  have hp : (0:ℝ)<(integerGramValue A z:ℝ) := by
    rw [←he]
    exact pow_pos (norm_pos_iff.mpr hne) _
  have hl : (integerGramValue A z:ℝ)<2 := by rw [←he];exact hshort
  have hpZ : 0 < integerGramValue A z := by exact_mod_cast hp
  have hlZ : integerGramValue A z<2 := by exact_mod_cast hl
  omega

 theorem integral_unimodular_unit_vector_three {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b : Basis (Fin 3) ℝ E) (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hGram : ∀ i j,⟪b i,b j⟫_ℝ=(A i j:ℝ)) (hdet : A.det=1) :
    ∃ z : Fin 3 → ℤ,integerGramValue A z=1 := by
  obtain ⟨z,hz,hshort⟩ := short_integer_combination_rank_three b (integral_gram_det_real b A hGram hdet)
  exact ⟨z,integral_unit_value_of_short_vector b A hGram z hz hshort⟩

 theorem integral_unimodular_unit_vector_two {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b : Basis (Fin 2) ℝ E) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hGram : ∀ i j,⟪b i,b j⟫_ℝ=(A i j:ℝ)) (hdet : A.det=1) :
    ∃ z : Fin 2 → ℤ,integerGramValue A z=1 := by
  obtain ⟨z,hz,hshort⟩ := short_integer_combination_rank_two b (integral_gram_det_real b A hGram hdet)
  exact ⟨z,integral_unit_value_of_short_vector b A hGram z hz hshort⟩

end CompletionTheory.ThreeSquares
