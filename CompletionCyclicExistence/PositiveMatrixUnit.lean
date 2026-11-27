/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCyclicExistence.UnitUnimodularVector
public import Mathlib.Analysis.Matrix.PosDef
@[expose] public section
namespace CompletionTheory.ThreeSquares
open Module MeasureTheory
open scoped BigOperators InnerProductSpace Matrix

 theorem integral_positive_unimodular_represents_one (n : ℕ) (hn : n=2 ∨ n=3)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (hpos : (A.map (fun a : ℤ => (a:ℝ))).PosDef) (hdet : A.det=1) :
    ∃ z : Fin n → ℤ,integerGramValue A z=1 := by
  classical
  let M := A.map (fun a : ℤ => (a:ℝ))
  letI : NormedAddCommGroup (Fin n → ℝ) := M.toNormedAddCommGroup hpos
  letI : SeminormedAddCommGroup (Fin n → ℝ) := M.toSeminormedAddCommGroup hpos.posSemidef
  letI : InnerProductSpace ℝ (Fin n → ℝ) := M.toInnerProductSpace hpos.posSemidef
  letI : Inner ℝ (Fin n → ℝ) := (M.toInnerProductSpace hpos.posSemidef).toInner
  letI : PseudoMetricSpace (Fin n → ℝ) := (M.toNormedAddCommGroup hpos).toSeminormedAddCommGroup.toPseudoMetricSpace
  letI : TopologicalSpace (Fin n → ℝ) := (M.toNormedAddCommGroup hpos).toUniformSpace.toTopologicalSpace
  letI : MeasurableSpace (Fin n → ℝ) := borel (Fin n → ℝ)
  letI : BorelSpace (Fin n → ℝ) := ⟨rfl⟩
  letI : MeasureSpace (Fin n → ℝ) := measureSpaceOfInnerProductSpace
  have hGram (i j : Fin n) :
      ⟪(Pi.basisFun ℝ (Fin n)) i,(Pi.basisFun ℝ (Fin n)) j⟫_ℝ=(A i j:ℝ) := by
    simp only [Pi.basisFun_apply]
    change (M*ᵥ(Pi.single j 1))⬝ᵥstar (Pi.single i 1)=(A i j:ℝ)
    simp [M,Matrix.mulVec_single, dotProduct_single]
  have hd : finrank ℝ (Fin n → ℝ)=n := by simp
  have hvol : (2:ENNReal)^finrank ℝ (Fin n → ℝ) <
      volume (Metric.ball (0:Fin n → ℝ) (Real.sqrt 2)) := by
    rcases hn with h | h
    · exact ball_sqrt_two_volume_dim_two (hd.trans h)
    · exact ball_sqrt_two_volume_dim_three (hd.trans h)
  obtain ⟨z,hz,hs⟩ := short_integer_combination_of_ball_volume
    (Pi.basisFun ℝ (Fin n)) (integral_gram_det_real _ A hGram hdet) hvol
  exact ⟨z,integral_unit_value_of_short_vector _ A hGram z hz hs⟩

end CompletionTheory.ThreeSquares
