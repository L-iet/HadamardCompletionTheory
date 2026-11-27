/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCyclicExistence.TernaryUnimodularNormalForm
public import Mathlib.Algebra.BigOperators.Fin
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory.ThreeSquares
open Module
open scoped BigOperators Matrix

 theorem positive_ternary_unimodular_values_are_three_squares
    (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hpos : (A.map (fun a : ℤ => (a:ℝ))).PosDef) (hdet : A.det=1)
    (x : Fin 3 → ℤ) :
    ∃ a b c : ℤ,Matrix.toBilin' A x x=a^2+b^2+c^2 := by
  classical
  obtain ⟨b,hb⟩ := positive_ternary_unimodular_orthonormal_basis A hpos hdet
  have hm : LinearMap.BilinForm.toMatrix b (Matrix.toBilin' A)=1 := by
    ext i j
    simpa only [LinearMap.BilinForm.toMatrix_apply,Matrix.one_apply] using hb i j
  have hq := (Matrix.toBilin' A).apply_eq_dotProduct_toMatrix_mulVec b x x
  rw [hm,Matrix.one_mulVec] at hq
  refine ⟨b.repr x 0,b.repr x 1,b.repr x 2,?_⟩
  simpa only [dotProduct,Fin.sum_univ_three,pow_two] using hq

end CompletionTheory.ThreeSquares
