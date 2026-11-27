/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCyclicExistence.TernaryKernelNormalization
public import CompletionCyclicExistence.PositiveMatrixUnit
@[expose] public section
namespace CompletionTheory.ThreeSquares
open Module

 theorem positive_ternary_unimodular_orthonormal_basis (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hpos : (A.map (fun a : ℤ => (a:ℝ))).PosDef) (hdet : A.det=1) :
    ∃ b : Basis (Fin 3) ℤ (Fin 3 → ℤ),∀ i j,
      Matrix.toBilin' A (b i) (b j)=if i=j then 1 else 0 := by
  obtain ⟨v,hv⟩ := integral_positive_unimodular_represents_one 3 (Or.inr rfl) A hpos hdet
  have hvB : Matrix.toBilin' A v v=1 := by
    simpa only [Matrix.toBilin'_apply,integerGramValue] using hv
  exact positive_ternary_orthonormal_basis_of_unit A hpos hdet v hvB

end CompletionTheory.ThreeSquares
