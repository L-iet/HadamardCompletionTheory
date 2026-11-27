/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0.
The residue-matrix construction imported below retains its AFP BSD-3-Clause
license and credits to Anna Danilkin and Loic Chevalier. -/
module
public import CompletionCyclicExistence.ResidueRealMatrix
public import CompletionCyclicExistence.PositiveMatrixUnit
@[expose] public section
namespace CompletionTheory.ThreeSquares

 theorem residue_matrix_represents_one (n d x y : ℤ) (hn : 2≤n) (hd : 0<d)
    (h : x^2+d=y*(d*n-1)) :
    ∃ z : Fin 3 → ℤ,integralQuadratic (residueMatrix n d x y) z=1 := by
  have hpos : ((residueMatrix n d x y).map (fun a : ℤ => (a:ℝ))).PosDef :=
    residue_real_positive_definite n d x y hn hd h
  obtain ⟨z,hz⟩ := integral_positive_unimodular_represents_one 3 (Or.inr rfl)
    (residueMatrix n d x y) hpos (residueMatrix_determinant n d x y h)
  exact ⟨z,hz⟩

end CompletionTheory.ThreeSquares
