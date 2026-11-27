/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0.
The imported AFP residue construction retains its BSD-3-Clause license,
with credits to Anna Danilkin and Loic Chevalier. -/
module
public import CompletionCyclicExistence.TernaryThreeSquareValues
public import CompletionCyclicExistence.ResidueRealMatrix
@[expose] public section
namespace CompletionTheory.ThreeSquares
open scoped Matrix

/-- Conditional on the explicit integer residue data; this does not assert
that the residue data exist for every positive integer congruent to 3 mod 8. -/
 theorem residue_data_three_square_representation (n d x y : ℤ)
    (hn : 2≤n) (hd : 0<d) (h : x^2+d=y*(d*n-1)) :
    ∃ a b c : ℤ,n=a^2+b^2+c^2 := by
  have hpos : ((residueMatrix n d x y).map (fun a : ℤ => (a:ℝ))).PosDef :=
    residue_real_positive_definite n d x y hn hd h
  have he : Matrix.toBilin' (residueMatrix n d x y) ![0,0,1] ![0,0,1]=n := by
    rw [Matrix.toBilin'_apply]
    exact residueMatrix_represents_n n d x y
  obtain ⟨a,b,c,habc⟩ := positive_ternary_unimodular_values_are_three_squares
    (residueMatrix n d x y) hpos (residueMatrix_determinant n d x y h) ![0,0,1]
  exact ⟨a,b,c,he.symm.trans habc⟩

end CompletionTheory.ThreeSquares
