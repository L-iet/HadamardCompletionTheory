/-
Reference: Three_Squares/Three_Squares.thy in the Archive of Formal Proofs.
Original authors: Anna Danilkin and Loïc Chevalier.
Lean translation and additional algebra: Copyright (c) 2026 Joshua Mark.
Released under the AFP BSD license; see AFP-LICENSE-BSD.txt in this directory.
This file proves only the explicit residue-matrix construction, not the
three-square theorem or the missing integral ternary-form classification.
-/
module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
@[expose] public section
namespace CompletionTheory.ThreeSquares
open scoped BigOperators Matrix

def residueMatrix (n d x y : ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  ![![y,x,1],![x,d*n-1,0],![1,0,n]]

def integralQuadratic (M : Matrix (Fin 3) (Fin 3) ℤ) (v : Fin 3 → ℤ) : ℤ :=
  ∑ i,∑ j,(v i*M i j*v j)

theorem residueMatrix_symmetric (n d x y : ℤ) : (residueMatrix n d x y)ᵀ=residueMatrix n d x y := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem residueMatrix_determinant (n d x y : ℤ) (h : x^2+d=y*(d*n-1)) :
    (residueMatrix n d x y).det=1 := by
  have he : y*(d*n-1)-x^2=d := by linarith
  calc
    _ = (y*(d*n-1)-x^2)*n-(d*n-1) := by
      rw [Matrix.det_fin_three]
      simp [residueMatrix]
      <;> ring
    _ = 1 := by rw [he]; ring

theorem residueMatrix_represents_n (n d x y : ℤ) :
    integralQuadratic (residueMatrix n d x y) ![0,0,1]=n := by
  simp [integralQuadratic,residueMatrix,Fin.sum_univ_three]

theorem residueMatrix_positive_identity (n d x y : ℤ) (h : x^2+d=y*(d*n-1))
    (v : Fin 3 → ℤ) :
    y*d*integralQuadratic (residueMatrix n d x y) v=
      d*(y*v 0+x*v 1+v 2)^2+(d*v 1-x*v 2)^2+y*(v 2)^2 := by
  have he :
      d*(y*v 0+x*v 1+v 2)^2+(d*v 1-x*v 2)^2+y*(v 2)^2-
        y*d*integralQuadratic (residueMatrix n d x y) v=
      (x^2+d-y*(d*n-1))*(d*(v 1)^2+(v 2)^2) := by
    simp [integralQuadratic,residueMatrix,Fin.sum_univ_three]
    <;> ring
  rw [sub_eq_zero.mpr h,zero_mul] at he
  exact (sub_eq_zero.mp he).symm

theorem residueMatrix_integrally_positive (n d x y : ℤ) (hn : 2≤n) (hd : 0< d)
    (h : x^2+d=y*(d*n-1)) (v : Fin 3 → ℤ) (hv : v≠0) :
    0< integralQuadratic (residueMatrix n d x y) v := by
  have ha : 0< d*n-1 := by nlinarith
  have hy : 0< y := by
    by_contra hy
    have hy0 : y≤0 := by omega
    have hb := mul_nonpos_of_nonpos_of_nonneg hy0 ha.le
    nlinarith [sq_nonneg x]
  have hA : 0≤d*(y*v 0+x*v 1+v 2)^2 := mul_nonneg hd.le (sq_nonneg _)
  have hB : 0≤(d*v 1-x*v 2)^2 := sq_nonneg _
  have hC : 0≤y*(v 2)^2 := mul_nonneg hy.le (sq_nonneg _)
  have hpos : 0< d*(y*v 0+x*v 1+v 2)^2+(d*v 1-x*v 2)^2+y*(v 2)^2 := by
    by_cases h2 : v 2=0
    · by_cases h1 : v 1=0
      · have h0 : v 0≠0 := by
          intro h0
          apply hv
          funext i
          fin_cases i <;> simp [h0,h1,h2]
        have hfirst : 0< d*(y*v 0+x*v 1+v 2)^2 := by
          apply mul_pos hd
          apply sq_pos_of_ne_zero
          simpa [h1,h2] using mul_ne_zero hy.ne' h0
        exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hfirst hB) hC
      · have hmid : 0<(d*v 1-x*v 2)^2 := by
          apply sq_pos_of_ne_zero
          simpa [h2] using mul_ne_zero hd.ne' h1
        exact add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos hA hmid) hC
    · exact add_pos_of_nonneg_of_pos (add_nonneg hA hB) (mul_pos hy (sq_pos_of_ne_zero h2))
  have hm : 0< y*d*integralQuadratic (residueMatrix n d x y) v := by
    rw [residueMatrix_positive_identity n d x y h v]
    exact hpos
  by_contra hq
  have hq0 : integralQuadratic (residueMatrix n d x y) v≤0 := le_of_not_gt hq
  have hm0 := mul_nonpos_of_nonneg_of_nonpos (mul_pos hy hd).le hq0
  linarith

end CompletionTheory.ThreeSquares
