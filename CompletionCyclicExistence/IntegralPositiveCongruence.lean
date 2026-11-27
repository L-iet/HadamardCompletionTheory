/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
@[expose] public section
namespace CompletionTheory.ThreeSquares
open scoped Matrix

 theorem integral_positive_congruence {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (A : Matrix ι ι ℤ) (T : Matrix ι κ ℤ)
    (hA : (A.map (fun a : ℤ => (a:ℝ))).PosSemidef)
    (hdet : (Tᵀ*A*T).det=1) :
    ((Tᵀ*A*T).map (fun a : ℤ => (a:ℝ))).PosDef := by
  let C := T.map (fun a : ℤ => (a:ℝ))
  have he : (Tᵀ*A*T).map (fun a : ℤ => (a:ℝ))=
      Cᴴ*(A.map (fun a : ℤ => (a:ℝ)))*C := by
    ext i j
    simp [C,Matrix.mul_apply,Matrix.conjTranspose_apply]
  have hp : ((Tᵀ*A*T).map (fun a : ℤ => (a:ℝ))).PosSemidef := by
    rw [he]
    exact hA.conjTranspose_mul_mul_same C
  apply hp.posDef_iff_det_ne_zero.mpr
  have hd : (((Tᵀ*A*T).map (fun a : ℤ => (a:ℝ))).det)=((Tᵀ*A*T).det:ℝ) :=
    (Int.cast_det (R:=ℝ) (Tᵀ*A*T)).symm
  rw [hd,hdet,Int.cast_one]
  exact one_ne_zero

end CompletionTheory.ThreeSquares
