/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.Tactic.Ring
@[expose] public section
namespace CompletionTheory.ThreeSquares
open Module

 theorem integral_basis_transition_det_square {M ι : Type*} [AddCommGroup M]
    [Fintype ι] [DecidableEq ι] (b c : Basis ι ℤ M) :
    (b.toMatrix c).det^2=1 := by
  have he := congrArg Matrix.det (b.toMatrix_mul_toMatrix_flip c)
  rw [Matrix.det_mul,Matrix.det_one] at he
  have hu : IsUnit (b.toMatrix c).det := IsUnit.of_mul_eq_one (c.toMatrix b).det he
  rcases Int.isUnit_iff.mp hu with hp | hp <;> rw [hp] <;> ring

 theorem integral_gram_determinant_basis_invariant {M ι : Type*} [AddCommGroup M]
    [Fintype ι] [DecidableEq ι] (b c : Basis ι ℤ M) (B : LinearMap.BilinForm ℤ M) :
    (LinearMap.BilinForm.toMatrix b B).det=(LinearMap.BilinForm.toMatrix c B).det := by
  have he := congrArg Matrix.det (B.toMatrix_mul_basis_toMatrix b c)
  simp only [Matrix.det_mul,Matrix.det_transpose] at he
  have hp := integral_basis_transition_det_square b c
  calc
    _=(b.toMatrix c).det^2*(LinearMap.BilinForm.toMatrix b B).det := by rw [hp,one_mul]
    _=(LinearMap.BilinForm.toMatrix c B).det := by nlinarith only [he]

end CompletionTheory.ThreeSquares
