/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCyclicExistence.IntegralFamilyGram
public import CompletionCyclicExistence.UnitAdaptedBasis
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory.ThreeSquares
open Module

 theorem kernel_gram_coordinates {M ι : Type*} [AddCommGroup M]
    [Fintype ι] [DecidableEq ι] (B : LinearMap.BilinForm ℤ M) (f : M →ₗ[ℤ] ℤ)
    (k : Basis ι ℤ (LinearMap.ker f)) (x y : ι → ℤ) :
    Matrix.toBilin' (Matrix.of (fun i j => B (k i:M) (k j:M))) x y=
      B ((k.equivFun.symm x : LinearMap.ker f):M)
        ((k.equivFun.symm y : LinearMap.ker f):M) := by
  let C := B.comp (LinearMap.ker f).subtype (LinearMap.ker f).subtype
  have hc : LinearMap.BilinForm.toMatrix k C=
      Matrix.of (fun i j => B (k i:M) (k j:M)) := by
    ext i j
    simp [C,LinearMap.BilinForm.toMatrix_apply,LinearMap.BilinForm.comp_apply,Matrix.of_apply]
  rw [Matrix.toBilin'_apply',←hc]
  simpa [C,LinearMap.BilinForm.comp_apply] using C.dotProduct_toMatrix_mulVec k x y

end CompletionTheory.ThreeSquares
