/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCyclicExistence.UnitLineSplitting
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.Tactic.Ring
@[expose] public section
namespace CompletionTheory.ThreeSquares
open LinearMap

 theorem unit_kernel_orthogonal {M : Type*} [AddCommGroup M]
    (B : LinearMap.BilinForm ℤ M) (v : M) (hv : B v v=1)
    (hs : ∀ x y,B x y=B y x) (x : M) :
    B v ((unitLineEquiv (B v) v hv x).2 : M)=0 ∧
    B ((unitLineEquiv (B v) v hv x).2 : M) v=0 := by
  have h := (unitLineEquiv (B v) v hv x).2.property
  have hz : B v ((unitLineEquiv (B v) v hv x).2 : M)=0 := h
  exact ⟨hz, (hs _ _).trans hz⟩

 theorem unit_orthogonal_quadratic_decomposition {M : Type*}
    [AddCommGroup M] (B : LinearMap.BilinForm ℤ M) (v : M)
    (hv : B v v=1) (hs : ∀ x y,B x y=B y x) (x : M) :
    B x x=(B v x)^2+B ((unitLineEquiv (B v) v hv x).2 : M)
      ((unitLineEquiv (B v) v hv x).2 : M) := by
  change B x x=(B v x)^2+B (x-B v x • v) (x-B v x • v)
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, hv]
  rw [hs x v]
  ring

end CompletionTheory.ThreeSquares
