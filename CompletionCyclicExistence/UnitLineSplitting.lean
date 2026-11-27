/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Tactic.Abel
@[expose] public section
namespace CompletionTheory.ThreeSquares

/-- An integer-valued functional taking value one splits the integer module
as its unit line and its kernel. No rational change of lattice is used. -/
def unitLineEquiv {M : Type*} [AddCommGroup M]
    (f : M →ₗ[ℤ] ℤ) (v : M) (hv : f v=1) : M ≃ₗ[ℤ] ℤ × LinearMap.ker f where
  toFun x := (f x, ⟨x-f x • v, by simp [hv]⟩)
  invFun x := x.1 • v + x.2.val
  left_inv x := by simp
  right_inv x := by
    apply Prod.ext
    · simp [hv, LinearMap.mem_ker.mp x.2.property]
    · apply Subtype.ext
      simp [hv, LinearMap.mem_ker.mp x.2.property]
  map_add' x y := by
    apply Prod.ext
    · exact f.map_add x y
    · apply Subtype.ext
      change x+y-f (x+y) • v=(x-f x • v)+(y-f y • v)
      rw [map_add, add_smul]
      abel
  map_smul' a x := by
    apply Prod.ext
    · exact f.map_smul a x
    · apply Subtype.ext
      change a • x-f (a • x) • v=a • (x-f x • v)
      simp only [map_smul, smul_sub, smul_smul, smul_eq_mul]

 theorem unit_line_coordinate {M : Type*} [AddCommGroup M]
    (f : M →ₗ[ℤ] ℤ) (v : M) (hv : f v=1) (x : M) :
    (unitLineEquiv f v hv x).1=f x := rfl

 theorem unit_line_reconstruction {M : Type*} [AddCommGroup M]
    (f : M →ₗ[ℤ] ℤ) (v : M) (hv : f v=1) (x : M) :
    f x • v + ((unitLineEquiv f v hv x).2 : M)=x := by simp [unitLineEquiv]

end CompletionTheory.ThreeSquares
