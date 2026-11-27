/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Module.Torsion.Free
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory
noncomputable section
open scoped BigOperators

theorem integer_kernel_retraction {N : ℕ} {T : Type*}
    [AddCommGroup T] [Module ℤ T] [Module.IsTorsionFree ℤ T]
    (f : (Fin N → ℤ) →ₗ[ℤ] T) :
    ∃ ρ : (Fin N → ℤ) →ₗ[ℤ] LinearMap.ker f,
      ∀ x : LinearMap.ker f,ρ x.val=x := by
  letI : Module ℤ (LinearMap.range f) := (LinearMap.range f).module
  letI : Module.IsTorsionFree ℤ (LinearMap.range f) :=
    Function.Injective.moduleIsTorsionFree (fun x : LinearMap.range f => x.val)
      Subtype.val_injective (fun _ _ => rfl)
  letI : Module.Finite ℤ (LinearMap.range f) := Module.Finite.of_surjective (R:=ℤ) (S:=ℤ) (M:=Fin N → ℤ) (P:=LinearMap.range f) (σ:=RingHom.id ℤ) f.rangeRestrict f.surjective_rangeRestrict
  letI : Module.Free ℤ (LinearMap.range f) := inferInstance
  obtain ⟨s,hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective (by simp)
  let P : (Fin N → ℤ) →ₗ[ℤ] (Fin N → ℤ) := LinearMap.id-s.comp f.rangeRestrict
  have hP : ∀ x,P x∈LinearMap.ker f := by
    intro x
    have hh := congrArg (fun L : LinearMap.range f →ₗ[ℤ] LinearMap.range f => L (f.rangeRestrict x)) hs
    have hf := congrArg Subtype.val hh
    change f (x-s (f.rangeRestrict x))=0
    change f (s (f.rangeRestrict x))=f x at hf
    rw [map_sub,hf,sub_self]
  refine ⟨P.codRestrict (LinearMap.ker f) hP,?_⟩
  intro x
  apply Subtype.ext
  change x.val-s (f.rangeRestrict x.val)=x.val
  have hx : f.rangeRestrict x.val=0 := Subtype.ext x.property
  rw [hx,map_zero,sub_zero]

end
end CompletionTheory
