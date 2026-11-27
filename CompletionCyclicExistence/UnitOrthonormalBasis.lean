/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCyclicExistence.UnitAdaptedBasis
public import CompletionCyclicExistence.OrthogonalUnitSplitting
@[expose] public section
namespace CompletionTheory.ThreeSquares
open Module

 theorem unit_adapted_basis_orthonormal {M ι : Type*} [AddCommGroup M] [DecidableEq ι]
    (B : LinearMap.BilinForm ℤ M) (v : M) (hv : B v v=1)
    (hs : ∀ x y,B x y=B y x) (k : Basis ι ℤ (LinearMap.ker (B v)))
    (hk : ∀ i j,B (k i:M) (k j:M)=if i=j then 1 else 0) :
    ∀ i j,B (unitAdaptedBasis (B v) v hv k i) (unitAdaptedBasis (B v) v hv k j)=
      if i=j then 1 else 0 := by
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · cases i
    cases j
    simpa only [unit_adapted_basis_first,if_true] using hv
  · rw [show i=() from Subsingleton.elim _ _,unit_adapted_basis_first,
      unit_adapted_basis_kernel]
    simpa using (k j).property
  · rw [show j=() from Subsingleton.elim _ _,unit_adapted_basis_first,
      unit_adapted_basis_kernel,hs]
    simpa using (k i).property
  · rw [unit_adapted_basis_kernel,unit_adapted_basis_kernel]
    simpa only [Sum.inr.injEq] using hk i j

 theorem integral_orthonormal_basis_reindex {M ι κ : Type*} [AddCommGroup M]
    [DecidableEq ι] [DecidableEq κ] (B : LinearMap.BilinForm ℤ M)
    (b : Basis ι ℤ M) (e : ι ≃ κ)
    (hb : ∀ i j,B (b i) (b j)=if i=j then 1 else 0) :
    ∀ i j,B (b.reindex e i) (b.reindex e j)=if i=j then 1 else 0 := by
  intro i j
  simpa using hb (e.symm i) (e.symm j)

end CompletionTheory.ThreeSquares
