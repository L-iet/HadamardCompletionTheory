/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCyclicExistence.UnitKernelRank
public import Mathlib.LinearAlgebra.Basis.Prod
@[expose] public section
namespace CompletionTheory.ThreeSquares
open Module

noncomputable def unitAdaptedBasis {M ι : Type*} [AddCommGroup M]
    (f : M →ₗ[ℤ] ℤ) (v : M) (hv : f v=1) (b : Basis ι ℤ (LinearMap.ker f)) :
    Basis (Unit ⊕ ι) ℤ M :=
  ((Basis.singleton Unit ℤ).prod b).map (unitLineEquiv f v hv).symm

 theorem unit_adapted_basis_first {M ι : Type*} [AddCommGroup M]
    (f : M →ₗ[ℤ] ℤ) (v : M) (hv : f v=1) (b : Basis ι ℤ (LinearMap.ker f)) :
    unitAdaptedBasis f v hv b (Sum.inl ())=v := by
  simp [unitAdaptedBasis, Basis.prod_apply, unitLineEquiv]

 theorem unit_adapted_basis_kernel {M ι : Type*} [AddCommGroup M]
    (f : M →ₗ[ℤ] ℤ) (v : M) (hv : f v=1) (b : Basis ι ℤ (LinearMap.ker f)) (i : ι) :
    unitAdaptedBasis f v hv b (Sum.inr i)=(b i:M) := by
  simp [unitAdaptedBasis, Basis.prod_apply, unitLineEquiv]

 theorem integral_unit_adapted_basis (n : ℕ) (f : (Fin n → ℤ) →ₗ[ℤ] ℤ)
    (v : Fin n → ℤ) (hv : f v=1) :
    ∃ b : Basis (Unit ⊕ Fin (n-1)) ℤ (Fin n → ℤ),
      b (Sum.inl ())=v ∧ ∀ i,f (b (Sum.inr i))=0 := by
  obtain ⟨k⟩ := unit_kernel_basis n f v hv
  refine ⟨unitAdaptedBasis f v hv k,unit_adapted_basis_first f v hv k,?_⟩
  intro i
  rw [unit_adapted_basis_kernel]
  exact (k i).property

end CompletionTheory.ThreeSquares
