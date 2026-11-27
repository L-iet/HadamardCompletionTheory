/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCyclicExistence.UnitLineSplitting
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Free
public import Lean.Elab.Tactic.Omega
@[expose] public section
namespace CompletionTheory.ThreeSquares
open Module

 theorem unit_kernel_rank (n : ℕ) (f : (Fin n → ℤ) →ₗ[ℤ] ℤ)
    (v : Fin n → ℤ) (hv : f v=1) :
    finrank ℤ (LinearMap.ker f)+1=n := by
  obtain ⟨k,b⟩ := Submodule.basisOfPid (Pi.basisFun ℤ (Fin n)) (LinearMap.ker f)
  letI := Module.Free.of_basis b
  letI := Module.Finite.of_basis b
  have h := (unitLineEquiv f v hv).finrank_eq
  simpa [Module.finrank_prod, add_comm] using h.symm

 theorem unit_kernel_basis (n : ℕ) (f : (Fin n → ℤ) →ₗ[ℤ] ℤ)
    (v : Fin n → ℤ) (hv : f v=1) :
    Nonempty (Basis (Fin (n-1)) ℤ (LinearMap.ker f)) := by
  have h := unit_kernel_rank n f v hv
  obtain ⟨k,b⟩ := Submodule.basisOfPid (Pi.basisFun ℤ (Fin n)) (LinearMap.ker f)
  have hk : finrank ℤ (LinearMap.ker f)=k := by simpa using Module.finrank_eq_card_basis b
  exact ⟨b.reindex (finCongr (by omega : k=n-1))⟩

end CompletionTheory.ThreeSquares
