/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.InnerProductSpace.PiL2
@[expose] public section
namespace CompletionTheory
noncomputable section
open scoped BigOperators

def integerToRationalLinear (N : ℕ) : (Fin N → ℤ) →ₗ[ℤ] (Fin N → ℚ) where
  toFun x := fun j => (x j : ℚ)
  map_add' x y := by funext j; simp
  map_smul' c x := by funext j; simp [zsmul_eq_mul]

def rationalCoordinateDot (N : ℕ) : LinearMap.BilinForm ℚ (Fin N → ℚ) := dotProductBilin ℚ ℚ


theorem rational_saturated_lattice_alternative {N : ℕ}
    (V : Submodule ℚ (Fin N → ℚ)) :
    ((∃ x : Fin N → ℤ,integerToRationalLinear N x∈V ∧ (∑ j,x j)%2=1) ∨
      (∃ w : Fin N → ℤ,(∀ j,w j%2=1) ∧
        integerToRationalLinear N w∈(rationalCoordinateDot N).orthogonal V)) ∧
    ¬((∃ x : Fin N → ℤ,integerToRationalLinear N x∈V ∧ (∑ j,x j)%2=1) ∧
      (∃ w : Fin N → ℤ,(∀ j,w j%2=1) ∧
        integerToRationalLinear N w∈(rationalCoordinateDot N).orthogonal V)) := by sorry

def witnessBudget {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Matrix ι κ ℝ) (f : κ → ℤ) : ℝ :=
  (Fintype.card κ : ℝ) * (∑ j, (f j : ℝ)^2) -
    ∑ i, (∑ j, P i j * (f j : ℝ))^2

theorem rational_row_span_zero_budget {r N : ℕ}
    (P : Matrix (Fin r) (Fin N) ℤ)
    (hP : ∀ i j : Fin r,(∑ k : Fin N,(P i k : ℝ)*(P j k : ℝ))=
      if i=j then (N : ℝ) else 0)
    (x : Fin N → ℤ)
    (hx : integerToRationalLinear N x∈Submodule.span ℚ
      (Set.range (fun i : Fin r => fun j : Fin N => (P i j : ℚ)))) :
    witnessBudget (fun i j => (P i j : ℝ)) x=0 := by sorry

end
end CompletionTheory
