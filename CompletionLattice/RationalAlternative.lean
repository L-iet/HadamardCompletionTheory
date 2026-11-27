/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionLattice.KernelAlternative
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Tactic.Ring
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
@[expose] public section
namespace CompletionTheory
noncomputable section
open scoped BigOperators

def integerToRationalLinear (N : ℕ) : (Fin N → ℤ) →ₗ[ℤ] (Fin N → ℚ) where
  toFun x := fun j => (x j : ℚ)
  map_add' x y := by funext j; simp
  map_smul' c x := by funext j; simp [zsmul_eq_mul]

def rationalCoordinateDot (N : ℕ) : LinearMap.BilinForm ℚ (Fin N → ℚ) := dotProductBilin ℚ ℚ

theorem integer_annihilator_rational_extension {N : ℕ}
    (V : Submodule ℚ (Fin N → ℚ)) (w : Fin N → ℤ)
    (hann : ∀ x : Fin N → ℤ,integerToRationalLinear N x∈V → (∑ j,x j*w j)=0) :
    integerToRationalLinear N w∈(rationalCoordinateDot N).orthogonal V := by
  intro v hv
  obtain ⟨b,hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) v
  choose x hx using hb
  have he : integerToRationalLinear N x=(b.val : ℚ) • v := by
    funext j
    simpa [integerToRationalLinear,Algebra.smul_def] using hx j
  have hxV : integerToRationalLinear N x∈V := by
    rw [he]
    exact V.smul_mem (b.val : ℚ) hv
  have hz : (∑ j,(x j : ℚ)*(w j : ℚ))=0 := by exact_mod_cast hann x hxV
  have hbne : (b.val : ℚ)≠0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero b
  have hh : (b.val : ℚ)*(∑ j,v j*(w j : ℚ))=0 := by
    calc
      _=∑ j,((b.val : ℚ)*v j)*(w j : ℚ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _=∑ j,(x j : ℚ)*(w j : ℚ) := by
        apply Finset.sum_congr rfl
        intro j _
        have hj := congrFun he j
        change (x j : ℚ)=(b.val : ℚ)*v j at hj
        rw [hj]
      _=0 := hz
  exact (mul_eq_zero.mp hh).resolve_left hbne

theorem rational_saturated_lattice_alternative {N : ℕ}
    (V : Submodule ℚ (Fin N → ℚ)) :
    ((∃ x : Fin N → ℤ,integerToRationalLinear N x∈V ∧ (∑ j,x j)%2=1) ∨
      (∃ w : Fin N → ℤ,(∀ j,w j%2=1) ∧
        integerToRationalLinear N w∈(rationalCoordinateDot N).orthogonal V)) ∧
    ¬((∃ x : Fin N → ℤ,integerToRationalLinear N x∈V ∧ (∑ j,x j)%2=1) ∧
      (∃ w : Fin N → ℤ,(∀ j,w j%2=1) ∧
        integerToRationalLinear N w∈(rationalCoordinateDot N).orthogonal V)) := by
  let Q := (Fin N → ℚ) ⧸ V
  letI : Module.IsTorsionFree ℤ Q := Module.IsTorsionFree.trans ℚ
  let f : (Fin N → ℤ) →ₗ[ℤ] Q := (V.mkQ.restrictScalars ℤ).comp (integerToRationalLinear N)
  have hfx : ∀ x,f x=0 ↔ integerToRationalLinear N x∈V := by
    intro x
    exact Submodule.Quotient.mk_eq_zero V
  have hA : (∃ x : Fin N → ℤ,f x=0 ∧ (∑ j,x j)%2=1) ↔
      (∃ x : Fin N → ℤ,integerToRationalLinear N x∈V ∧ (∑ j,x j)%2=1) := by
    simp only [hfx]
  have hB : (∃ w : Fin N → ℤ,(∀ j,w j%2=1) ∧ ∀ x,f x=0 → (∑ j,x j*w j)=0) ↔
      (∃ w : Fin N → ℤ,(∀ j,w j%2=1) ∧ integerToRationalLinear N w∈(rationalCoordinateDot N).orthogonal V) := by
    constructor
    · rintro ⟨w,hw,hann⟩
      exact ⟨w,hw,integer_annihilator_rational_extension V w (fun x hx => hann x ((hfx x).mpr hx))⟩
    · rintro ⟨w,hw,hann⟩
      refine ⟨w,hw,?_⟩
      intro x hx
      have hh := hann _ ((hfx x).mp hx)
      change (∑ j,(x j : ℚ)*(w j : ℚ))=0 at hh
      exact_mod_cast hh
  simpa only [hA,hB] using saturated_integer_kernel_alternative f

end
end CompletionTheory
