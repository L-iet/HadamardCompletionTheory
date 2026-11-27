/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionLattice.KernelRetraction
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.NormNum
@[expose] public section
namespace CompletionTheory
noncomputable section
open scoped BigOperators

theorem integer_linear_functional_coordinates {N : ℕ}
    (L : (Fin N → ℤ) →ₗ[ℤ] ℤ) (x : Fin N → ℤ) :
    L x=∑ j,x j*L (Pi.single j 1) := by
  have he : (∑ j,x j • Pi.single j (1 : ℤ))=x := by
    funext i
    simp [Finset.sum_apply,Pi.single_apply]
  conv_lhs => rw [← he]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact L.map_smul (x j) (Pi.single j 1)

theorem integer_odd_dot_parity {N : ℕ} (x w : Fin N → ℤ) (hw : ∀ j,w j%2=1) :
    (∑ j,x j*w j)%2=(∑ j,x j)%2 := by
  have he : ∀ s : Finset (Fin N),(∑ j∈s,x j*w j)%2=(∑ j∈s,x j)%2 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih => simp [Finset.sum_insert,hj,Int.add_emod,Int.mul_emod,hw j,ih]
  exact he Finset.univ

theorem saturated_integer_kernel_alternative {N : ℕ} {T : Type*}
    [AddCommGroup T] [Module ℤ T] [Module.IsTorsionFree ℤ T]
    (f : (Fin N → ℤ) →ₗ[ℤ] T) :
    ((∃ x : Fin N → ℤ,f x=0 ∧ (∑ j,x j)%2=1) ∨
      (∃ w : Fin N → ℤ,(∀ j,w j%2=1) ∧ ∀ x,f x=0 → (∑ j,x j*w j)=0)) ∧
    ¬((∃ x : Fin N → ℤ,f x=0 ∧ (∑ j,x j)%2=1) ∧
      (∃ w : Fin N → ℤ,(∀ j,w j%2=1) ∧ ∀ x,f x=0 → (∑ j,x j*w j)=0)) := by
  classical
  have hdis : ¬((∃ x : Fin N → ℤ,f x=0 ∧ (∑ j,x j)%2=1) ∧
      (∃ w : Fin N → ℤ,(∀ j,w j%2=1) ∧ ∀ x,f x=0 → (∑ j,x j*w j)=0)) := by
    rintro ⟨⟨x,hx,ho⟩,w,hw,hann⟩
    have hp := integer_odd_dot_parity x w hw
    rw [hann x hx,ho] at hp
    norm_num at hp
  refine ⟨?_,hdis⟩
  by_cases hodd : ∃ x : Fin N → ℤ,f x=0 ∧ (∑ j,x j)%2=1
  · exact Or.inl hodd
  right
  obtain ⟨ρ,hρ⟩ := integer_kernel_retraction f
  let L : (Fin N → ℤ) →ₗ[ℤ] ℤ :=
    { toFun := fun x => ∑ j,(ρ x).val j
      map_add' := by intro x y; simp [map_add,Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        change (∑ j,(ρ (c • x)).val j)=c • (∑ j,(ρ x).val j)
        rw [ρ.map_smul]
        change (∑ j,c*(ρ x).val j)=c*(∑ j,(ρ x).val j)
        exact (Finset.mul_sum _ _ _).symm }
  let w : Fin N → ℤ := fun j => 1-L (Pi.single j 1)
  have heven (x : LinearMap.ker f) : (∑ j,x.val j)%2=0 := by
    have hn : (∑ j,x.val j)%2≠1 := by
      intro hh
      exact hodd ⟨x.val,x.property,hh⟩
    omega
  refine ⟨w,?_,?_⟩
  · intro j
    have hh := heven (ρ (Pi.single j 1))
    change L (Pi.single j 1)%2=0 at hh
    change (1-L (Pi.single j 1))%2=1
    omega
  · intro x hx
    have hL : L x=∑ j,x j := by
      have hh := hρ ⟨x,hx⟩
      exact congrArg (fun y : LinearMap.ker f => ∑ j,y.val j) hh
    have hc := integer_linear_functional_coordinates L x
    change (∑ j,x j*(1-L (Pi.single j 1)))=0
    simp_rw [mul_sub,mul_one]
    rw [Finset.sum_sub_distrib,← hc,hL,sub_self]

end
end CompletionTheory
