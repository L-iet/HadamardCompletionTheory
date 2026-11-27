/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCyclicExistence.ThreeSquaresThreeModEight
public import CompletionCyclicExistence.FourSquaresFixedSumAlgebra
@[expose] public section
namespace CompletionTheory.ThreeSquares
open scoped BigOperators

 theorem four_squares_with_fixed_odd_sum (m t : ℤ) (hm : Odd m) (ht : Odd t)
    (hlarge : m^2+3≤4*t) :
    ∃ x : Fin 4 → ℤ,(∑ i,x i)=-m ∧ (∑ i,(x i)^2)=t := by
  have hm8 := odd_square_mod_eight m hm
  have ht2 := Int.odd_iff.mp ht
  have hNmod : (4*t-m^2)%8=3 := by omega
  let n : ℕ := (4*t-m^2).toNat
  have hcast : (n:ℤ)=4*t-m^2 := Int.toNat_of_nonneg (by omega)
  have hnmod : n%8=3 := by
    have hi : (n:ℤ)%8=3 := by rw [hcast];exact hNmod
    exact_mod_cast hi
  obtain ⟨u,v,w,hrep⟩ := three_squares_of_three_mod_eight n hnmod
  have h3 : (u^2+v^2+w^2)%8=3 := by rw [←hrep,hcast];exact hNmod
  obtain ⟨hu,hv,hw⟩ := three_square_mod_eight_odd u v w h3
  obtain ⟨u',hsign,hcong⟩ := sign_choice_mod_four m u v w hm hu hv hw
  have hu' : Odd u' := by
    rcases hsign with h | h
    · rw [h];exact hu
    · rw [h];exact hu.neg
  have hsq : u'^2=u^2 := by
    rcases hsign with h | h <;> rw [h] <;> ring
  have hN : m^2+u'^2+v^2+w^2=4*t := by rw [hsq];linarith
  exact fixed_sum_from_odd_three_squares m t u' v w hu' hv hw hcong hN

end CompletionTheory.ThreeSquares
