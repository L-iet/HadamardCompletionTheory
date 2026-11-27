/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum
@[expose] public section
namespace CompletionTheory.ThreeSquares

 theorem odd_square_mod_eight (a : ℤ) (ha : Odd a) : a^2%8=1 := by
  obtain ⟨k,rfl⟩ := ha
  obtain ⟨j,hj⟩ := Int.even_mul_succ_self k
  have he : (2*k+1)^2=8*j+1 := by nlinarith
  rw [he]
  omega

 theorem square_mod_eight_cases (a : ℤ) : a^2%8=0 ∨ a^2%8=1 ∨ a^2%8=4 := by
  have h0 := Int.emod_nonneg a (by decide : (8:ℤ)≠0)
  have h8 := Int.emod_lt_of_pos a (by decide : (0:ℤ)<8)
  have he : a^2%8=((a%8)*(a%8))%8 := by simpa only [pow_two] using Int.mul_emod a a 8
  simp only [he]
  interval_cases h : a%8 <;> norm_num

 theorem three_square_mod_eight_odd (a b c : ℤ) (h : (a^2+b^2+c^2)%8=3) :
    Odd a ∧ Odd b ∧ Odd c := by
  have ha := square_mod_eight_cases a
  have hb := square_mod_eight_cases b
  have hc := square_mod_eight_cases c
  rw [Int.add_emod,Int.add_emod] at h
  have hr : a^2%8=1 ∧ b^2%8=1 ∧ c^2%8=1 := by
    rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
      rcases hc with hc | hc | hc <;> omega
  refine ⟨?_,?_,?_⟩
  · exact (Int.odd_pow' (by decide : (2:ℕ)≠0)).mp (Int.odd_iff.mpr (by omega))
  · exact (Int.odd_pow' (by decide : (2:ℕ)≠0)).mp (Int.odd_iff.mpr (by omega))
  · exact (Int.odd_pow' (by decide : (2:ℕ)≠0)).mp (Int.odd_iff.mpr (by omega))

 theorem sign_choice_mod_four (m a b c : ℤ) (hm : Odd m) (ha : Odd a)
    (hb : Odd b) (hc : Odd c) :
    ∃ u : ℤ,(u=a ∨ u=-a) ∧ (u+b+c-m)%4=0 := by
  have hm2 := Int.odd_iff.mp hm
  have ha2 := Int.odd_iff.mp ha
  have hb2 := Int.odd_iff.mp hb
  have hc2 := Int.odd_iff.mp hc
  by_cases h : (a+b+c-m)%4=0
  · exact ⟨a,Or.inl rfl,h⟩
  · exact ⟨-a,Or.inr rfl,by omega⟩

end CompletionTheory.ThreeSquares
