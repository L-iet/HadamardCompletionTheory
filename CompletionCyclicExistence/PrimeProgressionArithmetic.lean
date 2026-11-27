/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega
@[expose] public section
namespace CompletionTheory.ThreeSquares

 theorem three_mod_eight_progression_coprime (k : ℕ) :
    (4*k+1).Coprime (4*(8*k+3)) := by
  rw [Nat.coprime_mul_iff_right]
  constructor
  · have h2 : (4*k+1).Coprime 2 :=
      Nat.coprime_two_right.mpr ⟨2*k,by ring⟩
    simpa using h2.pow_right 2
  · have he : 8*k+3=1+2*(4*k+1) := by ring
    rw [he,Nat.coprime_add_mul_right_right]
    simp

 theorem three_mod_eight_progression_parameter (k q : ℕ)
    (hq : Nat.ModEq (4*(8*k+3)) q (4*k+1)) (hlarge : 4*k+1≤q) :
    ∃ j : ℕ,q=(4*k+1)+4*(8*k+3)*j :=
  (Nat.modEq_iff_exists_eq_add hlarge).mp hq.symm

 theorem three_mod_eight_progression_data (k j q : ℕ)
    (he : q=(4*k+1)+4*(8*k+3)*j) :
    q%4=1 ∧ (8*(j:ℤ)+1)*(8*(k:ℤ)+3)=2*(q:ℤ)+1 := by
  constructor
  · have h : q=1+4*(k+(8*k+3)*j) := by rw [he];ring
    rw [h]
    simp
  · rw [he]
    push_cast
    ring

end CompletionTheory.ThreeSquares
