/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Tactic.Ring
@[expose] public section
namespace CompletionTheory.ThreeSquares

/-- A root modulo an odd modulus can be adjusted by that modulus so that
its quadratic value is divisible by twice the modulus. -/
 theorem odd_modulus_residue_lift (q d r : ℤ) (hq : Odd q) (hdiv : q ∣ r^2+d) :
    ∃ x y : ℤ,x^2+d=y*(2*q) := by
  obtain ⟨s,hs⟩ := hdiv
  rcases Int.even_or_odd s with ⟨b,hb⟩ | ⟨b,hb⟩
  · refine ⟨r,b,?_⟩
    calc
      _=q*s := hs
      _=b*(2*q) := by rw [hb];ring
  · obtain ⟨a,ha⟩ := hq
    refine ⟨r+q,a+b+r+1,?_⟩
    calc
      _=(r^2+d)+q*(2*r+q) := by ring
      _=q*(s+2*r+q) := by rw [hs];ring
      _=(a+b+r+1)*(2*q) := by rw [ha,hb];ring

end CompletionTheory.ThreeSquares
