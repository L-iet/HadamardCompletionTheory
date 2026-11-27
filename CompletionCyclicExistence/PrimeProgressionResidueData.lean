/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCyclicExistence.PrimeResidueLift
public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.Linarith
@[expose] public section
namespace CompletionTheory.ThreeSquares

 theorem prime_progression_residue_data (n q : ℕ) [Fact q.Prime] (d : ℤ)
    (hn : n%8=3) (hq : q%4=1) (hD : d*(n:ℤ)=2*(q:ℤ)+1) :
    ∃ x y : ℤ,x^2+d=y*(d*(n:ℤ)-1) := by
  have hqn : Int.ModEq (n:ℤ) (-2*(q:ℤ)) 1 := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨d,?_⟩
    calc
      _=d*(n:ℤ) := by linarith
      _=(n:ℤ)*d := mul_comm _ _
  have hdn : Int.ModEq (q:ℤ) (d*(n:ℤ)) 1 := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-2,?_⟩
    rw [hD]
    ring
  have hJ := jacobi_residue_criterion n q d hn hq hqn hdn
  have hqo : Odd q := Nat.odd_iff.mpr (by omega)
  obtain ⟨x,y,he⟩ := prime_jacobi_residue_lift q d hqo hJ
  refine ⟨x,y,?_⟩
  have hd : d*(n:ℤ)-1=2*(q:ℤ) := by linarith
  simpa only [hd] using he

end CompletionTheory.ThreeSquares
