/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCyclicExistence.JacobiResidueCriterion
public import CompletionCyclicExistence.OddModulusResidueLift
@[expose] public section
namespace CompletionTheory.ThreeSquares

 theorem prime_jacobi_residue_lift (q : ℕ) [Fact q.Prime] (d : ℤ)
    (hq : Odd q) (hJ : jacobiSym (-d) q=1) :
    ∃ x y : ℤ,x^2+d=y*(2*(q:ℤ)) := by
  letI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  obtain ⟨z,hz⟩ := ZMod.isSquare_of_jacobiSym_eq_one hJ
  have hdiv : (q:ℤ) ∣ (z.val:ℤ)^2+d := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
    simp only [Int.cast_add,Int.cast_pow,Int.cast_natCast,ZMod.natCast_zmod_val]
    rw [pow_two,←hz]
    simp
  have hqZ : Odd (q:ℤ) := by exact_mod_cast hq
  exact odd_modulus_residue_lift q d z.val hqZ hdiv

end CompletionTheory.ThreeSquares
