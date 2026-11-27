/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP
@[expose] public section
namespace CompletionTheory.ThreeSquares

 theorem large_prime_in_progression (a m bound : ℕ) (hm : m≠0) (hcop : a.Coprime m) :
    ∃ q : ℕ,bound<q ∧ q.Prime ∧ Nat.ModEq m q a :=
  Nat.forall_exists_prime_gt_and_modEq bound hm hcop

end CompletionTheory.ThreeSquares
