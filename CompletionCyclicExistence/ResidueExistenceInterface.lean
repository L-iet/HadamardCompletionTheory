/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Algebra.Ring.Int.Defs
import CompletionCyclicExistence.ThreeModEightResidueExistence
@[expose] public section
namespace CompletionTheory.ThreeSquares

/-- A small public API: the arithmetic and analytic proof imports remain private.
The original unconditional proof remains a kernel-visible dependency. -/
 theorem residue_data_exists_three_mod_eight_api (n : ℕ) (hn : n%8=3) :
    ∃ d x y : ℤ,0<d ∧ x^2+d=y*(d*(n:ℤ)-1) :=
  residue_data_exists_three_mod_eight n hn

end CompletionTheory.ThreeSquares
