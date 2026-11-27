/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Algebra.Ring.Int.Defs
import CompletionCyclicExistence.ThreeSquaresThreeModEight
@[expose] public section
namespace CompletionTheory.ThreeSquares

 theorem three_squares_of_three_mod_eight_api (n : ℕ) (hn : n%8=3) :
    ∃ a b c : ℤ,(n:ℤ)=a^2+b^2+c^2 :=
  three_squares_of_three_mod_eight n hn

end CompletionTheory.ThreeSquares
