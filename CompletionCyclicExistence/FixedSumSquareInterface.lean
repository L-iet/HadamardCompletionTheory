/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Algebra.BigOperators.Fin
import CompletionCyclicExistence.FourSquaresFixedSum
@[expose] public section
namespace CompletionTheory.ThreeSquares
open scoped BigOperators

 theorem four_squares_fixed_sum_api (m t : ℤ) (hm : Odd m) (ht : Odd t)
    (hlarge : m^2+3≤4*t) :
    ∃ x : Fin 4 → ℤ,(∑ i,x i)=-m ∧ (∑ i,(x i)^2)=t :=
  four_squares_with_fixed_odd_sum m t hm ht hlarge

end CompletionTheory.ThreeSquares
