/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCyclicExistence.OddSquareArithmetic
public import Mathlib.Algebra.BigOperators.Fin
@[expose] public section
namespace CompletionTheory.ThreeSquares
open scoped BigOperators

 theorem fixed_sum_from_odd_three_squares (m t u v w : ℤ)
    (hu : Odd u) (hv : Odd v) (hw : Odd w) (hcong : (u+v+w-m)%4=0)
    (hN : m^2+u^2+v^2+w^2=4*t) :
    ∃ x : Fin 4 → ℤ,(∑ i,x i)=-m ∧ (∑ i,(x i)^2)=t := by
  have hu2 := Int.odd_iff.mp hu
  have hv2 := Int.odd_iff.mp hv
  have hw2 := Int.odd_iff.mp hw
  let a := (-m+u+v+w)/4
  let b := (-m+u-v-w)/4
  let c := (-m-u+v-w)/4
  let d := (-m-u-v+w)/4
  have hA : 4*a=-m+u+v+w := by dsimp [a];omega
  have hB : 4*b=-m+u-v-w := by dsimp [b];omega
  have hC : 4*c=-m-u+v-w := by dsimp [c];omega
  have hD : 4*d=-m-u-v+w := by dsimp [d];omega
  have hs : a+b+c+d=-m := by omega
  have he : (4*a)^2+(4*b)^2+(4*c)^2+(4*d)^2=4*(m^2+u^2+v^2+w^2) := by
    rw [hA,hB,hC,hD]
    ring
  have hn : a^2+b^2+c^2+d^2=t := by nlinarith
  refine ⟨![a,b,c,d],?_,?_⟩
  · simpa [Fin.sum_univ_four] using hs
  · simpa [Fin.sum_univ_four] using hn

end CompletionTheory.ThreeSquares
