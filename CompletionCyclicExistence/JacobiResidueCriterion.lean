/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Lean.Elab.Tactic.Omega
@[expose] public section
namespace CompletionTheory.ThreeSquares

 theorem jacobi_neg_two_at_three_mod_eight (n : ℕ) (hn : n%8=3) :
    jacobiSym (-2) n=1 := by
  have hno : Odd n := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.at_neg_two hno,ZMod.χ₈'_nat_eq_if_mod_eight]
  have hn2 : n%2=1 := by omega
  simp [hn,hn2]

 theorem jacobi_residue_criterion (n q : ℕ) (d : ℤ)
    (hn : n%8=3) (hq : q%4=1)
    (hqn : (-2*(q:ℤ))%(n:ℤ)=1%(n:ℤ))
    (hdn : (d*(n:ℤ))%(q:ℤ)=1%(q:ℤ)) :
    jacobiSym (-d) q=1 := by
  have hno : Odd n := Nat.odd_iff.mpr (by omega)
  have hqo : Odd q := Nat.odd_iff.mpr (by omega)
  have hqjn : jacobiSym (q:ℤ) n=1 := by
    have he := jacobiSym.mod_left' hqn
    rw [jacobiSym.mul_left,jacobi_neg_two_at_three_mod_eight n hn,
      one_mul,jacobiSym.one_left] at he
    exact he
  have hnjq : jacobiSym (n:ℤ) q=1 := by
    rw [←jacobiSym.quadratic_reciprocity_one_mod_four hq hno]
    exact hqjn
  have hdjq : jacobiSym d q=1 := by
    have he := jacobiSym.mod_left' hdn
    rw [jacobiSym.mul_left,hnjq,mul_one,jacobiSym.one_left] at he
    exact he
  rw [jacobiSym.neg d hqo,ZMod.χ₄_nat_one_mod_four hq,hdjq,one_mul]

end CompletionTheory.ThreeSquares
