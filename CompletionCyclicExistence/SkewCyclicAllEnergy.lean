/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCharacter.Full
public import CompletionCyclicExistence.ThreeSquareExistenceInterface
public import CompletionCyclicExistence.OddSquareArithmetic
@[expose] public section
namespace CompletionTheory.ThreeSquares
open CharacterFloor
open scoped BigOperators

 theorem character_template_actual_solution {m : ℕ} [NeZero m] (L : ZMod m → ℤ)
    (t : ℤ) (h : CharacterTemplateEnergy L t) : CyclicNormSolution m t := by
  obtain ⟨u,v,w,r,hA,hn⟩ := h
  refine ⟨fun i z => fullCharacterAnsatz L u v w i (z-r i),?_,hn⟩
  intro i z
  have he := (ZMod.intCast_eq_intCast_iff' (fullCharacterAnsatz L u v w i (z-r i)) 1 2).mpr
    (by simpa using hA i z)
  simpa using he

 theorem skew_template_all_odd_energies {m : ℕ} [NeZero m] (q : ℤ)
    (hM : (m:ℤ)=4*q+3) (L : ZMod m → ℤ) (hD : IsCharacterData L (-1))
    (t : ℤ) (ht : Odd t) (hT : q^2+3*q+3≤t) : CharacterTemplateEnergy L t := by
  obtain ⟨hzero,hs,hcor,hreflect⟩ := hD
  have hL := character_augmentation_zero L hcor
  let n : ℕ := (4*t-3*(m:ℤ)-4*q^2).toNat
  have hlarge : 3≤4*t-3*(m:ℤ)-4*q^2 := by nlinarith
  have hcast : (n:ℤ)=4*t-3*(m:ℤ)-4*q^2 := Int.toNat_of_nonneg (by omega)
  obtain ⟨j,hj⟩ := Int.even_mul_succ_self q
  have hpoly : 3*(m:ℤ)+4*q^2=8*(j+q+1)+1 := by rw [hM];nlinarith
  have ht2 := Int.odd_iff.mp ht
  have hmod : (4*t-3*(m:ℤ)-4*q^2)%8=3 := by omega
  have hnmod : n%8=3 := by
    have hi : (n:ℤ)%8=3 := by rw [hcast];exact hmod
    exact_mod_cast hi
  obtain ⟨a,b,c,habc⟩ := three_squares_of_three_mod_eight_api n hnmod
  have habcmod : (a^2+b^2+c^2)%8=3 := by rw [←habc,hcast];exact hmod
  obtain ⟨ha,hb,hc⟩ := three_square_mod_eight_odd a b c habcmod
  have ha2 := Int.odd_iff.mp ha
  have hb2 := Int.odd_iff.mp hb
  have hc2 := Int.odd_iff.mp hc
  let u : Fin 4 → ℤ := ![1,1,1,0]
  let v : Fin 4 → ℤ := ![a,b,c,-2*q]
  let w : Fin 4 → ℤ := ![0,0,0,1]
  refine ⟨u,v,w,fun _ => 0,?_,?_⟩
  · simp only [sub_zero]
    apply full_template_odd_of_parities L hzero hs u v w
    · intro i;fin_cases i <;> simp [u,v,w] <;> omega
    · intro i;fin_cases i <;> simp [u,v,w] <;> omega
  · intro z
    simp only [sub_zero]
    rw [fullCharacterAnsatz_norm L hzero hL hcor (-1) hreflect u v w]
    by_cases hz : z=0 <;> simp [hz,squareSum,scalarDot,Fin.sum_univ_four,u,v,w,hM] <;>
      nlinarith [habc,hcast]

end CompletionTheory.ThreeSquares
