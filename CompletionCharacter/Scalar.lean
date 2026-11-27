/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.CyclicEnergy
public import Mathlib.Tactic.Positivity
@[expose] public section
namespace CompletionTheory.CharacterFloor
open scoped BigOperators

def squareSum (a : Fin 4 → ℤ) : ℤ := ∑ i,a i^2

def scalarDot (a b : Fin 4 → ℤ) : ℤ := ∑ i,a i*b i

theorem squareSum_nonnegative (a : Fin 4 → ℤ) : 0≤squareSum a :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem integer_square_positive {a : ℤ} (h : a≠0) : 1≤a^2 := by
  have hc : a≤ -1 ∨ 1≤a := by omega
  rcases hc with hc|hc <;> nlinarith [sq_nonneg (a+1),sq_nonneg (a-1)]

theorem scalar_cauchy (a b : Fin 4 → ℤ) :
    scalarDot a b^2≤squareSum a*squareSum b := by
  simp only [scalarDot,squareSum,Fin.sum_univ_four]
  nlinarith [sq_nonneg (a 0*b 1-a 1*b 0),sq_nonneg (a 0*b 2-a 2*b 0),
    sq_nonneg (a 0*b 3-a 3*b 0),sq_nonneg (a 1*b 2-a 2*b 1),
    sq_nonneg (a 1*b 3-a 3*b 1),sq_nonneg (a 2*b 3-a 3*b 2)]

theorem scalar_constant_nonzero {m : ℤ} (u v w : Fin 4 → ℤ)
    (hp : ∀ i,(u i+w i)%2=1)
    (he : 2*scalarDot w v=squareSum u-m*squareSum w) :
    0<squareSum w := by
  have hw := squareSum_nonnegative w
  by_contra h
  have hz : squareSum w=0 := by omega
  have hwj : ∀ j,w j=0 := by
    intro j
    have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (w i))).mp hz j (Finset.mem_univ _)
    nlinarith
  have hu : squareSum u=0 := by
    have hh : (0 : ℤ)=squareSum u := by simpa [scalarDot,squareSum,hwj] using he
    exact hh.symm
  have huj := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (u i))).mp hu (0 : Fin 4) (Finset.mem_univ _)
  have hu0 : u 0=0 := by nlinarith
  have hh := hp 0
  norm_num [hwj,hu0] at hh

theorem scalar_energy_cauchy {m t : ℤ} (u v w : Fin 4 → ℤ)
    (he : 2*scalarDot w v=squareSum u-m*squareSum w)
    (ht : 4*t=m*squareSum u+squareSum v) :
    (squareSum u+m*squareSum w)^2≤16*squareSum w*t := by
  have hcs := scalar_cauchy w v
  have he2 := congrArg (fun z : ℤ => z^2) he
  have htW := congrArg (fun z : ℤ => squareSum w*z) ht
  nlinarith [he2,htW]

theorem squareSum_one_unique (w : Fin 4 → ℤ) (hw : squareSum w=1) :
    ∃ i,w i^2=1 ∧ ∀ j,j≠i → w j=0 := by
  have hex : ∃ i,w i≠0 := by
    by_contra! h
    simp [squareSum,h] at hw
  obtain ⟨i,hi⟩ := hex
  have hb : w i^2≤squareSum w := Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hp := integer_square_positive hi
  have hs : w i^2=1 := by omega
  refine ⟨i,hs,?_⟩
  intro j hji
  have hdec := Finset.sum_erase_add (s:=Finset.univ) (f:=fun k => w k^2) (Finset.mem_univ i)
  have hrest : (∑ k∈Finset.univ.erase i,w k^2)=0 := by change _=squareSum w at hdec; omega
  have hjmem : j∈Finset.univ.erase i := Finset.mem_erase.mpr ⟨hji,Finset.mem_univ _⟩
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (w k))).mp hrest j hjmem
  nlinarith

end CompletionTheory.CharacterFloor
