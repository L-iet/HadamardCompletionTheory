/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.CyclicEnergy
public import CompletionCyclicExistence.OddSquareArithmetic
@[expose] public section
namespace CompletionTheory.ThreeSquares
open scoped BigOperators

def uniformFamilyArray {m : ℕ} (x : Fin 4 → ℤ) (i : Fin 4) (z : ZMod m) : ℤ :=
  1+2*x i*(if z=0 then 1 else 0)

 theorem uniform_single_array_correlation {m : ℕ} [NeZero m] (a : ℤ) (k : ZMod m) :
    (∑ z : ZMod m,(1+2*a*(if z=0 then 1 else 0))*
      (1+2*a*(if z-k=0 then 1 else 0)))=
      (m:ℤ)+4*a+(if k=0 then 4*a^2 else 0) := by
  have he (z : ZMod m) : (1+2*a*(if z=0 then 1 else 0))*
      (1+2*a*(if z-k=0 then 1 else 0))=
      1+2*a*(if z=0 then 1 else 0)+2*a*(if z=k then 1 else 0)+
        (if k=0 then 4*a^2*(if z=0 then 1 else 0) else 0) := by
    by_cases hk : k=0 <;> by_cases hz : z=0 <;> by_cases hzk : z=k <;>
      simp_all [sub_eq_zero] <;> ring
  calc
    _=∑ z : ZMod m,(1+2*a*(if z=0 then 1 else 0)+2*a*(if z=k then 1 else 0)+
      (if k=0 then 4*a^2*(if z=0 then 1 else 0) else 0)) :=
      Finset.sum_congr rfl (fun z _ => he z)
    _=_ := by
      by_cases hk : k=0 <;> simp [hk,Finset.sum_add_distrib,mul_ite] <;> ring

 theorem uniform_family_norm {m : ℕ} [NeZero m] (x : Fin 4 → ℤ) (k : ZMod m) :
    cyclicNorm (uniformFamilyArray x) k=
      4*((m:ℤ)+∑ i,x i)+(if k=0 then 4*∑ i,(x i)^2 else 0) := by
  unfold cyclicNorm uniformFamilyArray
  rw [Finset.sum_comm]
  simp_rw [uniform_single_array_correlation]
  simp only [Fin.sum_univ_four]
  by_cases hk : k=0 <;> simp [hk] <;> ring

 theorem uniform_family_odd {m : ℕ} (x : Fin 4 → ℤ) :
    ∀ i z,(uniformFamilyArray (m:=m) x i z : ZMod 2)=1 := by
  intro i z
  simp [uniformFamilyArray,show (2:ZMod 2)=0 by decide]

 theorem uniform_family_of_fixed_sum {m : ℕ} [NeZero m] (x : Fin 4 → ℤ) (t : ℤ)
    (hs : (∑ i,x i)=-(m:ℤ)) (hn : (∑ i,(x i)^2)=t) :
    ∀ k,cyclicNorm (uniformFamilyArray (m:=m) x) k=if k=0 then 4*t else 0 := by
  intro k
  rw [uniform_family_norm,hs,hn]
  by_cases hk : k=0 <;> simp [hk]

end CompletionTheory.ThreeSquares
