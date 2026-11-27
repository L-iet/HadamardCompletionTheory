/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCyclicExistence.UniformCyclicFamily
@[expose] public section
namespace CompletionTheory.ThreeSquares
open scoped BigOperators

def UniformFamilySolution (m : ℕ) [NeZero m] (t : ℤ) : Prop :=
  ∃ x : Fin 4 → ℤ,∀ k,cyclicNorm (uniformFamilyArray (m:=m) x) k=
    if k=0 then 4*t else 0

 theorem uniform_family_actual_solution {m : ℕ} [NeZero m] {t : ℤ}
    (h : UniformFamilySolution m t) : CyclicNormSolution m t := by
  obtain ⟨x,hx⟩ := h
  exact ⟨uniformFamilyArray x,uniform_family_odd x,hx⟩

 theorem uniform_family_fixed_sum_of_solution {m : ℕ} [NeZero m] (hm : 1<m)
    (x : Fin 4 → ℤ) (t : ℤ)
    (h : ∀ k,cyclicNorm (uniformFamilyArray (m:=m) x) k=if k=0 then 4*t else 0) :
    (∑ i,x i)=-(m:ℤ) ∧ (∑ i,(x i)^2)=t := by
  letI : Fact (1<m) := ⟨hm⟩
  have h10 : (1:ZMod m)≠0 := one_ne_zero
  have h0 := h 0
  have h1 := h 1
  simp only [uniform_family_norm,ite_true] at h0
  simp only [uniform_family_norm,h10,ite_false] at h1
  constructor <;> linarith

 theorem uniform_family_necessary_threshold {m : ℕ} [NeZero m]
    (hm : Odd m) (t : ℤ) (ht : Odd t) (h : UniformFamilySolution m t) :
    (m:ℤ)^2+3≤4*t := by
  by_cases h1 : m=1
  · subst m
    have hT := cyclicNorm_solution_energy_lower (uniform_family_actual_solution h)
    norm_num at *
    omega
  · have hm1 : 1<m := by have hz := NeZero.ne m;omega
    obtain ⟨x,hx⟩ := h
    obtain ⟨hs,hn⟩ := uniform_family_fixed_sum_of_solution hm1 x t hx
    have hC : (∑ i,x i)^2≤4*∑ i,(x i)^2 := by
      simp only [Fin.sum_univ_four]
      nlinarith [sq_nonneg (x 0-x 1),sq_nonneg (x 0-x 2),sq_nonneg (x 0-x 3),
        sq_nonneg (x 1-x 2),sq_nonneg (x 1-x 3),sq_nonneg (x 2-x 3)]
    rw [hs,hn] at hC
    simp only [neg_sq] at hC
    have hmOdd : Odd (m:ℤ) := by exact_mod_cast hm
    have hm8 := odd_square_mod_eight (m:ℤ) hmOdd
    have ht2 := Int.odd_iff.mp ht
    omega

end CompletionTheory.ThreeSquares
