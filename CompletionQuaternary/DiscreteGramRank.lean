/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionBloch.GramAxis
@[expose] public section
namespace CompletionTheory.Bloch
noncomputable section
open scoped BigOperators

theorem dot3_comm (r s : Fin 3 → ℝ) : dot3 r s=dot3 s r := by
  unfold dot3
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem dot3_neg_left (r s : Fin 3 → ℝ) : dot3 (-r) s= -dot3 r s := by
  simp [dot3,Finset.sum_neg_distrib]

theorem dot3_neg_right (r s : Fin 3 → ℝ) : dot3 r (-s)= -dot3 r s := by
  simp [dot3,Finset.sum_neg_distrib]

theorem dot3_difference (r s : Fin 3 → ℝ) :
    dot3 (r-s) (r-s)=dot3 r r+dot3 s s-2*dot3 r s := by
  simp [dot3,Fin.sum_univ_succ]
  ring

theorem unit_dot_one_eq {r s : Fin 3 → ℝ} (hr : dot3 r r=1) (hs : dot3 s s=1)
    (h : dot3 r s=1) : r=s := by
  by_contra hne
  have hp := dot3_positive (sub_ne_zero.mpr hne)
  rw [dot3_difference,hr,hs,h] at hp
  norm_num at hp

theorem unit_dot_minus_one_eq {r s : Fin 3 → ℝ} (hr : dot3 r r=1) (hs : dot3 s s=1)
    (h : dot3 r s= -1) : r= -s := by
  apply unit_dot_one_eq hr
  · rw [dot3_neg_left,dot3_neg_right,hs]
    norm_num
  · rw [dot3_neg_right,h]
    norm_num

theorem discrete_unit_classification {r s : Fin 3 → ℝ} (hr : dot3 r r=1) (hs : dot3 s s=1)
    (h : dot3 r s= -1 ∨ dot3 r s=0 ∨ dot3 r s=1) :
    r=s ∨ r= -s ∨ dot3 r s=0 := by
  rcases h with h|h|h
  · exact Or.inr (Or.inl (unit_dot_minus_one_eq hr hs h))
  · exact Or.inr (Or.inr h)
  · exact Or.inl (unit_dot_one_eq hr hs h)

theorem discrete_unit_gram_rank_le_two {n : ℕ} (hn : 0<n) (M : Matrix (Fin n) (Fin 3) ℝ)
    (hunit : ∀ i,dot3 (M i) (M i)=1)
    (hdiscrete : ∀ i j,dot3 (M i) (M j)= -1 ∨ dot3 (M i) (M j)=0 ∨ dot3 (M i) (M j)=1)
    (hno : ∀ i j k,¬(dot3 (M i) (M j)=0 ∧ dot3 (M j) (M k)=0 ∧ dot3 (M k) (M i)=0)) :
    (M*M.transpose).rank≤2 := by
  classical
  let i0 : Fin n := ⟨0,hn⟩
  by_cases hp : ∃ j,dot3 (M i0) (M j)=0
  · obtain ⟨j0,hij⟩ := hp
    have hji : dot3 (M j0) (M i0)=0 := by rw [dot3_comm]; exact hij
    have hall (i : Fin n) : M i=M i0 ∨ M i= -M i0 ∨ M i=M j0 ∨ M i= -M j0 := by
      rcases discrete_unit_classification (hunit i) (hunit i0) (hdiscrete i i0) with h|h|h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · rcases discrete_unit_classification (hunit i) (hunit j0) (hdiscrete i j0) with h'|h'|h'
        · exact Or.inr (Or.inr (Or.inl h'))
        · exact Or.inr (Or.inr (Or.inr h'))
        · exact False.elim (hno i0 j0 i ⟨hij,by rw [dot3_comm]; exact h',h⟩)
    let A : Matrix (Fin 2) (Fin 3) ℝ := ![M i0,M j0]
    let C : Matrix (Fin n) (Fin 2) ℝ := fun i => ![dot3 (M i) (M i0),dot3 (M i) (M j0)]
    have he : M=C*A := by
      ext i k
      change M i k = ∑ j : Fin 2, C i j * A j k
      rcases hall i with h|h|h|h <;>
        simp [Matrix.mul_apply,Fin.sum_univ_succ,A,C,h,dot3_neg_left,hunit i0,hunit j0,hij,hji]
    rw [Matrix.rank_self_mul_transpose,he]
    exact (Matrix.rank_mul_le_left C A).trans (Matrix.rank_le_width C)
  · have hall (i : Fin n) : M i=M i0 ∨ M i= -M i0 := by
      rcases discrete_unit_classification (hunit i) (hunit i0) (hdiscrete i i0) with h|h|h
      · exact Or.inl h
      · exact Or.inr h
      · exact False.elim (hp ⟨i,by rw [dot3_comm]; exact h⟩)
    let A : Matrix (Fin 2) (Fin 3) ℝ := ![M i0,0]
    let C : Matrix (Fin n) (Fin 2) ℝ := fun i => ![dot3 (M i) (M i0),0]
    have he : M=C*A := by
      ext i k
      change M i k = ∑ j : Fin 2, C i j * A j k
      rcases hall i with h|h <;>
        simp [Matrix.mul_apply,Fin.sum_univ_succ,A,C,h,dot3_neg_left,hunit i0]
    rw [Matrix.rank_self_mul_transpose,he]
    exact (Matrix.rank_mul_le_left C A).trans (Matrix.rank_le_width C)

end
end CompletionTheory.Bloch
