module

public import CompletionTheory.CodimensionTwo

/-! # Completion at every positive even order with two missing rows -/

@[expose] public section
namespace CompletionTheory

theorem even_order_defect_two_completion {n : ℕ} (hn : 2 ≤ n) (heven : Even n)
    (P : Matrix (Fin (n - 2)) (Fin n) ℝ) (hP : IsPartialHadamard P) :
    ∃ (H : Matrix (Fin n) (Fin n) ℝ) (rows : Fin (n - 2) ↪ Fin n),
      Matrix.IsHadamard H ∧ ∀ i j, H (rows i) j = P i j := by
  apply codimension_two_completion_of_card (by simp only [Fintype.card_fin]; omega) P hP
  simp only [Fintype.card_fin]
  obtain ⟨k, hk⟩ := heven
  exact ⟨k - 1, by omega⟩

end CompletionTheory
