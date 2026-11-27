/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module

public import CompletionTheory.Order24Data

/-! # The explicit three-for-four order-24 exchange and its full completion

The exclusion of cheaper exchanges is a separate, still-unproved certificate.
-/

@[expose] public section
namespace CompletionTheory

def base24Frame : Matrix (Fin 16) (Fin 24) ℝ := encodedRealFrame base24Masks

def insert24Frame : Matrix (Fin 4) (Fin 24) ℝ := encodedRealFrame insert24Masks

def completion24Frame : Matrix (Fin 24) (Fin 24) ℝ := encodedRealFrame completion24Masks

theorem base24Frame_partialHadamard : IsPartialHadamard base24Frame :=
  encodedRealFrame_partialHadamard base24Masks base24_integer_gram

theorem insert24Frame_partialHadamard : IsPartialHadamard insert24Frame :=
  encodedRealFrame_partialHadamard insert24Masks insert24_integer_gram

theorem completion24Frame_hadamard : Matrix.IsHadamard completion24Frame :=
  isHadamard_mathlib (encodedRealFrame_partialHadamard completion24Masks completion24_integer_gram)

theorem base24_insert_cross : ∀ i : Fin 16, i ∉ delete24Rows → ∀ a : Fin 4,
    (∑ j : Fin 24, base24Frame i j * insert24Frame a j) = 0 := by
  intro i hi a
  have h := base24_insert_cross_integer i hi a
  change (∑ j : Fin 24, (encodedIntFrame base24Masks i j : ℝ) *
    (encodedIntFrame insert24Masks a j : ℝ)) = 0
  exact_mod_cast h

theorem base24_three_row_exchange : HasAugmentingExchange base24Frame 3 :=
  ⟨delete24Rows, delete24Rows_card, insert24Frame, insert24Frame_partialHadamard, base24_insert_cross⟩

theorem base24_exchangeCost_le_three : exchangeCost base24Frame ≤ (3 : WithTop ℕ) :=
  (exchangeCost_le_iff base24Frame 3).mpr ⟨3, le_rfl, base24_three_row_exchange⟩

def order24RepairIndex : ({i : Fin 16 // i ∉ delete24Rows} ⊕ Fin 4) → Fin 24 :=
  Sum.elim (fun i => retained24Position i.val) insert24Position

set_option maxRecDepth 10000 in
theorem order24RepairIndex_injective : Function.Injective order24RepairIndex := by decide

theorem completion24_retains_base (i : Fin 16) (hi : i ∉ delete24Rows) (j : Fin 24) :
    completion24Frame (retained24Position i) j = base24Frame i j := by
  change (encodedSign (completion24Masks (retained24Position i)) j.val : ℝ) =
    (encodedSign (base24Masks i) j.val : ℝ)
  rw [completion24_retains_masks i hi]

theorem completion24_retains_insert (i : Fin 4) (j : Fin 24) :
    completion24Frame (insert24Position i) j = insert24Frame i j := by
  change (encodedSign (completion24Masks (insert24Position i)) j.val : ℝ) =
    (encodedSign (insert24Masks i) j.val : ℝ)
  rw [completion24_insert_masks i]

theorem completion24_retains_exchange :
    ∀ r : ({i : Fin 16 // i ∉ delete24Rows} ⊕ Fin 4), ∀ j : Fin 24,
      completion24Frame (order24RepairIndex r) j = exchangeFrame base24Frame delete24Rows insert24Frame r j := by
  intro r j
  cases r with
  | inl i => exact completion24_retains_base i.val i.property j
  | inr i => exact completion24_retains_insert i j

theorem base24_exchange_with_completion : HasAugmentingExchange base24Frame 3 ∧
    ∃ H : Matrix (Fin 24) (Fin 24) ℝ, Matrix.IsHadamard H ∧
      ∃ e : ({i : Fin 16 // i ∉ delete24Rows} ⊕ Fin 4) ↪ Fin 24,
        ∀ r j, H (e r) j = exchangeFrame base24Frame delete24Rows insert24Frame r j := by
  exact ⟨base24_three_row_exchange, completion24Frame, completion24Frame_hadamard,
    ⟨order24RepairIndex, order24RepairIndex_injective⟩, completion24_retains_exchange⟩

end CompletionTheory
