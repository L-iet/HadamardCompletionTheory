/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module

public import CompletionTheory.EncodedFrames

/-! # Explicit integer data for the order-24 exchange certificate

Each set bit denotes a negative entry, starting at coordinate zero.
The integer Gram certificates are checked by kernel reduction.+-/

@[expose] public section
namespace CompletionTheory

def base24Masks : Fin 16 → ℕ :=
  ![0, 16773120, 16519104, 10359454, 7684730, 5820908, 9389414, 1547504,
    6736278, 11838780, 3701846, 13790378, 10646512, 2963882, 12892774, 5974836]

def insert24Masks : Fin 4 → ℕ := ![353924, 1104648, 2786850, 4759768]

def completion24Masks : Fin 24 → ℕ :=
  ![16773120, 16519104, 10359454, 7684730, 1547504, 6736278, 11838780,
    3701846, 13790378, 10646512, 2963882, 12892774, 5974836,
    353924, 1104648, 2786850, 4759768,
    5133676, 7583694, 9432922, 10076646, 10684492, 12653842, 15326908]

def delete24Rows : Finset (Fin 16) := {0, 5, 6}

def retained24Position : Fin 16 → Fin 24 :=
  ![0, 0, 1, 2, 3, 0, 0, 4, 5, 6, 7, 8, 9, 10, 11, 12]

def insert24Position (i : Fin 4) : Fin 24 := ⟨13 + i.val, by omega⟩

theorem delete24Rows_card : delete24Rows.card = 3 := by decide

theorem completion24_retains_masks :
    ∀ i : Fin 16, i ∉ delete24Rows → completion24Masks (retained24Position i) = base24Masks i := by
  decide

theorem completion24_insert_masks :
    ∀ i : Fin 4, completion24Masks (insert24Position i) = insert24Masks i := by
  decide

set_option maxRecDepth 10000 in
theorem base24_integer_gram :
    (encodedIntFrame base24Masks : Matrix (Fin 16) (Fin 24) ℤ) *
      (encodedIntFrame base24Masks).transpose = (24 : ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ) := by
  decide

set_option maxRecDepth 10000 in
theorem insert24_integer_gram :
    (encodedIntFrame insert24Masks : Matrix (Fin 4) (Fin 24) ℤ) *
      (encodedIntFrame insert24Masks).transpose = (24 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  decide

set_option maxRecDepth 10000 in
theorem completion24_integer_gram :
    (encodedIntFrame completion24Masks : Matrix (Fin 24) (Fin 24) ℤ) *
      (encodedIntFrame completion24Masks).transpose = (24 : ℤ) • (1 : Matrix (Fin 24) (Fin 24) ℤ) := by
  decide

set_option maxRecDepth 10000 in
theorem base24_insert_cross_integer :
    ∀ i : Fin 16, i ∉ delete24Rows → ∀ a : Fin 4,
      (∑ j : Fin 24, encodedIntFrame base24Masks i j * encodedIntFrame insert24Masks a j) = 0 := by
  decide

end CompletionTheory
