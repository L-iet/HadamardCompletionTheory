/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module

public import PhaseGeometry.Finite
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section
namespace PhaseGeometry
open scoped BigOperators

def IsSign {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∀ i j, H i j = 1 ∨ H i j = -1

theorem sign_square {z : ℤ} (hz : z = 1 ∨ z = -1) : z ^ 2 = 1 := by
  rcases hz with rfl | rfl <;> norm_num

theorem flipCell_isSign {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ}
    (hH : IsSign H) (a b : Fin n) : IsSign (flipCell H a b) := by
  intro i j
  simp only [flipCell]
  split_ifs
  · rcases hH i j with h | h <;> simp [h]
  · exact hH i j

theorem rowGram_symmetric {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    rowGram H i j = rowGram H j i := by
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem rowGram_diagonal {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ}
    (hH : IsSign H) (i : Fin n) : rowGram H i i = n := by
  unfold rowGram
  have h : ∀ k, H i k * H i k = 1 := by
    intro k
    nlinarith [sign_square (hH i k)]
  simp [h]

theorem rowGram_flip_unaffected {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ)
    (a b i j : Fin n) (hi : i ≠ a) (hj : j ≠ a) :
    rowGram (flipCell H a b) i j = rowGram H i j := by
  simp [rowGram, flipCell, hi, hj]

/-- A symmetric matrix supported on one off-diagonal star has twice the
sum of its central row. This is an exact finite-sum identity. -/
theorem sum_symmetric_star {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ι → ℤ) (a : ι) (hs : ∀ i j, f i j = f j i)
    (hd : f a a = 0) (hz : ∀ i j, i ≠ a → j ≠ a → f i j = 0) :
    (∑ i, ∑ j, f i j) = 2 * ∑ j, f a j := by
  have he : ∀ i j, f i j = (if i = a then f a j else 0) +
      (if j = a then f a i else 0) := by
    intro i j
    by_cases hi : i = a <;> by_cases hj : j = a
    · subst i; subst j; simp [hd]
    · subst i; simp [hj]
    · subst j; simp [hi, hs i a]
    · simp [hi, hj, hz i j hi hj]
  calc
    _ = ∑ i, ∑ j, ((if i = a then f a j else 0) +
        (if j = a then f a i else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact he i j
    _ = _ := by simp [Finset.sum_add_distrib]; ring

theorem gramEnergy_eq_gramSquares_sub {n : ℕ}
    {H : Matrix (Fin n) (Fin n) ℤ} (hH : IsSign H) :
    gramEnergy H = (∑ i, ∑ j, rowGram H i j ^ 2) - (n : ℤ) ^ 3 := by
  have he : ∀ i j, (rowGram H i j - if i = j then (n : ℤ) else 0) ^ 2 =
      rowGram H i j ^ 2 - if i = j then (n : ℤ) ^ 2 else 0 := by
    intro i j
    by_cases h : i = j
    · subst j; simp [rowGram_diagonal hH]
    · simp [h]
  unfold gramEnergy
  simp_rw [he]
  simp only [Finset.sum_sub_distrib]
  simp
  ring

/-- The cubic entry (HHᵀH) used in the exact flip formula. -/
def cubicEntry {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) (a b : Fin n) : ℤ :=
  ∑ j, rowGram H a j * H j b

theorem single_flip_energy_change {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ}
    (hH : IsSign H) (a b : Fin n) :
    gramEnergy (flipCell H a b) - gramEnergy H =
      8 * ((2 * (n : ℤ) - 1) - H a b * cubicEntry H a b) := by
  let G := rowGram H
  let G' := rowGram (flipCell H a b)
  let f := fun i j => G' i j ^ 2 - G i j ^ 2
  have hdH := rowGram_diagonal hH a
  have hdF := rowGram_diagonal (flipCell_isSign hH a b) a
  have hs : ∀ i j, f i j = f j i := by
    intro i j
    dsimp [f, G, G']
    rw [rowGram_symmetric H i j, rowGram_symmetric (flipCell H a b) i j]
  have hd : f a a = 0 := by dsimp [f, G, G']; rw [hdH, hdF]; ring
  have hz : ∀ i j, i ≠ a → j ≠ a → f i j = 0 := by
    intro i j hi hj
    dsimp [f, G, G']
    rw [rowGram_flip_unaffected H a b i j hi hj]
    ring
  have hstar := sum_symmetric_star f a hs hd hz
  have hsq := sign_square (hH a b)
  have hrow : ∀ j, f a j = 4 - 4 * H a b * (G a j * H j b) +
      (if j = a then 4 * ((n : ℤ) - 1) else 0) := by
    intro j
    by_cases hj : j = a
    · subst j
      rw [hd]
      dsimp [G]
      rw [hdH]
      simp only [ite_true]
      nlinarith [congrArg (fun x : ℤ => (n : ℤ) * x) hsq]
    · dsimp [f, G, G']
      rw [rowGram_flip_away H a b j hj]
      simp only [hj, ite_false, add_zero]
      have ht := sign_square (hH j b)
      calc
        _ = 4 * ((H a b) ^ 2 * (H j b) ^ 2) -
            4 * H a b * (rowGram H a j * H j b) := by ring
        _ = _ := by rw [hsq, ht]; ring
  have hsum : (∑ j, f a j) = 8 * (n : ℤ) - 4 - 4 * H a b * cubicEntry H a b := by
    simp_rw [hrow]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum]
    simp [cubicEntry, G]
    ring
  rw [gramEnergy_eq_gramSquares_sub (flipCell_isSign hH a b),
    gramEnergy_eq_gramSquares_sub hH]
  have he : (∑ i, ∑ j, G' i j ^ 2) - (∑ i, ∑ j, G i j ^ 2) =
      ∑ i, ∑ j, f i j := by simp [f, Finset.sum_sub_distrib]
  change (∑ i, ∑ j, G' i j ^ 2) - (n : ℤ) ^ 3 -
      ((∑ i, ∑ j, G i j ^ 2) - (n : ℤ) ^ 3) = _
  rw [sub_sub_sub_cancel_right]
  rw [he, hstar, hsum]
  ring

def columnGram {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) (b d : Fin n) : ℤ :=
  ∑ j, H j b * H j d

theorem rowGram_flip_center {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ}
    (hH : IsSign H) (a b j : Fin n) :
    rowGram (flipCell H a b) a j = rowGram H a j - 2 * H a b * H j b +
      if j = a then 2 else 0 := by
  by_cases hj : j = a
  · subst j
    rw [rowGram_diagonal (flipCell_isSign hH a b), rowGram_diagonal hH]
    simp only [ite_true]
    nlinarith [sign_square (hH a b)]
  · rw [rowGram_flip_away H a b j hj]; simp [hj]

theorem rowGram_flip_other {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ)
    (a b c j : Fin n) (hc : c ≠ a) :
    rowGram (flipCell H a b) c j = rowGram H c j +
      if j = a then -2 * H c b * H a b else 0 := by
  by_cases hj : j = a
  · subst j
    rw [rowGram_symmetric (flipCell H a b) c a, rowGram_flip_away H a b c hc]
    rw [rowGram_symmetric H a c]
    simp only [ite_true]
    ring
  · rw [rowGram_flip_unaffected H a b c j hc hj]; simp [hj]

theorem cubic_flip_same_row {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ}
    (hH : IsSign H) (a b d : Fin n) (hd : d ≠ b) :
    cubicEntry (flipCell H a b) a d = cubicEntry H a d -
      2 * H a b * columnGram H b d + 2 * H a d := by
  have he : ∀ j, rowGram (flipCell H a b) a j * flipCell H a b j d =
      rowGram H a j * H j d - 2 * H a b * (H j b * H j d) +
        if j = a then 2 * H a d else 0 := by
    intro j
    rw [rowGram_flip_center hH]
    simp only [flipCell, hd, and_false, ite_false]
    by_cases hj : j = a
    · subst j; simp; ring
    · simp [hj]; ring
  unfold cubicEntry
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  simp [columnGram]

theorem cubic_flip_distinct_row_column {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ)
    (a b c d : Fin n) (hc : c ≠ a) (hd : d ≠ b) :
    cubicEntry (flipCell H a b) c d = cubicEntry H c d -
      2 * H a b * H c b * H a d := by
  have he : ∀ j, rowGram (flipCell H a b) c j * flipCell H a b j d =
      rowGram H c j * H j d - if j = a then 2 * H a b * H c b * H a d else 0 := by
    intro j
    rw [rowGram_flip_other H a b c j hc]
    simp only [flipCell, hd, and_false, ite_false]
    by_cases hj : j = a
    · subst j; simp; ring
    · simp [hj]
  unfold cubicEntry
  simp_rw [he]
  simp [Finset.sum_sub_distrib]

theorem cubic_flip_same_column {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ}
    (hH : IsSign H) (a b c : Fin n) (hc : c ≠ a) :
    cubicEntry (flipCell H a b) c b = cubicEntry H c b -
      2 * H a b * rowGram H c a + 2 * H c b := by
  have he : ∀ j, rowGram (flipCell H a b) c j * flipCell H a b j b =
      rowGram H c j * H j b +
        if j = a then -2 * H a b * rowGram H c a + 2 * H c b else 0 := by
    intro j
    rw [rowGram_flip_other H a b c j hc]
    by_cases hj : j = a
    · subst j
      simp only [flipCell, and_self, ite_true, eq_self]
      nlinarith [congrArg (fun x : ℤ => H c b * x) (sign_square (hH a b))]
    · simp [flipCell, hj]
  unfold cubicEntry
  simp_rw [he]
  simp [Finset.sum_add_distrib]
  ring

theorem two_flip_same_row {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ}
    (hH : IsSign H) (a b d : Fin n) (hd : d ≠ b) :
    gramEnergy (flipCell (flipCell H a b) a d) - gramEnergy H =
      (gramEnergy (flipCell H a b) - gramEnergy H) +
      (gramEnergy (flipCell H a d) - gramEnergy H) +
      16 * (H a b * H a d * columnGram H b d - 1) := by
  have h1 := single_flip_energy_change hH a b
  have h2 := single_flip_energy_change (flipCell_isSign hH a b) a d
  have h3 := single_flip_energy_change hH a d
  rw [cubic_flip_same_row hH a b d hd] at h2
  simp only [flipCell, hd, and_false, ite_false] at h2
  nlinarith [sign_square (hH a d)]

theorem two_flip_same_column {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ}
    (hH : IsSign H) (a b c : Fin n) (hc : c ≠ a) :
    gramEnergy (flipCell (flipCell H a b) c b) - gramEnergy H =
      (gramEnergy (flipCell H a b) - gramEnergy H) +
      (gramEnergy (flipCell H c b) - gramEnergy H) +
      16 * (H a b * H c b * rowGram H a c - 1) := by
  have h1 := single_flip_energy_change hH a b
  have h2 := single_flip_energy_change (flipCell_isSign hH a b) c b
  have h3 := single_flip_energy_change hH c b
  rw [cubic_flip_same_column hH a b c hc, rowGram_symmetric H c a] at h2
  simp only [flipCell, hc, false_and, ite_false] at h2
  nlinarith [sign_square (hH c b)]

theorem two_flip_distinct_row_column {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ}
    (hH : IsSign H) (a b c d : Fin n) (hc : c ≠ a) (hd : d ≠ b) :
    gramEnergy (flipCell (flipCell H a b) c d) - gramEnergy H =
      (gramEnergy (flipCell H a b) - gramEnergy H) +
      (gramEnergy (flipCell H c d) - gramEnergy H) +
      16 * H a b * H a d * H c b * H c d := by
  have h1 := single_flip_energy_change hH a b
  have h2 := single_flip_energy_change (flipCell_isSign hH a b) c d
  have h3 := single_flip_energy_change hH c d
  rw [cubic_flip_distinct_row_column H a b c d hc hd] at h2
  simp only [flipCell, hc, false_and, ite_false] at h2
  nlinarith

theorem rowGram_even {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ}
    (hH : IsSign H) (hn : Even n) (i j : Fin n) : Even (rowGram H i j) := by
  let f := fun k => (H i k * H j k - 1) / 2
  have he : ∀ k, H i k * H j k = 1 + 2 * f k := by
    intro k
    rcases hH i k with hi | hi <;> rcases hH j k with hj | hj <;>
      norm_num [f, hi, hj]
  have hsum : rowGram H i j = (n : ℤ) + 2 * ∑ k, f k := by
    calc
      _ = ∑ k, (1 + 2 * f k) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact he k
      _ = _ := by simp [Finset.sum_add_distrib, Finset.mul_sum]
  obtain ⟨r, hr⟩ := hn
  have hcast : (n : ℤ) = (r : ℤ) + (r : ℤ) := by exact_mod_cast hr
  refine ⟨(r : ℤ) + ∑ k, f k, ?_⟩
  rw [hsum, hcast]
  ring

theorem even_integer_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℤ) (hf : ∀ i ∈ s, Even (f i)) :
    Even (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨x, hx⟩ := hf a (Finset.mem_insert_self a s)
      obtain ⟨y, hy⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      refine ⟨x + y, ?_⟩
      rw [Finset.sum_insert ha, hx, hy]
      ring

theorem cubicEntry_even {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ}
    (hH : IsSign H) (hn : Even n) (a b : Fin n) : Even (cubicEntry H a b) := by
  apply even_integer_sum
  intro j hj
  obtain ⟨r, hr⟩ := rowGram_even hH hn a j
  refine ⟨r * H j b, ?_⟩
  rw [hr]
  ring

/-- The exact parity assertion: every even-order one-entry change is eight
times an odd integer, hence no neutral one-entry move exists. -/
theorem single_flip_change_eight_times_odd {n : ℕ}
    {H : Matrix (Fin n) (Fin n) ℤ} (hH : IsSign H) (hn : Even n) (a b : Fin n) :
    ∃ q : ℤ, gramEnergy (flipCell H a b) - gramEnergy H = 8 * (2 * q + 1) := by
  obtain ⟨r, hr⟩ := cubicEntry_even hH hn a b
  refine ⟨(n : ℤ) - H a b * r - 1, ?_⟩
  rw [single_flip_energy_change hH, hr]
  ring

theorem single_flip_nonzero {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ}
    (hH : IsSign H) (hn : Even n) (a b : Fin n) :
    gramEnergy (flipCell H a b) ≠ gramEnergy H := by
  obtain ⟨q, hq⟩ := single_flip_change_eight_times_odd hH hn a b
  intro he
  rw [he] at hq
  omega

end PhaseGeometry
