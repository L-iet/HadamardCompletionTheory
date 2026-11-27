module

public import PhaseGeometry.TrapCertificate
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix

/-! # Exact flip calculus on arbitrary finite square index types -/

@[expose] public section
namespace PhaseGeometry.Indexed

def rowGram {ι : Type*} [Fintype ι] (H : Matrix ι ι ℤ) (i j : ι) : ℤ :=
  ∑ k, H i k * H j k

def gramEnergy {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℤ) : ℤ :=
  ∑ i, ∑ j, (rowGram H i j - if i = j then (Fintype.card ι : ℤ) else 0) ^ 2

def flipCell {ι : Type*} [DecidableEq ι] (H : Matrix ι ι ℤ) (a b : ι) : Matrix ι ι ℤ :=
  fun i j => if i = a ∧ j = b then -H i j else H i j

def IsSign {ι : Type*} (H : Matrix ι ι ℤ) : Prop := ∀ i j, H i j = 1 ∨ H i j = -1

theorem sum_flip_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : ι → ℤ) (b : ι) :
    (∑ k, (if k = b then - f k else f k) * g k) =
      (∑ k, f k * g k) - 2 * f b * g b := by
  calc
    _ = ∑ k, (f k * g k - if k = b then 2 * f b * g b else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      split_ifs with h
      · subst k; ring
      · ring
    _ = _ := by rw [Finset.sum_sub_distrib]; simp

/-- The actual row-correlation update used by the entry-flip calculus. -/

theorem rowGram_flip_away {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℤ)
    (a b j : ι) (hj : j ≠ a) :
    rowGram (flipCell H a b) a j =
      rowGram H a j - 2 * H a b * H j b := by
  simp only [rowGram, flipCell, true_and, false_and, ite_false, hj, eq_self]
  exact sum_flip_product (H a) (H j) b

theorem sign_square {z : ℤ} (hz : z = 1 ∨ z = -1) : z ^ 2 = 1 := by
  rcases hz with rfl | rfl <;> norm_num

theorem flipCell_isSign {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℤ}
    (hH : IsSign H) (a b : ι) : IsSign (flipCell H a b) := by
  intro i j
  simp only [flipCell]
  split_ifs
  · rcases hH i j with h | h <;> simp [h]
  · exact hH i j

theorem rowGram_symmetric {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℤ) (i j : ι) :
    rowGram H i j = rowGram H j i := by
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem rowGram_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℤ}
    (hH : IsSign H) (i : ι) : rowGram H i i = (Fintype.card ι) := by
  unfold rowGram
  have h : ∀ k, H i k * H i k = 1 := by
    intro k
    nlinarith [sign_square (hH i k)]
  simp [h]

theorem rowGram_flip_unaffected {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℤ)
    (a b i j : ι) (hi : i ≠ a) (hj : j ≠ a) :
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

theorem gramEnergy_eq_gramSquares_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℤ} (hH : IsSign H) :
    gramEnergy H = (∑ i, ∑ j, rowGram H i j ^ 2) - ((Fintype.card ι) : ℤ) ^ 3 := by
  have he : ∀ i j, (rowGram H i j - if i = j then ((Fintype.card ι) : ℤ) else 0) ^ 2 =
      rowGram H i j ^ 2 - if i = j then ((Fintype.card ι) : ℤ) ^ 2 else 0 := by
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
def cubicEntry {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℤ) (a b : ι) : ℤ :=
  ∑ j, rowGram H a j * H j b

theorem single_flip_energy_change {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℤ}
    (hH : IsSign H) (a b : ι) :
    gramEnergy (flipCell H a b) - gramEnergy H =
      8 * ((2 * ((Fintype.card ι) : ℤ) - 1) - H a b * cubicEntry H a b) := by
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
      (if j = a then 4 * (((Fintype.card ι) : ℤ) - 1) else 0) := by
    intro j
    by_cases hj : j = a
    · subst j
      rw [hd]
      dsimp [G]
      rw [hdH]
      simp only [ite_true]
      nlinarith [congrArg (fun x : ℤ => ((Fintype.card ι) : ℤ) * x) hsq]
    · dsimp [f, G, G']
      rw [rowGram_flip_away H a b j hj]
      simp only [hj, ite_false, add_zero]
      have ht := sign_square (hH j b)
      calc
        _ = 4 * ((H a b) ^ 2 * (H j b) ^ 2) -
            4 * H a b * (rowGram H a j * H j b) := by ring
        _ = _ := by rw [hsq, ht]; ring
  have hsum : (∑ j, f a j) = 8 * ((Fintype.card ι) : ℤ) - 4 - 4 * H a b * cubicEntry H a b := by
    simp_rw [hrow]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum]
    simp [cubicEntry, G]
    ring
  rw [gramEnergy_eq_gramSquares_sub (flipCell_isSign hH a b),
    gramEnergy_eq_gramSquares_sub hH]
  have he : (∑ i, ∑ j, G' i j ^ 2) - (∑ i, ∑ j, G i j ^ 2) =
      ∑ i, ∑ j, f i j := by simp [f, Finset.sum_sub_distrib]
  change (∑ i, ∑ j, G' i j ^ 2) - ((Fintype.card ι) : ℤ) ^ 3 -
      ((∑ i, ∑ j, G i j ^ 2) - ((Fintype.card ι) : ℤ) ^ 3) = _
  rw [sub_sub_sub_cancel_right]
  rw [he, hstar, hsum]
  ring

def columnGram {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℤ) (b d : ι) : ℤ :=
  ∑ j, H j b * H j d

theorem rowGram_flip_center {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℤ}
    (hH : IsSign H) (a b j : ι) :
    rowGram (flipCell H a b) a j = rowGram H a j - 2 * H a b * H j b +
      if j = a then 2 else 0 := by
  by_cases hj : j = a
  · subst j
    rw [rowGram_diagonal (flipCell_isSign hH a b), rowGram_diagonal hH]
    simp only [ite_true]
    nlinarith [sign_square (hH a b)]
  · rw [rowGram_flip_away H a b j hj]; simp [hj]

theorem rowGram_flip_other {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℤ)
    (a b c j : ι) (hc : c ≠ a) :
    rowGram (flipCell H a b) c j = rowGram H c j +
      if j = a then -2 * H c b * H a b else 0 := by
  by_cases hj : j = a
  · subst j
    rw [rowGram_symmetric (flipCell H a b) c a, rowGram_flip_away H a b c hc]
    rw [rowGram_symmetric H a c]
    simp only [ite_true]
    ring
  · rw [rowGram_flip_unaffected H a b c j hc hj]; simp [hj]

theorem cubic_flip_same_row {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℤ}
    (hH : IsSign H) (a b d : ι) (hd : d ≠ b) :
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

theorem cubic_flip_distinct_row_column {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℤ)
    (a b c d : ι) (hc : c ≠ a) (hd : d ≠ b) :
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

theorem cubic_flip_same_column {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℤ}
    (hH : IsSign H) (a b c : ι) (hc : c ≠ a) :
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

theorem two_flip_same_row {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℤ}
    (hH : IsSign H) (a b d : ι) (hd : d ≠ b) :
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

theorem two_flip_same_column {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℤ}
    (hH : IsSign H) (a b c : ι) (hc : c ≠ a) :
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

theorem two_flip_distinct_row_column {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℤ}
    (hH : IsSign H) (a b c d : ι) (hc : c ≠ a) (hd : d ≠ b) :
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


end PhaseGeometry.Indexed
