/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import PhaseGeometry.FlipCalculus
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace PhaseGeometry

def trapRowGramTable : Matrix (Fin 8) (Fin 8) ℤ :=
  ![![8, 0, 2, 0, 0, 0, -2, -2],
    ![0, 8, 2, 0, 0, 0, 2, -2],
    ![2, 2, 8, -2, -2, -2, 0, 0],
    ![0, 0, -2, 8, 0, -4, 2, -2],
    ![0, 0, -2, 0, 8, 0, -2, -2],
    ![0, 0, -2, -4, 0, 8, 2, -2],
    ![-2, 2, 0, 2, -2, 2, 8, 0],
    ![-2, -2, 0, -2, -2, -2, 0, 8]]

def trapColumnGramTable : Matrix (Fin 8) (Fin 8) ℤ :=
  ![![8, 0, -4, 0, -2, 0, 0, 0],
    ![0, 8, 0, 0, 2, 4, 0, 0],
    ![-4, 0, 8, 0, -2, 0, 0, 0],
    ![0, 0, 0, 8, -2, 0, 0, -4],
    ![-2, 2, -2, -2, 8, -2, -2, -2],
    ![0, 4, 0, 0, -2, 8, 0, 0],
    ![0, 0, 0, 0, -2, 0, 8, 0],
    ![0, 0, 0, -4, -2, 0, 0, 8]]

def trapCostTable : Matrix (Fin 8) (Fin 8) ℤ :=
  ![![8, 40, 40, 72, 40, 8, 72, 72],
    ![40, 72, 8, 8, 40, 72, 72, 40],
    ![8, 72, 40, 40, 8, 72, 40, 8],
    ![40, 40, 8, 40, 40, 8, 40, 8],
    ![72, 8, 72, 40, 40, 40, 72, 8],
    ![8, 8, 40, 8, 40, 40, 40, 40],
    ![72, 40, 72, 8, 8, 8, 40, 40],
    ![40, 8, 8, 72, 8, 40, 40, 72]]

set_option maxRecDepth 100000 in
theorem trap8_row_gram_table : ∀ i j : Fin 8, rowGram trap8 i j = trapRowGramTable i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

set_option maxRecDepth 100000 in
theorem trap8_column_gram_table : ∀ i j : Fin 8, columnGram trap8 i j = trapColumnGramTable i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem trap8_cubic_cost_table : ∀ i j : Fin 8,
    8 * ((2 * (8 : ℤ) - 1) - trap8 i j * cubicEntry trap8 i j) = trapCostTable i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem trap8_isSign : IsSign trap8 := by
  intro i j
  unfold trap8 fromMasks
  split_ifs <;> simp

theorem trap8_single_cost : ∀ i j,
    gramEnergy (flipCell trap8 i j) - gramEnergy trap8 = trapCostTable i j := by
  intro i j
  rw [single_flip_energy_change trap8_isSign]
  exact trap8_cubic_cost_table i j

set_option maxRecDepth 100000 in
theorem trap8_cost_at_least_eight : ∀ i j : Fin 8, (8 : ℤ) ≤ trapCostTable i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

theorem trap8_every_one_flip_ge160 (a b : Fin 8) :
    160 ≤ gramEnergy (flipCell trap8 a b) := by
  have h := trap8_single_cost a b
  have hh := trap8_cost_at_least_eight a b
  rw [trap8_energy] at h
  omega

def trapPairInteraction (a b c d : Fin 8) : ℤ :=
  if c = a then 16 * (trap8 a b * trap8 a d * trapColumnGramTable b d - 1)
  else if d = b then 16 * (trap8 a b * trap8 c b * trapRowGramTable a c - 1)
  else 16 * trap8 a b * trap8 a d * trap8 c b * trap8 c d

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem trap8_pair_arithmetic_bound : ∀ a b c d : Fin 8,
    c ≠ a ∨ d ≠ b →
    0 ≤ trapCostTable a b + trapCostTable c d + trapPairInteraction a b c d := by decide

theorem flipCell_involutive {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) (a b : Fin n) :
    flipCell (flipCell H a b) a b = H := by
  funext i j
  by_cases h : i = a ∧ j = b <;> simp [flipCell, h]

/-- Every actual pair of flips has nonnegative energy change. The large
matrix computation is replaced by the proved universal flip calculus and
a small exact table certificate, all checked by the kernel. -/
theorem trap8_every_two_flips_nonnegative : ∀ a b c d : Fin 8,
    152 ≤ gramEnergy (flipCell (flipCell trap8 a b) c d) := by
  intro a b c d
  by_cases hc : c = a
  · subst c
    by_cases hd : d = b
    · subst d; rw [flipCell_involutive, trap8_energy]
    · have he := two_flip_same_row trap8_isSign a b d hd
      rw [trap8_single_cost, trap8_single_cost, trap8_column_gram_table] at he
      have hb := trap8_pair_arithmetic_bound a b a d (Or.inr hd)
      simp only [trapPairInteraction, ite_true] at hb
      rw [trap8_energy] at he
      omega
  · by_cases hd : d = b
    · subst d
      have he := two_flip_same_column trap8_isSign a b c hc
      rw [trap8_single_cost, trap8_single_cost, trap8_row_gram_table] at he
      have hb := trap8_pair_arithmetic_bound a b c b (Or.inl hc)
      simp only [trapPairInteraction, hc, ite_false, ite_true] at hb
      rw [trap8_energy] at he
      omega
    · have he := two_flip_distinct_row_column trap8_isSign a b c d hc hd
      rw [trap8_single_cost, trap8_single_cost] at he
      have hb := trap8_pair_arithmetic_bound a b c d (Or.inl hc)
      simp only [trapPairInteraction, hc, hd, ite_false] at hb
      rw [trap8_energy] at he
      omega

end PhaseGeometry

