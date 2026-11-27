/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Tactic.Ring

@[expose] public section
namespace PhaseGeometry

open scoped BigOperators

/-- Integer sign matrix specified by the paper's negative-entry masks. -/
def fromMasks {n : ℕ} (masks : Fin n → ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if (masks i).testBit j.val then -1 else 1

def rowGram {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) : ℤ :=
  ∑ k, H i k * H j k

/-- Squared Frobenius row-Gram defect, with the diagonal included. -/
def gramEnergy {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) : ℤ :=
  ∑ i, ∑ j, (rowGram H i j - if i = j then (n : ℤ) else 0) ^ 2

def flipCell {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) (a b : Fin n) :
    Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if i = a ∧ j = b then - H i j else H i j

theorem gramEnergy_nonnegative {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) :
    0 ≤ gramEnergy H := by
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact sq_nonneg _

/-- Zero Gram energy is exactly orthogonality, with no sign assumption. -/
theorem gramEnergy_eq_zero_iff {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) :
    gramEnergy H = 0 ↔ ∀ i j,
      rowGram H i j = if i = j then (n : ℤ) else 0 := by
  constructor
  · intro h i j
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg (fun j _ =>
        sq_nonneg (rowGram H i j - if i = j then (n : ℤ) else 0)))).mp h i
        (Finset.mem_univ i)
    have hij := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      sq_nonneg (rowGram H i j - if i = j then (n : ℤ) else 0))).mp hi j
        (Finset.mem_univ j)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hij)
  · intro h
    simp [gramEnergy, h]

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
theorem rowGram_flip_away {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ)
    (a b j : Fin n) (hj : j ≠ a) :
    rowGram (flipCell H a b) a j =
      rowGram H a j - 2 * H a b * H j b := by
  simp only [rowGram, flipCell, true_and, false_and, ite_false, hj, eq_self]
  exact sum_flip_product (H a) (H j) b

def trap8 : Matrix (Fin 8) (Fin 8) ℤ :=
  fromMasks ![84, 44, 30, 230, 133, 73, 111, 51]

def repaired8 : Matrix (Fin 8) (Fin 8) ℤ :=
  fromMasks ![84, 44, 31, 2, 133, 73, 103, 49]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem trap8_energy : gramEnergy trap8 = 152 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem repaired8_gram : ∀ i j, rowGram repaired8 i j =
    if i = j then (8 : ℤ) else 0 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem trap8_three_flip_escape :
    gramEnergy (flipCell (flipCell (flipCell trap8 0 0) 0 5) 7 4) = 128 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem trap8_escape_barrier_witness :
    gramEnergy (flipCell trap8 0 0) = 160 ∧
    gramEnergy (flipCell (flipCell trap8 0 0) 0 5) = 152 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem trap8_every_one_flip_raises : ∀ a b : Fin 8,
    152 < gramEnergy (flipCell trap8 a b) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem trap8_four_row_repair_energies :
    gramEnergy (fromMasks ![84, 44, 30, 2, 133, 73, 111, 51]) = 120 ∧
    gramEnergy (fromMasks ![84, 44, 31, 2, 133, 73, 111, 51]) = 96 ∧
    gramEnergy (fromMasks ![84, 44, 31, 2, 133, 73, 103, 51]) = 56 ∧
    gramEnergy repaired8 = 0 := by decide

end PhaseGeometry
