/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum

@[expose] public section
namespace PhaseGeometry

/-- The exact Gaussian-integer parity gap used by even-order phase rounding. -/
theorem even_gaussian_gap {a b : ℤ} (he : Even (a + b))
    (hsmall : a ^ 2 + b ^ 2 < 2) : a = 0 ∧ b = 0 := by
  obtain ⟨k, hk⟩ := he
  have ha2 : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg b]
  have hb2 : b ^ 2 ≤ 1 := by nlinarith [sq_nonneg a]
  have ha : -1 ≤ a ∧ a ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 1)]
  have hb : -1 ≤ b ∧ b ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (b - 1), sq_nonneg (b + 1)]
  rcases ha with ⟨halo, hahi⟩
  rcases hb with ⟨hblo, hbhi⟩
  interval_cases a <;> interval_cases b <;> norm_num at * <;> omega

/-- Without parity the Gaussian-integer gap is one. -/
theorem gaussian_gap {a b : ℤ} (hsmall : a ^ 2 + b ^ 2 < 1) :
    a = 0 ∧ b = 0 := by
  have ha2 : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
  have hb2 : b ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
  exact ⟨sq_eq_zero_iff.mp ha2, sq_eq_zero_iff.mp hb2⟩

/-- Exact arithmetic linking the averaged pivot error to the even-order
Gaussian-integrality threshold. Producing that averaged error is separate. -/
theorem even_rounding_error_threshold {n D η : ℝ} (hn : 0 < n)
    (hη : η ≤ D / (2 * n ^ 2)) (hD : D < 2 * n) :
    2 * n * η < 2 := by
  have hd : 0 < 2 * n ^ 2 := by positivity
  have hmul : η * (2 * n ^ 2) ≤ D := (le_div_iff₀ hd).mp hη
  have hbound : n * (2 * n * η) < n * 2 := by nlinarith
  by_contra h
  have hbad : 0 ≤ 2 * n * η - 2 := by linarith
  have hp := mul_nonneg (le_of_lt hn) hbad
  nlinarith

end PhaseGeometry
