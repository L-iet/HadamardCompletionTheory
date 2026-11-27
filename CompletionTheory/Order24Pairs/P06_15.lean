/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P06_11
@[expose] public section
namespace CompletionTheory

def pair24_06_15Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14]
def pair24_06_15Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_06_15Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![3, -2, 2, 2, 0, 0, 0, -1, 2, 2, 0, 1, 2, 1;
     -37, 38, 6, -6, 12, 4, 6, 15, 2, -16, 2, -13, -14, 1;
     5, -4, 0, 0, 0, -2, 0, -3, -1, 2, -1, 2, 4, -2;
     31, -30, -5, 4, -12, -4, -3, -11, -1, 11, -2, 12, 9, 1;
     15, -14, -1, 2, -6, 0, -3, -7, -1, 5, 0, 4, 5, 1;
     -17, 18, 4, -2, 6, 2, 0, 7, -1, -4, 1, -6, -6, -2;
     13, -12, -2, 4, -6, -4, 0, -5, 2, 2, -2, 3, 6, 1;
     5, -4, 0, 0, 0, -2, 0, -3, 2, 2, -4, -1, 4, 1;
     -17, 18, 1, -2, 6, 2, 3, 7, -1, -7, 4, -6, -9, 1;
     1, 0, -2, -2, 0, 2, 0, 1, -1, 2, 1, 0, 0, -2;
     -31, 32, 3, -6, 12, 4, 3, 15, -1, -13, 2, -10, -11, 1;
     35, -34, -6, 6, -12, -2, -6, -15, -1, 14, -1, 14, 10, -2;
     -14, 14, 2, -4, 6, 2, 0, 8, 0, -6, 4, -4, -8, 0;
     20, -20, -2, 4, -6, -2, 0, -8, 0, 6, -4, 4, 8, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def pair24_06_15Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-12, -12, -12, -12, 0, 0, 0, 0, -12, 0;
     84, 132, 84, 84, 120, 24, 96, 60, 156, 60;
     -12, -24, 0, -12, -12, 0, -12, 0, -24, -12;
     -72, -96, -72, -60, -96, -30, -84, -54, -126, -42;
     -36, -48, -36, -36, -48, -6, -36, -30, -54, -18;
     48, 48, 36, 36, 48, 24, 48, 36, 72, 24;
     -48, -36, -24, -24, -24, -12, -36, -24, -60, -12;
     -24, -12, 0, -24, 0, 0, -12, 0, -24, -12;
     48, 60, 36, 48, 48, 6, 48, 18, 78, 30;
     12, 0, 0, 0, -12, 0, 0, 0, 0, -12;
     84, 108, 72, 72, 96, 18, 72, 54, 138, 42;
     -72, -120, -84, -72, -120, -24, -84, -60, -144, -48;
     48, 48, 24, 36, 36, 0, 36, 24, 72, 24;
     -60, -60, -36, -48, -48, -12, -48, -36, -84, -36;
     12, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 12, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 12, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 12, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 12, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 12, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 12, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 12, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 12, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 12]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_06_15_certificate :
    pair24_06_15Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_06_15Rows id +
      pair24_06_15Inverse * integerInformationSelector pair24_06_15Free = (12 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_06_15_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_06_15Inverse.mulVec (fun t => if b t then 1 else -1) k = 12 ∨
      pair24_06_15Inverse.mulVec (fun t => if b t then 1 else -1) k = -12) →
    IntegerScaledHalfPattern 12 (1)
      (∑ k, encodedIntFrame base24Masks 6 k * pair24_06_15Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 15 k * pair24_06_15Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_06_15_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {6, 15} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 6 k * x k) (∑ k, base24Frame 15 k * x k) := by
  have h := order24_integer_pair_lift 6 15 pair24_06_15Rows pair24_06_15Free
    pair24_06_15Left pair24_06_15Inverse 12 (1) (by norm_num) (by decide +kernel)
    pair24_06_15_certificate pair24_06_15_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
