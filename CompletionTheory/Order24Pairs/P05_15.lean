/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P05_11
@[expose] public section
namespace CompletionTheory

def pair24_05_15Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14]
def pair24_05_15Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_05_15Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![3, -2, 2, 2, 0, 0, 0, -1, 2, 2, 0, 1, 2, 1;
     23, -22, -2, 2, -8, -4, -2, -9, 2, 8, -2, 7, 6, 1;
     -25, 26, 4, -4, 10, 2, 4, 9, -1, -10, 1, -8, -6, -2;
     -29, 30, 3, -4, 8, 4, 5, 13, -1, -13, 2, -8, -11, 1;
     15, -14, -1, 2, -6, 0, -3, -7, -1, 5, 0, 4, 5, 1;
     13, -12, 0, 2, -4, -2, -4, -5, -1, 8, -1, 4, 4, -2;
     -47, 48, 6, -4, 14, 4, 8, 19, 2, -22, 2, -17, -14, 1;
     -25, 26, 4, -4, 10, 2, 4, 9, 2, -10, -2, -11, -6, 1;
     13, -12, -3, 2, -4, -2, -1, -5, -1, 5, 2, 4, 1, 1;
     31, -30, -6, 2, -10, -2, -4, -11, -1, 14, -1, 10, 10, -2;
     29, -28, -5, 2, -8, -4, -5, -9, -1, 11, -2, 10, 9, 1;
     5, -4, -2, 2, -2, 2, -2, -3, -1, 2, 1, 4, 0, -2;
     16, -16, -2, 0, -4, -2, -4, -4, 0, 6, 2, 6, 2, 0;
     -10, 10, 2, 0, 4, 2, 4, 4, 0, -6, -2, -6, -2, 0;
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

def pair24_05_15Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-12, -12, -12, -12, 0, 0, 0, 0, -12, 0;
     -60, -60, -60, -60, -72, -24, -48, -36, -84, -36;
     60, 72, 72, 60, 84, 24, 60, 48, 96, 36;
     72, 96, 72, 84, 96, 18, 60, 42, 114, 54;
     -36, -48, -36, -36, -48, -6, -36, -30, -54, -18;
     -24, -48, -36, -36, -48, 0, -24, -12, -48, -24;
     96, 156, 120, 120, 168, 36, 108, 72, 180, 84;
     48, 84, 72, 48, 96, 24, 60, 48, 96, 36;
     -24, -36, -36, -24, -48, -18, -24, -30, -42, -18;
     -60, -96, -72, -72, -108, -24, -72, -48, -120, -60;
     -60, -84, -72, -72, -96, -30, -72, -42, -102, -54;
     0, -24, -12, 0, -24, 0, -12, -12, -24, 0;
     -24, -48, -48, -36, -60, -24, -36, -24, -48, -24;
     12, 36, 36, 24, 48, 12, 24, 12, 36, 12;
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
theorem pair24_05_15_certificate :
    pair24_05_15Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_05_15Rows id +
      pair24_05_15Inverse * integerInformationSelector pair24_05_15Free = (12 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_05_15_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_05_15Inverse.mulVec (fun t => if b t then 1 else -1) k = 12 ∨
      pair24_05_15Inverse.mulVec (fun t => if b t then 1 else -1) k = -12) →
    IntegerScaledHalfPattern 12 (1)
      (∑ k, encodedIntFrame base24Masks 5 k * pair24_05_15Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 15 k * pair24_05_15Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_05_15_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {5, 15} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 5 k * x k) (∑ k, base24Frame 15 k * x k) := by
  have h := order24_integer_pair_lift 5 15 pair24_05_15Rows pair24_05_15Free
    pair24_05_15Left pair24_05_15Inverse 12 (1) (by norm_num) (by decide +kernel)
    pair24_05_15_certificate pair24_05_15_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
