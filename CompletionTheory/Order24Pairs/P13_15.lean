/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P12_13
@[expose] public section
namespace CompletionTheory

def pair24_13_15Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14]
def pair24_13_15Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_13_15Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![-15, 20, 14, 6, 10, 2, 2, 4, 7, 10, -2, 2, -5, 5;
     25, -20, 2, -2, -10, 6, -14, 2, -9, 10, 4, -4, 5, 5;
     -35, 40, 8, -8, 20, -6, 4, 8, 9, -5, -14, -1, -10, -10;
     20, -15, -7, 2, -15, -11, 9, 3, -1, -5, 1, -1, 15, 5;
     0, 5, 5, 0, -5, 5, 5, -5, -5, -5, -5, 5, -5, 5;
     5, 0, 8, 2, 0, 4, -6, -12, -1, -5, 16, -1, 0, -10;
     -25, 30, 2, 8, 0, -14, 6, 12, 11, 10, -26, -4, -15, 5;
     -35, 40, 8, -8, 20, -6, 4, 8, 9, 10, -14, -16, -25, 5;
     50, -45, -13, 8, -15, 1, -9, -3, -19, -5, 19, 11, 15, 5;
     5, 0, -10, -10, 0, 10, 0, 0, 5, -5, 10, 5, 0, -10;
     10, -5, -7, -8, 5, 9, -11, -7, 9, -5, 1, -1, 5, 5;
     25, -20, -10, 10, -10, 0, 10, -10, -15, -5, 10, 5, 20, -10;
     50, -50, -6, -4, -10, 2, -8, -16, -8, 0, 18, 12, 20, 0;
     -20, 20, 6, 4, 10, -2, 8, 16, 8, 0, -18, -12, -20, 0;
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

def pair24_13_15Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![12, 36, 12, 12, 96, 24, 72, 48, 60, 48;
     -84, -12, -84, -84, -72, -48, -24, -36, -60, -36;
     84, 72, 144, 84, 132, 48, 84, 96, 120, 36;
     -36, -48, -36, 24, -48, -42, -96, -54, -90, 6;
     0, 0, 0, 0, 0, 30, 0, -30, 30, 30;
     24, -48, -36, -36, -48, 48, 24, 36, 0, -24;
     -24, 108, 96, 96, 168, 12, 36, 24, 60, 84;
     24, 132, 144, 24, 192, 48, 84, 96, 120, 36;
     -84, -132, -144, -84, -192, -78, -84, -126, -150, -66;
     60, 0, 0, 0, -60, 0, 0, 0, 0, -60;
     24, 12, -36, -36, -48, -42, -36, 6, 30, -54;
     0, -120, -60, 0, -120, 0, -60, -60, -120, 0;
     -48, -144, -168, -108, -204, -96, -108, -72, -120, -72;
     -12, 84, 108, 48, 144, 36, 48, 12, 60, 12;
     60, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 60, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 60, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 60, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 60, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 60, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 60, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 60, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 60, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 60]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_13_15_certificate :
    pair24_13_15Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_13_15Rows id +
      pair24_13_15Inverse * integerInformationSelector pair24_13_15Free = (60 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_13_15_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_13_15Inverse.mulVec (fun t => if b t then 1 else -1) k = 60 ∨
      pair24_13_15Inverse.mulVec (fun t => if b t then 1 else -1) k = -60) →
    IntegerScaledHalfPattern 60 (1)
      (∑ k, encodedIntFrame base24Masks 13 k * pair24_13_15Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 15 k * pair24_13_15Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_13_15_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {13, 15} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 13 k * x k) (∑ k, base24Frame 15 k * x k) := by
  have h := order24_integer_pair_lift 13 15 pair24_13_15Rows pair24_13_15Free
    pair24_13_15Left pair24_13_15Inverse 60 (1) (by norm_num) (by decide +kernel)
    pair24_13_15_certificate pair24_13_15_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
