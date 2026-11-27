/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P11_14
@[expose] public section
namespace CompletionTheory

def pair24_12_15Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14]
def pair24_12_15Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_12_15Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![0, 5, 12, 8, 5, 1, 1, 2, 1, 10, 4, 1, 5, 5;
     10, -5, 4, -4, -5, 7, -13, 4, -3, 10, -2, -3, -5, 5;
     -5, 10, 4, -4, 10, -8, 2, 4, -3, -5, -2, -3, 10, -10;
     -25, 30, -1, -4, 0, -8, 12, 9, 17, -5, -17, 2, -15, 5;
     15, -10, 3, 2, -10, 4, 4, -7, -11, -5, 1, 4, 5, 5;
     5, 0, 8, 2, 0, 4, -6, -12, -1, -5, 16, -1, 0, -10;
     20, -15, -4, 14, -15, -17, 3, 6, -7, 10, -8, -7, 15, 5;
     40, -35, -2, 2, -5, -11, -1, -2, -21, 10, 16, -21, 25, 5;
     5, 0, -7, 2, 0, 4, -6, 3, -1, -5, 1, 14, -15, 5;
     5, 0, -10, -10, 0, 10, 0, 0, 5, -5, 10, 5, 0, -10;
     -5, 10, -5, -10, 10, 10, -10, -5, 15, -5, -5, 0, -5, 5;
     -35, 40, -2, 2, 10, 4, 14, -2, 9, -5, -14, 9, -20, -10;
     -10, 10, 2, -12, 10, 6, -4, -8, 16, 0, -6, 16, -20, 0;
     40, -40, -2, 12, -10, -6, 4, 8, -16, 0, 6, -16, 20, 0;
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

def pair24_12_15Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-24, -12, -24, -24, 48, 12, 36, 24, 0, 24;
     -48, 36, -48, -48, -24, -36, 12, -12, 0, -12;
     12, -24, 72, 12, 36, 24, 12, 48, 0, -12;
     72, 96, 72, 132, 96, -6, 12, 18, 90, 78;
     -36, -48, -36, -36, -48, 18, -36, -54, -30, 6;
     24, -48, -36, -36, -48, 48, 24, 36, 0, -24;
     -132, -36, -12, -12, 24, -24, -72, -48, -120, 12;
     -156, -108, -36, -156, -48, -12, -96, -24, -180, -84;
     24, 12, -36, 24, -48, -42, 24, -54, 30, 6;
     60, 0, 0, 0, -60, 0, 0, 0, 0, -60;
     60, 60, 0, 0, 0, -30, 0, 30, 90, -30;
     144, 72, 84, 144, 72, 48, 84, 36, 120, 96;
     96, 48, -24, 36, -12, -48, 36, 24, 120, 24;
     -156, -108, -36, -96, -48, -12, -96, -84, -180, -84;
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
theorem pair24_12_15_certificate :
    pair24_12_15Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_12_15Rows id +
      pair24_12_15Inverse * integerInformationSelector pair24_12_15Free = (60 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_12_15_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_12_15Inverse.mulVec (fun t => if b t then 1 else -1) k = 60 ∨
      pair24_12_15Inverse.mulVec (fun t => if b t then 1 else -1) k = -60) →
    IntegerScaledHalfPattern 60 (1)
      (∑ k, encodedIntFrame base24Masks 12 k * pair24_12_15Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 15 k * pair24_12_15Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_12_15_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {12, 15} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 12 k * x k) (∑ k, base24Frame 15 k * x k) := by
  have h := order24_integer_pair_lift 12 15 pair24_12_15Rows pair24_12_15Free
    pair24_12_15Left pair24_12_15Inverse 60 (1) (by norm_num) (by decide +kernel)
    pair24_12_15_certificate pair24_12_15_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
