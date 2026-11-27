/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P08_14
@[expose] public section
namespace CompletionTheory

def pair24_09_12Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 13, 14, 15]
def pair24_09_12Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_09_12Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![0, 5, 10, 10, 5, 5, 5, 0, -5, 10, 5, 5, -5, 10;
     10, -5, 2, -2, -5, 11, -9, 2, -9, 4, 1, -5, -5, 10;
     -5, 10, 5, -5, 10, -10, 0, 5, 0, -5, -5, 10, -5, -5;
     -25, 30, 0, -5, 0, -10, 10, 10, 20, -20, 0, -15, 10, -5;
     15, -10, 4, 1, -10, 2, 2, -6, -8, -2, 2, 5, 10, -5;
     5, 0, 9, 1, 0, 2, -8, -11, 2, 13, -3, 0, -5, -5;
     20, -15, -6, 16, -15, -13, 7, 4, -13, -2, -3, 15, -5, 10;
     40, -35, -4, 4, -5, -7, 3, -4, -27, 22, -17, 25, -5, 10;
     5, 0, -6, 1, 0, 2, -8, 4, 2, -2, 12, -15, 10, -5;
     5, 0, -9, -11, 0, 8, -2, 1, 8, 7, 3, 0, -5, -5;
     -5, 10, -4, -11, 10, 8, -12, -4, 18, -8, -2, -5, 10, -5;
     -35, 40, -1, 1, 10, 2, 12, -1, 12, -17, 7, -20, -5, -5;
     -10, 10, 2, -12, 10, 6, -4, -8, 16, -6, 16, -20, 0, 0;
     40, -40, -2, 12, -10, -6, 4, 8, -16, 6, -16, 20, 0, 0;
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

def pair24_09_12Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![0, -60, 0, 0, 0, 60, 60, 0, 0, 0;
     -24, -12, -24, -24, -72, 12, 36, -36, 0, -36;
     0, 0, 60, 0, 60, 0, 0, 60, 0, 0;
     60, 120, 60, 120, 120, -30, 0, 30, 90, 90;
     -48, -24, -48, -48, -24, -6, -48, -42, -30, 18;
     12, -24, -48, -48, -24, 24, 12, 48, 0, -12;
     -108, -84, 12, 12, -24, 24, -48, -72, -120, -12;
     -132, -156, -12, -132, -96, 36, -72, -48, -180, -108;
     12, 36, -48, 12, -24, -66, 12, -42, 30, 18;
     48, 24, -12, -12, -36, -24, -12, 12, 0, -48;
     48, 84, -12, -12, 24, -54, -12, 42, 90, -18;
     132, 96, 72, 132, 96, 24, 72, 48, 120, 108;
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
theorem pair24_09_12_certificate :
    pair24_09_12Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_09_12Rows id +
      pair24_09_12Inverse * integerInformationSelector pair24_09_12Free = (60 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_09_12_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_09_12Inverse.mulVec (fun t => if b t then 1 else -1) k = 60 ∨
      pair24_09_12Inverse.mulVec (fun t => if b t then 1 else -1) k = -60) →
    IntegerScaledHalfPattern 60 (1)
      (∑ k, encodedIntFrame base24Masks 9 k * pair24_09_12Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 12 k * pair24_09_12Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_09_12_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {9, 12} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 9 k * x k) (∑ k, base24Frame 12 k * x k) := by
  have h := order24_integer_pair_lift 9 12 pair24_09_12Rows pair24_09_12Free
    pair24_09_12Left pair24_09_12Inverse 60 (1) (by norm_num) (by decide +kernel)
    pair24_09_12_certificate pair24_09_12_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
