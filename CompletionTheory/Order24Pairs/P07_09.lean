/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P06_13
@[expose] public section
namespace CompletionTheory

def pair24_07_09Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 8, 10, 11, 12, 13, 14, 15]
def pair24_07_09Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_07_09Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![0, 2, 4, 4, 2, 2, 2, -2, 4, 2, 0, 2, -2, 4;
     10, -8, 0, 0, -4, 4, -4, -6, 4, 0, 2, 0, -2, 4;
     13, -11, 0, 0, -1, -5, -1, -6, 4, -3, 5, 9, -2, -2;
     20, -18, -4, 2, -10, -6, 2, -4, 4, -2, 10, 4, 4, -2;
     -12, 14, 4, -2, 2, 2, 2, 4, -8, 2, -6, -4, 4, -2;
     -31, 33, 8, -4, 11, 3, -1, 14, -8, 1, -11, -11, -2, -2;
     20, -18, -4, 8, -10, -6, 2, -10, 4, -2, 4, 10, -2, 4;
     4, -2, 0, 0, 2, -2, 2, -6, 4, -6, -4, 6, -2, 4;
     14, -12, -4, 2, -4, 0, -4, -4, 4, 4, 4, -2, 4, -2;
     5, -3, -4, -4, -1, 3, -1, 2, 4, 1, 1, 1, -2, -2;
     -14, 16, 0, -6, 8, 4, -4, 12, -8, 0, -4, -6, 4, -2;
     -17, 19, 0, 0, 5, 1, 5, 6, -8, 3, -1, -9, -2, -2;
     -28, 28, 4, -8, 12, 4, 0, 16, -12, 8, -8, -16, 0, 0;
     40, -40, -4, 8, -12, -4, 0, -16, 12, -8, 8, 16, 0, 0;
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

def pair24_07_09Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![0, -24, 0, 0, 0, 24, 24, 0, 0, 0;
     -24, -24, -24, -24, -48, 0, 0, -24, -24, -24;
     -36, -48, -12, -36, -24, -12, -36, 0, -60, -24;
     -48, -48, -48, -24, -48, -36, -72, -36, -84, -12;
     24, 48, 24, 24, 48, 12, 24, 12, 60, 36;
     84, 96, 60, 60, 96, 36, 84, 72, 132, 48;
     -72, -72, -24, -24, -48, 0, -48, -48, -96, -24;
     -24, -24, 24, -24, 0, 24, 0, 0, -24, -24;
     -24, -24, -48, -24, -48, -36, -24, -36, -36, -12;
     12, 0, -12, -12, -24, -12, -12, 0, -12, -24;
     48, 72, 24, 24, 48, -12, 24, 36, 84, 12;
     60, 48, 36, 60, 48, 12, 36, 24, 60, 48;
     96, 96, 48, 72, 72, 0, 72, 48, 144, 48;
     -120, -120, -72, -96, -96, -24, -96, -72, -168, -72;
     24, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 24, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 24, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 24, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 24, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 24, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 24, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 24, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 24, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 24]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_07_09_certificate :
    pair24_07_09Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_07_09Rows id +
      pair24_07_09Inverse * integerInformationSelector pair24_07_09Free = (24 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_07_09_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_07_09Inverse.mulVec (fun t => if b t then 1 else -1) k = 24 ∨
      pair24_07_09Inverse.mulVec (fun t => if b t then 1 else -1) k = -24) →
    IntegerScaledHalfPattern 24 (1)
      (∑ k, encodedIntFrame base24Masks 7 k * pair24_07_09Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 9 k * pair24_07_09Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_07_09_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {7, 9} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 7 k * x k) (∑ k, base24Frame 9 k * x k) := by
  have h := order24_integer_pair_lift 7 9 pair24_07_09Rows pair24_07_09Free
    pair24_07_09Left pair24_07_09Inverse 24 (1) (by norm_num) (by decide +kernel)
    pair24_07_09_certificate pair24_07_09_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
