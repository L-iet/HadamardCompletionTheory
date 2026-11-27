/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P01_09
@[expose] public section
namespace CompletionTheory

def pair24_01_13Rows : Fin 14 → Fin 16 := ![0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15]
def pair24_01_13Free : Fin 10 → Fin 24 := ![13, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_01_13Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![4, 8, 0, 0, 0, -8, -8, 4, 16, 8, 8, 12, 12, -8;
     4, 0, 8, 0, 16, 8, 8, -20, -24, 8, 0, -12, -28, 32;
     4, 4, -20, 0, -16, -24, -12, 16, 32, -4, 4, 24, 28, -36;
     4, -5, 7, -6, -4, 18, 9, -5, -19, -1, -2, 0, -11, 15;
     4, 3, -1, -6, 4, 2, -7, -5, -3, -1, 6, 0, 5, -1;
     4, 8, 0, 0, 0, -8, -8, 4, 4, 8, -4, 0, 0, -8;
     4, -6, 2, -12, -8, -4, -10, -2, 6, 2, 12, 12, 2, 2;
     4, 0, -16, 0, -8, -16, -16, 4, 24, 8, 0, 12, 20, -16;
     4, -7, 21, 6, 12, 22, 19, -23, -41, 5, 2, -24, -33, 37;
     4, -4, -12, 0, 0, -8, 4, 16, 16, -4, -4, 0, 12, -20;
     4, -3, -7, 6, 4, -10, -1, 13, 3, -7, -6, 0, 11, -7;
     4, -4, 12, 0, 0, 16, 4, -8, -8, -4, -4, 0, -12, 4;
     0, 2, 10, 12, 8, 20, 14, -6, -26, -6, -4, -24, -26, 26;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 4, -4, 0, -8, -8, 4, 12, 20, -12, -8, 0, 20, -20;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def pair24_01_13Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![48, 0, -96, -48, 0, -48, 0, 48, 0, 48;
     -48, -96, 96, 48, -96, 144, 96, -96, 0, -96;
     96, 96, -144, -96, 48, -192, -96, 144, 0, 96;
     -36, -60, 72, 84, -24, 60, -12, -72, -36, -24;
     12, -12, -24, -12, -24, 12, -12, -24, 12, 24;
     0, 0, -48, -48, 0, 0, 0, 48, 0, 0;
     72, -24, -48, 24, -48, -24, -24, 0, -24, 48;
     96, 48, -96, -96, 0, -96, -48, 96, 0, 48;
     -108, -132, 168, 108, -72, 180, 108, -168, -12, -120;
     0, 96, -48, -48, 48, -96, -48, 48, 0, 0;
     -12, 60, -24, -36, 24, -60, -36, 24, 36, -24;
     -48, -48, 48, 48, 0, 48, 0, -48, -48, 0;
     -120, -72, 144, 72, 0, 120, 72, -96, 24, -96;
     48, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 96, -48, -48, 96, -96, -48, 48, 0, 48;
     0, 48, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 48, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 48, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 48, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 48, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 48, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 48, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 48, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 48]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_01_13_certificate :
    pair24_01_13Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_01_13Rows id +
      pair24_01_13Inverse * integerInformationSelector pair24_01_13Free = (48 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_01_13_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_01_13Inverse.mulVec (fun t => if b t then 1 else -1) k = 48 ∨
      pair24_01_13Inverse.mulVec (fun t => if b t then 1 else -1) k = -48) →
    IntegerScaledHalfPattern 48 (-1)
      (∑ k, encodedIntFrame base24Masks 1 k * pair24_01_13Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 13 k * pair24_01_13Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_01_13_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {1, 13} x →
    HalfCorrelationPattern 24 (rationalRealCast (-1))
      (∑ k, base24Frame 1 k * x k) (∑ k, base24Frame 13 k * x k) := by
  have h := order24_integer_pair_lift 1 13 pair24_01_13Rows pair24_01_13Free
    pair24_01_13Left pair24_01_13Inverse 48 (-1) (by norm_num) (by decide +kernel)
    pair24_01_13_certificate pair24_01_13_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
