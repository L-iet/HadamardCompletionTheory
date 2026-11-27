/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P03_06
@[expose] public section
namespace CompletionTheory

def pair24_03_10Rows : Fin 14 → Fin 16 := ![0, 1, 2, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15]
def pair24_03_10Free : Fin 10 → Fin 24 := ![13, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_03_10Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![-8, 14, 16, 6, -2, -10, -4, 14, 28, 6, 8, -2, 22, -16;
     -2, 8, 4, 0, 16, -4, 8, -10, -8, 0, -10, -8, -14, 20;
     -2, 8, 4, 12, -8, 8, 8, -10, -14, -6, -4, 16, -20, 8;
     13, -7, -8, -15, -11, 11, 2, 2, -8, 3, 17, -5, 4, 2;
     7, -1, 4, -9, 7, 5, -10, -10, -8, 9, -1, 1, 4, 2;
     -8, 14, 16, 6, -2, -10, -4, 14, 10, -12, -10, -2, 4, -16;
     4, 2, -8, -18, -14, -10, -16, 2, 16, 18, 20, -2, 10, -4;
     -20, 26, 4, 18, -2, 14, 8, -10, -8, -18, -28, 10, -14, 20;
     13, -7, -8, -3, 1, -13, 2, 2, 4, 15, 5, -17, 16, -10;
     4, 2, -8, 6, 10, 14, 20, 2, -14, -12, -22, 10, -20, 8;
     13, -7, -8, 9, 13, -1, 2, 2, -20, -9, -7, 7, -8, 14;
     22, -16, -8, -12, -8, -4, -16, 2, 22, 6, 32, -8, 16, -28;
     18, -18, 0, 6, 6, 6, 0, 0, -12, 6, -6, -6, -12, 12;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     18, -18, 0, -6, -6, -6, 0, 0, 12, -6, 6, 6, 12, -12;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def pair24_03_10Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![48, 72, -96, -48, 96, -72, 24, 96, 48, 96;
     -24, 0, 48, 24, -48, 72, 96, -48, 48, -48;
     -24, -72, 120, 24, 24, 72, 24, 24, -24, -48;
     12, -36, -24, 60, -48, -36, -84, -48, -60, 24;
     12, -36, -24, -12, -48, 36, -12, -48, 12, 24;
     -24, 72, -24, -48, 96, 0, 24, 96, 48, 24;
     120, 0, -96, 24, -48, -72, -48, 24, -24, 96;
     -24, 0, 192, 24, 96, 144, 96, 24, 48, -48;
     12, 36, -96, -12, -48, -108, -12, -48, 12, 24;
     -96, 0, 120, 24, 24, 72, 24, -48, -24, -120;
     -60, -36, 48, -12, -48, 36, -12, -48, 12, -120;
     48, 0, -168, -48, -48, -144, -120, 24, -96, 96;
     -72, -72, 0, 0, -72, 0, 0, -72, 0, -72;
     72, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, -72, -72, 0, -72, -72, 0, -72, 0;
     0, 72, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 72, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 72, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 72, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 72, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 72, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 72, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 72, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 72]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_03_10_certificate :
    pair24_03_10Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_03_10Rows id +
      pair24_03_10Inverse * integerInformationSelector pair24_03_10Free = (72 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_03_10_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_03_10Inverse.mulVec (fun t => if b t then 1 else -1) k = 72 ∨
      pair24_03_10Inverse.mulVec (fun t => if b t then 1 else -1) k = -72) →
    IntegerScaledHalfPattern 72 (1)
      (∑ k, encodedIntFrame base24Masks 3 k * pair24_03_10Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 10 k * pair24_03_10Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_03_10_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {3, 10} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 3 k * x k) (∑ k, base24Frame 10 k * x k) := by
  have h := order24_integer_pair_lift 3 10 pair24_03_10Rows pair24_03_10Free
    pair24_03_10Left pair24_03_10Inverse 72 (1) (by norm_num) (by decide +kernel)
    pair24_03_10_certificate pair24_03_10_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
