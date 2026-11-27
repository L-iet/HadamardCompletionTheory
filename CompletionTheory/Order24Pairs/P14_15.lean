/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P12_14
@[expose] public section
namespace CompletionTheory

def pair24_14_15Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
def pair24_14_15Free : Fin 10 → Fin 24 := ![11, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_14_15Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![3, 6, 10, 14, 4, 2, 8, -2, -3, 9, 6, 5, 8, 2;
     3, 6, 2, -2, -4, 10, -8, 2, -3, 9, -6, 1, 4, -14;
     -30, 30, 16, -16, 22, -10, -10, 16, 12, 0, -12, -10, -22, 14;
     21, -12, -12, 6, -18, -12, 18, 0, -3, -9, 0, 3, 24, -6;
     15, -6, 0, 6, -12, 6, 12, -12, -15, -9, 0, 9, 6, 0;
     -12, 12, 20, -8, 8, 4, -20, -4, 12, 0, 12, -8, -20, 4;
     -27, 36, -2, 14, -2, -16, 14, 10, 9, 9, -30, -1, -10, -4;
     -15, 24, 2, -2, 14, -8, 10, 2, -3, 9, -6, -17, -14, 4;
     33, -24, -16, 10, -10, 4, -2, -4, -15, -9, 12, 19, 16, -14;
     6, -6, -4, -20, 2, 10, -14, 8, 12, 0, 12, -2, -14, 10;
     39, -30, -16, -2, -4, 10, -8, -16, -3, -9, 12, 1, 22, 4;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     36, -36, -4, -8, -4, 4, -8, -16, 0, 0, 12, 16, 16, -8;
     -30, 30, 8, 4, 14, -2, 10, 20, 12, 0, -24, -14, -26, -2;
     30, -30, -4, 4, -10, -2, -2, -4, -12, 0, 12, -2, 10, 10;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def pair24_14_15Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-36, -48, -36, 0, 24, 24, 36, 12, -24, 48;
     -36, 48, -36, 0, -24, -24, 36, -12, 24, 24;
     72, 96, 144, 0, 168, 24, 72, 120, 120, -24;
     -36, -72, -36, 72, -72, -36, -108, -72, -108, 36;
     -36, -72, -36, 0, -72, 36, -36, -72, -36, 36;
     72, 48, 0, -72, 48, 48, 72, 96, 96, -48;
     -36, 96, 108, 144, 168, 24, 36, 12, 48, 120;
     -36, 48, 108, 0, 120, 48, 36, 60, 24, 24;
     -36, -96, -108, 0, -168, -60, -36, -120, -84, -12;
     72, 48, 0, -72, -24, -24, 0, 24, 24, -120;
     -36, -96, -108, -72, -168, -60, -108, -48, -84, -84;
     72, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, -96, -144, -72, -168, -96, -72, -48, -48, -48;
     0, 120, 144, 72, 192, 48, 72, 24, 96, 24;
     0, -96, -72, -72, -96, -24, -72, -48, -120, -48;
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
theorem pair24_14_15_certificate :
    pair24_14_15Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_14_15Rows id +
      pair24_14_15Inverse * integerInformationSelector pair24_14_15Free = (72 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_14_15_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_14_15Inverse.mulVec (fun t => if b t then 1 else -1) k = 72 ∨
      pair24_14_15Inverse.mulVec (fun t => if b t then 1 else -1) k = -72) →
    IntegerScaledHalfPattern 72 (1)
      (∑ k, encodedIntFrame base24Masks 14 k * pair24_14_15Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 15 k * pair24_14_15Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_14_15_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {14, 15} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 14 k * x k) (∑ k, base24Frame 15 k * x k) := by
  have h := order24_integer_pair_lift 14 15 pair24_14_15Rows pair24_14_15Free
    pair24_14_15Left pair24_14_15Inverse 72 (1) (by norm_num) (by decide +kernel)
    pair24_14_15_certificate pair24_14_15_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
