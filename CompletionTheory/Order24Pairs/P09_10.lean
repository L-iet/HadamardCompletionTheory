/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P08_12
@[expose] public section
namespace CompletionTheory

def pair24_09_10Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 12, 13, 14, 15]
def pair24_09_10Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_09_10Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![-30, 36, 16, 8, 16, 8, 8, 4, 6, 8, -10, -4, -6, 12;
     0, 6, 4, -4, -2, 14, -10, 4, -6, 2, -4, -10, -6, 12;
     9, -3, 4, -4, 7, -13, -1, 4, -6, -7, 5, 17, -6, -6;
     30, -24, -8, 2, -20, -16, 8, 4, 0, -4, 20, 2, 12, -6;
     24, -18, 4, 2, -14, 2, 2, -8, -12, 2, 2, 8, 12, -6;
     -33, 39, 16, -4, 13, 5, -7, -8, 18, -1, -13, -13, -6, -6;
     30, -24, -8, 20, -20, -16, 8, 4, -18, -4, 2, 20, -6, 12;
     -18, 24, 4, -4, 16, -4, 8, 4, -6, -16, -22, 8, -6, 12;
     12, -6, -8, 2, -2, 2, -10, 4, 0, 14, 2, -16, 12, -6;
     -15, 21, -8, -16, 7, 11, -1, 4, 18, 5, -7, -7, -6, -6;
     18, -12, -8, -10, 4, 8, -16, -8, 12, -4, 8, 2, 12, -6;
     9, -3, -8, 8, -5, -1, 11, -8, -6, 5, 17, -7, -6, -6;
     6, -6, 0, -12, 6, 6, -6, -12, 12, 18, 6, -18, 0, 0;
     30, -30, 0, 12, -6, -6, 6, 12, -12, -18, -6, 18, 0, 0;
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

def pair24_09_10Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![72, 24, 72, 72, 96, 96, 144, 48, 120, 48;
     0, 24, 0, 0, -48, 24, 72, -24, 48, -24;
     -36, -48, 36, -36, 24, -12, -36, 48, -60, -24;
     -72, -48, -72, 0, -48, -84, -144, -60, -132, 12;
     -72, -48, -72, -72, -48, -12, -72, -60, -60, 12;
     108, 96, 36, 36, 96, 60, 108, 120, 156, 48;
     -144, -120, 0, 0, -48, 24, -72, -96, -168, -24;
     0, 24, 144, 0, 96, 96, 72, 48, 48, -24;
     0, 24, -72, 0, -48, -84, 0, -60, 12, 12;
     108, 96, 36, 36, 24, -12, 36, 48, 84, -24;
     0, 24, -72, -72, -48, -84, -72, 12, 12, -60;
     36, -48, -36, 36, -48, -12, -36, -24, -60, 48;
     72, 0, -72, 0, -72, -72, 0, 0, 72, 0;
     -144, -72, 0, -72, 0, 0, -72, -72, -144, -72;
     72, 0, 0, 0, 0, 0, 0, 0, 0, 0;
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
theorem pair24_09_10_certificate :
    pair24_09_10Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_09_10Rows id +
      pair24_09_10Inverse * integerInformationSelector pair24_09_10Free = (72 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_09_10_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_09_10Inverse.mulVec (fun t => if b t then 1 else -1) k = 72 ∨
      pair24_09_10Inverse.mulVec (fun t => if b t then 1 else -1) k = -72) →
    IntegerScaledHalfPattern 72 (1)
      (∑ k, encodedIntFrame base24Masks 9 k * pair24_09_10Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 10 k * pair24_09_10Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_09_10_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {9, 10} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 9 k * x k) (∑ k, base24Frame 10 k * x k) := by
  have h := order24_integer_pair_lift 9 10 pair24_09_10Rows pair24_09_10Free
    pair24_09_10Left pair24_09_10Inverse 72 (1) (by norm_num) (by decide +kernel)
    pair24_09_10_certificate pair24_09_10_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
