/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P09_13
@[expose] public section
namespace CompletionTheory

def pair24_10_12Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15]
def pair24_10_12Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_10_12Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![0, 3, 8, 4, 3, -1, -1, 2, 3, 10, -1, 3, 7, -4;
     6, -3, 2, -2, -3, 5, -7, 2, -3, 4, -1, -3, 1, 2;
     -3, 6, 2, -2, 6, -4, 2, 2, -3, -5, -1, 6, -8, 2;
     -15, 18, -4, 1, 0, 2, 14, 2, 0, -20, 8, -9, -14, 17;
     9, -6, 2, 1, -6, 2, 2, -4, -6, -2, 2, 3, 4, -1;
     3, 0, 8, -2, 0, -4, -10, -4, 9, 13, -7, 0, 10, -16;
     12, -9, -4, 10, -9, -7, 5, 2, -9, -2, -1, 9, -5, 8;
     24, -21, 2, -2, -3, -13, -7, 2, -3, 22, -19, 15, 19, -16;
     3, 0, -4, 1, 0, 2, -4, 2, 0, -2, 8, -9, 4, -1;
     3, 0, -4, -8, 0, 2, -4, 2, 9, 7, -1, 0, 4, -10;
     -3, 6, -4, -5, 6, 8, -4, -4, 6, -8, 2, -3, -2, 5;
     -21, 24, -4, 4, 6, 8, 14, -4, -3, -17, 11, -12, -20, 14;
     -6, 6, 0, -6, 6, 6, 0, -6, 6, -6, 12, -12, -6, 6;
     24, -24, 0, 6, -6, -6, 0, 6, -6, 6, -12, 12, 6, -6;
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

def pair24_10_12Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-24, 12, -24, -24, 48, -12, 12, 24, 0, 24;
     -24, 12, -24, -24, -24, -12, 12, -12, 0, -12;
     12, -24, 48, 12, 12, 24, 12, 24, 0, -12;
     84, -24, 84, 120, -24, 78, 48, -30, 54, 6;
     -24, -24, -24, -24, -24, 6, -24, -30, -18, 6;
     -24, 48, -60, -60, 48, -48, -24, 60, 0, 24;
     -60, -60, 12, 12, -24, 24, -24, -48, -72, -12;
     -132, 12, -60, -132, 48, -84, -96, 24, -108, -12;
     12, 12, -24, 12, -24, -30, 12, -30, 18, 6;
     12, 48, -24, -24, 12, -48, -24, 24, 0, -12;
     48, 12, 12, 12, -24, 6, 12, 6, 54, -30;
     120, -24, 84, 120, -24, 96, 84, -12, 72, 24;
     72, 0, 0, 36, -36, 0, 36, 0, 72, 0;
     -108, -36, -36, -72, 0, -36, -72, -36, -108, -36;
     36, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 36, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 36, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 36, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 36, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 36, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 36, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 36, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 36, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 36]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_10_12_certificate :
    pair24_10_12Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_10_12Rows id +
      pair24_10_12Inverse * integerInformationSelector pair24_10_12Free = (36 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_10_12_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_10_12Inverse.mulVec (fun t => if b t then 1 else -1) k = 36 ∨
      pair24_10_12Inverse.mulVec (fun t => if b t then 1 else -1) k = -36) →
    IntegerScaledHalfPattern 36 (1)
      (∑ k, encodedIntFrame base24Masks 10 k * pair24_10_12Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 12 k * pair24_10_12Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_10_12_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {10, 12} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 10 k * x k) (∑ k, base24Frame 12 k * x k) := by
  have h := order24_integer_pair_lift 10 12 pair24_10_12Rows pair24_10_12Free
    pair24_10_12Left pair24_10_12Inverse 36 (1) (by norm_num) (by decide +kernel)
    pair24_10_12_certificate pair24_10_12_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
