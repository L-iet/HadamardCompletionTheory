/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P09_14
@[expose] public section
namespace CompletionTheory

def pair24_10_13Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 14, 15]
def pair24_10_13Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_10_13Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![-9, 12, 8, 4, 6, 2, 2, 2, 3, 4, 2, -3, 1, 2;
     15, -12, 2, -2, -6, 2, -10, 2, -3, 10, -4, 3, 7, -4;
     -21, 24, 2, -2, 12, 2, 8, 2, -3, -17, 5, -6, -20, 14;
     12, -9, -4, 1, -9, -7, 5, 2, 0, -2, -1, 9, 4, -1;
     0, 3, 2, 1, -3, 5, 5, -4, -6, -8, 5, -3, -2, 5;
     3, 0, 8, -2, 0, -4, -10, -4, 9, 13, -7, 0, 10, -16;
     -15, 18, -4, 10, 0, 2, 14, 2, -9, -20, 8, -9, -23, 26;
     -21, 24, 2, -2, 12, 2, 8, 2, -3, -8, -4, -15, -11, 14;
     30, -27, -4, 1, -9, -7, -13, 2, 0, 16, -1, 9, 22, -19;
     3, 0, -4, -8, 0, 2, -4, 2, 9, 7, -1, 0, 4, -10;
     6, -3, -4, -5, 3, 5, -7, -4, 6, -2, -1, 3, 4, -1;
     15, -12, -4, 4, -6, -4, 2, -4, -3, 7, -1, 12, 4, -10;
     30, -30, 0, -6, -6, -6, -12, -6, 6, 18, 0, 12, 18, -18;
     -12, 12, 0, 6, 6, 6, 12, 6, -6, -18, 0, -12, -18, 18;
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

def pair24_10_13Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![12, 12, 12, 12, 48, 24, 48, 24, 36, 24;
     -60, 12, -60, -60, -24, -48, -24, -12, -36, -12;
     84, -24, 120, 84, 12, 96, 84, 24, 72, -12;
     -24, -24, -24, 12, -24, -30, -60, -30, -54, 6;
     12, -24, 12, 12, -24, 42, 12, -30, 18, 6;
     -24, 48, -60, -60, 48, -48, -24, 60, 0, 24;
     48, -60, 120, 120, -24, 132, 84, -48, 36, -12;
     48, 12, 120, 48, 48, 96, 84, 24, 72, -12;
     -96, 12, -132, -96, -24, -138, -96, -30, -90, 6;
     12, 48, -24, -24, 12, -48, -24, 24, 0, -12;
     12, 12, -24, -24, -24, -30, -24, 6, 18, -30;
     -24, -24, -60, -24, -24, -48, -60, -12, -72, 24;
     -72, 0, -144, -108, -36, -144, -108, 0, -72, 0;
     36, -36, 108, 72, 0, 108, 72, -36, 36, -36;
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
theorem pair24_10_13_certificate :
    pair24_10_13Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_10_13Rows id +
      pair24_10_13Inverse * integerInformationSelector pair24_10_13Free = (36 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_10_13_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_10_13Inverse.mulVec (fun t => if b t then 1 else -1) k = 36 ∨
      pair24_10_13Inverse.mulVec (fun t => if b t then 1 else -1) k = -36) →
    IntegerScaledHalfPattern 36 (1)
      (∑ k, encodedIntFrame base24Masks 10 k * pair24_10_13Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 13 k * pair24_10_13Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_10_13_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {10, 13} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 10 k * x k) (∑ k, base24Frame 13 k * x k) := by
  have h := order24_integer_pair_lift 10 13 pair24_10_13Rows pair24_10_13Free
    pair24_10_13Left pair24_10_13Inverse 36 (1) (by norm_num) (by decide +kernel)
    pair24_10_13_certificate pair24_10_13_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
