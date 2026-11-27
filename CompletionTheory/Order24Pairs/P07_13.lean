/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P07_09
@[expose] public section
namespace CompletionTheory

def pair24_07_13Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 14, 15]
def pair24_07_13Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_07_13Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![-3, 4, 2, 2, 2, 2, 2, -1, -2, 2, 2, -1, -3, 4;
     5, -4, 0, 0, -2, 2, -2, -3, 0, 2, 0, 1, -1, 2;
     -7, 8, 0, 0, 4, 2, 4, -3, -9, 2, 3, -2, -10, 8;
     4, -3, -2, 1, -3, -1, 3, -2, -4, 2, 1, 3, -2, 3;
     0, 1, 2, -1, -1, -1, -1, 2, 4, -4, -1, -1, 6, -5;
     1, 0, 4, -2, 0, -4, -6, 7, 11, -4, -5, 0, 10, -12;
     -5, 6, -2, 4, 0, 2, 6, -5, -10, 2, 4, -3, -11, 12;
     -7, 8, 0, 0, 4, 2, 4, -3, -6, 2, 0, -5, -7, 8;
     10, -9, -2, 1, -3, -1, -3, -2, 2, 2, 1, 3, 4, -3;
     1, 0, -2, -2, 0, 2, 0, 1, -1, 2, 1, 0, -2, 0;
     2, -1, 0, -3, 1, -1, -5, 6, 6, -4, -3, 1, 8, -7;
     5, -4, 0, 0, -2, -4, -2, 3, 9, -4, -3, 4, 8, -10;
     10, -10, 2, -4, -2, -6, -8, 8, 16, -6, -4, 4, 16, -16;
     -4, 4, -2, 4, 2, 6, 8, -8, -16, 6, 4, -4, -16, 16;
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

def pair24_07_13Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![12, -12, 12, 12, 0, 24, 24, 0, 12, 0;
     -12, -12, -12, -12, -24, 0, 0, -12, -12, -12;
     36, -24, 48, 36, -12, 48, 36, 0, 24, -12;
     0, -24, 0, 12, -24, 6, -12, -18, -18, -6;
     -12, 24, -12, -12, 24, -18, -12, 6, 6, 18;
     -24, 48, -36, -36, 48, -48, -24, 36, 0, 24;
     24, -36, 48, 48, -24, 60, 36, -24, 12, -12;
     24, -12, 48, 24, 0, 48, 36, 0, 24, -12;
     -24, -12, -36, -24, -24, -30, -24, -18, -30, -6;
     12, 0, 0, 0, -12, 0, 0, 0, 0, -12;
     -12, 36, -24, -24, 24, -42, -24, 18, 6, 6;
     -24, 24, -36, -24, 24, -48, -36, 12, -24, 24;
     -48, 48, -72, -60, 36, -96, -60, 24, -24, 24;
     36, -60, 60, 48, -48, 84, 48, -36, 12, -36;
     12, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 12, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 12, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 12, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 12, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 12, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 12, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 12, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 12, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 12]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_07_13_certificate :
    pair24_07_13Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_07_13Rows id +
      pair24_07_13Inverse * integerInformationSelector pair24_07_13Free = (12 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_07_13_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_07_13Inverse.mulVec (fun t => if b t then 1 else -1) k = 12 ∨
      pair24_07_13Inverse.mulVec (fun t => if b t then 1 else -1) k = -12) →
    IntegerScaledHalfPattern 12 (1)
      (∑ k, encodedIntFrame base24Masks 7 k * pair24_07_13Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 13 k * pair24_07_13Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_07_13_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {7, 13} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 7 k * x k) (∑ k, base24Frame 13 k * x k) := by
  have h := order24_integer_pair_lift 7 13 pair24_07_13Rows pair24_07_13Free
    pair24_07_13Left pair24_07_13Inverse 12 (1) (by norm_num) (by decide +kernel)
    pair24_07_13_certificate pair24_07_13_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
