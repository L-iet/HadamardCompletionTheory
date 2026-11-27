/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P07_10
@[expose] public section
namespace CompletionTheory

def pair24_07_14Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 15]
def pair24_07_14Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_07_14Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![3, -1, 4, 4, 1, 1, 1, -2, 2, 4, 1, 1, 3, 2;
     13, -11, 0, 0, -5, 3, -5, -6, 2, 4, -1, 3, 1, 2;
     16, -14, 0, 0, -2, -6, -2, -6, 2, 4, -4, 6, 10, -4;
     14, -12, -4, 2, -8, -4, 4, -4, -4, 4, 0, 8, 2, 2;
     -18, 20, 4, -2, 4, 4, 4, 4, -4, -8, 4, -8, -6, 2;
     -28, 30, 8, -4, 10, 2, -2, 14, 2, -8, 0, -10, -10, -4;
     23, -21, -4, 8, -11, -7, 1, -10, 2, 4, -3, 5, 11, 2;
     7, -5, 0, 0, 1, -3, 1, -6, 2, 4, -7, -3, 7, 2;
     8, -6, -4, 2, -2, 2, -2, -4, -4, 4, 6, 2, -4, 2;
     8, -6, -4, -4, -2, 2, -2, 2, 2, 4, 0, 2, 2, -4;
     -20, 22, 0, -6, 10, 6, -2, 12, -4, -8, 2, -6, -8, 2;
     -14, 16, 0, 0, 4, 0, 4, 6, 2, -8, 2, 0, -8, -4;
     -28, 28, 4, -8, 12, 4, 0, 16, 0, -12, 8, -8, -16, 0;
     40, -40, -4, 8, -12, -4, 0, -16, 0, 12, -8, 8, 16, 0;
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

def pair24_07_14Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-12, -24, -12, -12, 0, 12, 12, 0, -12, 0;
     -36, -24, -36, -36, -48, -12, -12, -24, -36, -24;
     -48, -48, -24, -48, -24, -24, -48, 0, -72, -24;
     -24, -48, -24, 0, -48, -12, -48, -36, -60, -12;
     48, 48, 48, 48, 48, 36, 48, 12, 84, 36;
     72, 96, 48, 48, 96, 24, 72, 72, 120, 48;
     -84, -72, -36, -36, -48, -12, -60, -48, -108, -24;
     -36, -24, 12, -36, 0, 12, -12, 0, -36, -24;
     0, -24, -24, 0, -48, -12, 0, -36, -12, -12;
     0, 0, -24, -24, -24, -24, -24, 0, -24, -24;
     72, 72, 48, 48, 48, 12, 48, 36, 108, 12;
     48, 48, 24, 48, 48, 0, 24, 24, 48, 48;
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
theorem pair24_07_14_certificate :
    pair24_07_14Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_07_14Rows id +
      pair24_07_14Inverse * integerInformationSelector pair24_07_14Free = (24 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_07_14_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_07_14Inverse.mulVec (fun t => if b t then 1 else -1) k = 24 ∨
      pair24_07_14Inverse.mulVec (fun t => if b t then 1 else -1) k = -24) →
    IntegerScaledHalfPattern 24 (1)
      (∑ k, encodedIntFrame base24Masks 7 k * pair24_07_14Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 14 k * pair24_07_14Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_07_14_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {7, 14} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 7 k * x k) (∑ k, base24Frame 14 k * x k) := by
  have h := order24_integer_pair_lift 7 14 pair24_07_14Rows pair24_07_14Free
    pair24_07_14Left pair24_07_14Inverse 24 (1) (by norm_num) (by decide +kernel)
    pair24_07_14_certificate pair24_07_14_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
