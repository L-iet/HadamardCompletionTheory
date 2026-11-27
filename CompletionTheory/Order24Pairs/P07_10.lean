/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P06_14
@[expose] public section
namespace CompletionTheory

def pair24_07_10Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 8, 9, 11, 12, 13, 14, 15]
def pair24_07_10Free : Fin 10 → Fin 24 := ![13, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_07_10Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![-5, 8, 8, 2, 4, 0, -2, 5, 10, 2, 1, 0, 7, -4;
     1, 2, 2, -4, -2, 6, -8, -1, 4, 2, 1, -6, 1, 2;
     1, 2, 2, -4, 4, -6, -2, -1, 1, -1, 4, 6, -2, -4;
     7, -4, -4, -1, -8, -6, 4, 2, -2, 2, 10, -3, 4, -1;
     1, 2, 2, 5, -2, 6, 10, -10, -14, 2, -8, 3, -8, 11;
     -5, 8, 8, 2, 4, 0, -2, 5, 1, -7, -8, 0, -2, -4;
     -2, 5, -4, 8, -5, -3, 7, -7, -8, 5, -2, 3, -11, 14;
     -8, 11, 2, -4, 7, -3, 1, -1, 4, -7, -8, 3, 1, 2;
     7, -4, -4, -1, -2, 0, -8, 2, 4, 8, 4, -9, 10, -7;
     7, -4, -4, -10, -2, 0, -8, 11, 13, -1, 4, 0, 10, -16;
     7, -4, -4, -1, 4, 6, -2, 2, -8, -4, -2, 3, -2, 5;
     7, -4, -4, 8, -2, 0, 10, -7, -5, -1, 4, 0, -8, 2;
     9, -9, 0, 0, 3, 3, 3, 0, -6, 3, -3, -3, -6, 6;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     9, -9, 0, 0, -3, -3, -3, 0, 6, -3, 3, 3, 6, -6;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def pair24_07_10Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![12, 24, -24, -12, 48, -12, 24, 36, 24, 36;
     12, 24, -24, -12, -24, -12, 24, 0, 24, 0;
     12, -12, 12, -12, 12, -12, -12, 36, -12, 0;
     12, -12, -24, 24, -24, -30, -48, -18, -30, 18;
     -24, -48, 48, 24, -24, 78, 24, -54, 6, -18;
     -24, 24, 12, -12, 48, 24, 24, 36, 24, 0;
     12, -48, 48, 60, -24, 60, 24, -36, -12, 0;
     12, 24, 48, -12, 48, 24, 24, 36, 24, 0;
     12, 24, -60, -12, -24, -66, -12, -18, 6, 18;
     12, 60, -60, -48, 12, -84, -48, 36, -12, 0;
     -24, -12, 12, -12, -24, 6, -12, -18, 6, -54;
     -24, -48, 12, 24, -24, 24, -12, -36, -48, 0;
     -36, -36, 0, 0, -36, 0, 0, -36, 0, -36;
     36, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, -36, -36, 0, -36, -36, 0, -36, 0;
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
theorem pair24_07_10_certificate :
    pair24_07_10Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_07_10Rows id +
      pair24_07_10Inverse * integerInformationSelector pair24_07_10Free = (36 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_07_10_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_07_10Inverse.mulVec (fun t => if b t then 1 else -1) k = 36 ∨
      pair24_07_10Inverse.mulVec (fun t => if b t then 1 else -1) k = -36) →
    IntegerScaledHalfPattern 36 (1)
      (∑ k, encodedIntFrame base24Masks 7 k * pair24_07_10Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 10 k * pair24_07_10Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_07_10_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {7, 10} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 7 k * x k) (∑ k, base24Frame 10 k * x k) := by
  have h := order24_integer_pair_lift 7 10 pair24_07_10Rows pair24_07_10Free
    pair24_07_10Left pair24_07_10Inverse 36 (1) (by norm_num) (by decide +kernel)
    pair24_07_10_certificate pair24_07_10_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
