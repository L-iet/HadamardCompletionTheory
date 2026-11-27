/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P05_15
@[expose] public section
namespace CompletionTheory

def pair24_06_10Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 7, 8, 9, 11, 12, 13, 14, 15]
def pair24_06_10Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_06_10Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![-3, 6, 8, 4, 4, 0, 2, 3, 8, 0, -1, 2, 5, -2;
     -15, 18, 2, -2, 4, 12, 2, -3, -10, 6, -7, -10, -13, 16;
     3, 0, 2, -2, 4, -6, 2, -3, -1, -3, 2, 8, -4, -2;
     27, -24, -4, 1, -14, -12, 2, 0, 8, -6, 14, 5, 14, -11;
     15, -12, 2, 1, -8, 0, -4, -6, 2, 0, 2, 5, 8, -5;
     -27, 30, 8, -2, 10, 6, -4, 9, -7, 3, -10, -10, -10, 4;
     27, -24, -4, 10, -14, -12, 2, -9, 8, -6, 5, 14, 5, -2;
     3, 0, 2, -2, 4, -6, 2, -3, 8, -12, -7, 8, 5, -2;
     -9, 12, -4, 1, 4, 6, 2, 0, -10, 12, -4, -13, -4, 7;
     -9, 12, -4, -8, 4, 6, 2, 9, -1, 3, -4, -4, -4, -2;
     -15, 18, -4, -5, 10, 12, -4, 6, -16, 6, -4, -7, -10, 13;
     21, -18, -4, 4, -8, -6, -4, -3, 11, -3, 14, 2, 8, -14;
     -6, 6, 0, -6, 6, 6, -6, 6, -6, 12, 0, -12, -6, 6;
     24, -24, 0, 6, -6, -6, 6, -6, 6, -12, 0, 12, 6, -6;
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

def pair24_06_10Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-12, 12, -12, -12, 48, 0, 24, 24, 12, 24;
     60, 12, 60, 60, -24, 72, 96, -12, 84, -12;
     -12, -24, 24, -12, 12, 0, -12, 24, -24, -12;
     -84, -24, -84, -48, -24, -90, -120, -30, -114, 6;
     -48, -24, -48, -48, -24, -18, -48, -30, -42, 6;
     96, 48, 60, 60, 48, 72, 96, 60, 120, 24;
     -120, -60, -48, -48, -24, -36, -84, -48, -132, -12;
     -48, 12, 24, -48, 48, 0, -12, 24, -24, -12;
     60, 12, 24, 60, -24, 18, 60, -30, 66, 6;
     60, 48, 24, 24, 12, 0, 24, 24, 48, -12;
     96, 12, 60, 60, -24, 54, 60, 6, 102, -30;
     -48, -24, -84, -48, -24, -72, -84, -12, -96, 24;
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
theorem pair24_06_10_certificate :
    pair24_06_10Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_06_10Rows id +
      pair24_06_10Inverse * integerInformationSelector pair24_06_10Free = (36 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_06_10_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_06_10Inverse.mulVec (fun t => if b t then 1 else -1) k = 36 ∨
      pair24_06_10Inverse.mulVec (fun t => if b t then 1 else -1) k = -36) →
    IntegerScaledHalfPattern 36 (1)
      (∑ k, encodedIntFrame base24Masks 6 k * pair24_06_10Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 10 k * pair24_06_10Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_06_10_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {6, 10} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 6 k * x k) (∑ k, base24Frame 10 k * x k) := by
  have h := order24_integer_pair_lift 6 10 pair24_06_10Rows pair24_06_10Free
    pair24_06_10Left pair24_06_10Inverse 36 (1) (by norm_num) (by decide +kernel)
    pair24_06_10_certificate pair24_06_10_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
