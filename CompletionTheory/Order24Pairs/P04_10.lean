/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P04_06
@[expose] public section
namespace CompletionTheory

def pair24_04_10Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15]
def pair24_04_10Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_04_10Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![9, -6, 8, 4, -4, -4, 2, 3, 16, -4, 3, 6, 13, -10;
     -3, 6, 2, -2, 8, -4, 2, -3, -2, 2, -3, -6, -5, 8;
     15, -12, 2, -2, -10, -4, 2, -3, 7, -7, 6, 12, 4, -10;
     -15, 18, -4, 1, 2, 14, 2, 0, -20, 8, 0, -9, -14, 17;
     -9, 12, 2, 1, 8, 8, -4, -6, -14, 8, -6, -3, -8, 11;
     3, 0, 8, -2, -4, -10, -4, 9, 13, -7, 0, 0, 10, -16;
     -15, 18, -4, 10, 2, 14, 2, -9, -20, 8, -9, 0, -23, 26;
     15, -12, 2, -2, -10, -4, 2, -3, 16, -16, -3, 12, 13, -10;
     3, 0, -4, 1, 2, -4, 2, 0, -2, 8, 0, -9, 4, -1;
     3, 0, -4, -8, 2, -4, 2, 9, 7, -1, 0, 0, 4, -10;
     15, -12, -4, -5, 2, -10, -4, 6, 4, -4, 6, 3, 10, -7;
     -3, 6, -4, 4, 2, 8, -4, -3, -5, 5, 6, -6, -8, 2;
     12, -12, 0, -6, 0, -6, -6, 6, 6, 6, 6, -6, 6, -6;
     6, -6, 0, 6, 0, 6, 6, -6, -6, -6, -6, 6, -6, 6;
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

def pair24_04_10Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-60, 12, -60, -60, 48, -48, -24, 24, -36, 24;
     12, 12, 12, 12, -24, 24, 48, -12, 36, -12;
     -60, -24, -24, -60, 12, -48, -60, 24, -72, -12;
     84, -24, 84, 120, -24, 78, 48, -30, 54, 6;
     48, -24, 48, 48, -24, 78, 48, -30, 54, 6;
     -24, 48, -60, -60, 48, -48, -24, 60, 0, 24;
     48, -60, 120, 120, -24, 132, 84, -48, 36, -12;
     -96, 12, -24, -96, 48, -48, -60, 24, -72, -12;
     12, 12, -24, 12, -24, -30, 12, -30, 18, 6;
     12, 48, -24, -24, 12, -48, -24, 24, 0, -12;
     -24, 12, -60, -60, -24, -66, -60, 6, -18, -30;
     48, -24, 12, 48, -24, 24, 12, -12, 0, 24;
     0, 0, -72, -36, -36, -72, -36, 0, 0, 0;
     -36, -36, 36, 0, 0, 36, 0, -36, -36, -36;
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
theorem pair24_04_10_certificate :
    pair24_04_10Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_04_10Rows id +
      pair24_04_10Inverse * integerInformationSelector pair24_04_10Free = (36 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_04_10_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_04_10Inverse.mulVec (fun t => if b t then 1 else -1) k = 36 ∨
      pair24_04_10Inverse.mulVec (fun t => if b t then 1 else -1) k = -36) →
    IntegerScaledHalfPattern 36 (1)
      (∑ k, encodedIntFrame base24Masks 4 k * pair24_04_10Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 10 k * pair24_04_10Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_04_10_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {4, 10} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 4 k * x k) (∑ k, base24Frame 10 k * x k) := by
  have h := order24_integer_pair_lift 4 10 pair24_04_10Rows pair24_04_10Free
    pair24_04_10Left pair24_04_10Inverse 36 (1) (by norm_num) (by decide +kernel)
    pair24_04_10_certificate pair24_04_10_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
