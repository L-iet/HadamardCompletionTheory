/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P05_14
@[expose] public section
namespace CompletionTheory

def pair24_06_09Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 7, 8, 10, 11, 12, 13, 14, 15]
def pair24_06_09Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_06_09Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![15, -14, 0, 4, -4, 0, -2, -7, 8, 0, 5, 6, -1, 2;
     -25, 26, 4, -4, 8, 4, 4, 9, -10, 2, -9, -10, -1, 2;
     -1, 2, 1, -1, 2, -2, 1, 0, -1, -1, 0, 2, -1, -1;
     25, -24, -4, 3, -10, -4, -2, -8, 8, -2, 10, 7, 2, -1;
     9, -8, 0, 1, -4, 0, -2, -4, 2, 0, 2, 3, 2, -1;
     -23, 24, 5, -3, 8, 2, 1, 10, -7, 1, -8, -8, -1, -1;
     25, -24, -4, 6, -10, -4, -2, -11, 8, -2, 7, 10, -1, 2;
     17, -16, -2, 2, -4, -2, -2, -9, 8, -4, 3, 8, -1, 2;
     -23, 24, 2, -3, 8, 2, 4, 10, -10, 4, -8, -11, 2, -1;
     -5, 6, -1, -3, 2, 2, 1, 4, -1, 1, -2, -2, -1, -1;
     -37, 38, 4, -7, 14, 4, 4, 18, -16, 2, -12, -13, 2, -1;
     29, -28, -5, 5, -10, -2, -5, -12, 11, -1, 12, 8, -1, -1;
     -14, 14, 2, -4, 6, 2, 0, 8, -6, 4, -4, -8, 0, 0;
     20, -20, -2, 4, -6, -2, 0, -8, 6, -4, 4, 8, 0, 0;
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

def pair24_06_09Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-36, -60, -36, -36, -48, 0, -24, -24, -60, -24;
     60, 84, 60, 60, 72, 24, 72, 36, 108, 36;
     0, 0, 12, 0, 12, 0, 0, 12, 0, 0;
     -60, -72, -60, -48, -72, -30, -72, -42, -102, -30;
     -24, -24, -24, -24, -24, -6, -24, -18, -30, -6;
     60, 72, 48, 48, 72, 24, 60, 48, 96, 36;
     -72, -84, -48, -48, -72, -12, -60, -48, -108, -36;
     -48, -60, -24, -48, -48, 0, -36, -24, -72, -36;
     60, 84, 48, 60, 72, 6, 60, 30, 102, 42;
     24, 24, 12, 12, 12, 0, 12, 12, 24, 0;
     96, 132, 84, 84, 120, 18, 84, 66, 162, 54;
     -60, -96, -72, -60, -96, -24, -72, -48, -120, -36;
     48, 48, 24, 36, 36, 0, 36, 24, 72, 24;
     -60, -60, -36, -48, -48, -12, -48, -36, -84, -36;
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
theorem pair24_06_09_certificate :
    pair24_06_09Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_06_09Rows id +
      pair24_06_09Inverse * integerInformationSelector pair24_06_09Free = (12 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_06_09_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_06_09Inverse.mulVec (fun t => if b t then 1 else -1) k = 12 ∨
      pair24_06_09Inverse.mulVec (fun t => if b t then 1 else -1) k = -12) →
    IntegerScaledHalfPattern 12 (1)
      (∑ k, encodedIntFrame base24Masks 6 k * pair24_06_09Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 9 k * pair24_06_09Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_06_09_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {6, 9} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 6 k * x k) (∑ k, base24Frame 9 k * x k) := by
  have h := order24_integer_pair_lift 6 9 pair24_06_09Rows pair24_06_09Free
    pair24_06_09Left pair24_06_09Inverse 12 (1) (by norm_num) (by decide +kernel)
    pair24_06_09_certificate pair24_06_09_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
