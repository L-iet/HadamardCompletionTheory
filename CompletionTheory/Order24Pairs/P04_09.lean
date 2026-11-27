/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P04_05
@[expose] public section
namespace CompletionTheory

def pair24_04_09Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15]
def pair24_04_09Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_04_09Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![15, -10, 8, 12, 4, 4, -2, -11, 16, 4, 5, 10, -5, 10;
     -5, 10, 4, -4, 12, -8, 4, -3, -2, 2, -5, -10, -5, 10;
     25, -20, 1, -1, -12, -2, 1, -12, 7, -7, 10, 20, -5, -5;
     -25, 30, 0, -5, -10, 10, 10, 20, -20, 0, 0, -15, 10, -5;
     -15, 20, 8, -3, 4, 4, -2, 4, -14, 4, -10, -5, 10, -5;
     5, 0, 9, 1, 2, -8, -11, 2, 13, -3, 0, 0, -5, -5;
     -25, 30, 0, 10, -10, 10, 10, 5, -20, 0, -15, 0, -5, 10;
     25, -20, -2, 2, -6, 4, -2, -21, 16, -16, -5, 20, -5, 10;
     5, 0, -6, 1, 2, -8, 4, 2, -2, 12, 0, -15, 10, -5;
     5, 0, -9, -11, 8, -2, 1, 8, 7, 3, 0, 0, -5, -5;
     25, -20, -8, -7, 6, -14, -8, 6, 4, -4, 10, 5, 10, -5;
     -5, 10, -5, 5, 0, 10, -5, 0, -5, 5, 10, -10, -5, -5;
     20, -20, -2, -8, 4, -6, -12, 4, 6, 14, 10, -10, 0, 0;
     10, -10, 2, 8, -4, 6, 12, -4, -6, -14, -10, 10, 0, 0;
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

def pair24_04_09Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-36, -108, -36, -36, -48, 48, 24, -24, -60, -24;
     12, 36, 12, 12, -24, 24, 72, -12, 60, -12;
     -72, -96, -12, -72, -36, -24, -72, 12, -120, -48;
     60, 120, 60, 120, 120, -30, 0, 30, 90, 90;
     24, 72, 24, 24, 72, 18, 24, 6, 90, 66;
     12, -24, -48, -48, -24, 24, 12, 48, 0, -12;
     0, 60, 120, 120, 120, 60, 60, 0, 60, 60;
     -96, -108, 24, -96, -48, 48, -36, -24, -120, -84;
     12, 36, -48, 12, -24, -66, 12, -42, 30, 18;
     48, 24, -12, -12, -36, -24, -12, 12, 0, -48;
     -24, -12, -84, -84, -72, -78, -84, -6, -30, -66;
     60, 0, 0, 60, 0, 0, 0, 0, 0, 60;
     24, -48, -96, -36, -108, -72, -36, -24, 0, -24;
     -84, -12, 36, -24, 48, 12, -24, -36, -60, -36;
     60, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 60, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 60, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 60, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 60, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 60, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 60, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 60, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 60, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 60]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_04_09_certificate :
    pair24_04_09Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_04_09Rows id +
      pair24_04_09Inverse * integerInformationSelector pair24_04_09Free = (60 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_04_09_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_04_09Inverse.mulVec (fun t => if b t then 1 else -1) k = 60 ∨
      pair24_04_09Inverse.mulVec (fun t => if b t then 1 else -1) k = -60) →
    IntegerScaledHalfPattern 60 (1)
      (∑ k, encodedIntFrame base24Masks 4 k * pair24_04_09Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 9 k * pair24_04_09Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_04_09_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {4, 9} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 4 k * x k) (∑ k, base24Frame 9 k * x k) := by
  have h := order24_integer_pair_lift 4 9 pair24_04_09Rows pair24_04_09Free
    pair24_04_09Left pair24_04_09Inverse 60 (1) (by norm_num) (by decide +kernel)
    pair24_04_09_certificate pair24_04_09_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
