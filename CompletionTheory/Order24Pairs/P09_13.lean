/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P08_15
@[expose] public section
namespace CompletionTheory

def pair24_09_13Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 14, 15]
def pair24_09_13Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_09_13Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![-15, 20, 12, 8, 10, 6, 6, 2, 1, 4, 6, -5, -5, 10;
     25, -20, 0, 0, -10, 10, -10, 0, -15, 10, 0, 5, -5, 10;
     -35, 40, 9, -9, 20, -8, 2, 9, 12, -17, -3, -10, -5, -5;
     20, -15, -6, 1, -15, -13, 7, 4, 2, -2, -3, 15, 10, -5;
     0, 5, 6, -1, -5, 3, 3, -4, -2, -8, 3, -5, 10, -5;
     5, 0, 9, 1, 0, 2, -8, -11, 2, 13, -3, 0, -5, -5;
     -25, 30, 0, 10, 0, -10, 10, 10, 5, -20, 0, -15, -5, 10;
     -35, 40, 6, -6, 20, -2, 8, 6, 3, -8, -12, -25, -5, 10;
     50, -45, -12, 7, -15, -1, -11, -2, -16, 16, 9, 15, 10, -5;
     5, 0, -9, -11, 0, 8, -2, 1, 8, 7, 3, 0, -5, -5;
     10, -5, -6, -9, 5, 7, -13, -6, 12, -2, -3, 5, 10, -5;
     25, -20, -9, 9, -10, -2, 8, -9, -12, 7, 3, 20, -5, -5;
     50, -50, -6, -4, -10, 2, -8, -16, -8, 18, 12, 20, 0, 0;
     -20, 20, 6, 4, 10, -2, 8, 16, 8, -18, -12, -20, 0, 0;
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

def pair24_09_13Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![36, -12, 36, 36, 48, 72, 96, 24, 60, 24;
     -60, -60, -60, -60, -120, 0, 0, -60, -60, -60;
     72, 96, 132, 72, 156, 24, 72, 108, 120, 48;
     -48, -24, -48, 12, -24, -66, -108, -42, -90, 18;
     -12, 24, -12, -12, 24, 6, -12, -18, 30, 42;
     12, -24, -48, -48, -24, 24, 12, 48, 0, -12;
     0, 60, 120, 120, 120, 60, 60, 0, 60, 60;
     48, 84, 168, 48, 144, 96, 108, 72, 120, 12;
     -96, -108, -156, -96, -168, -102, -96, -114, -150, -54;
     48, 24, -12, -12, -36, -24, -12, 12, 0, -48;
     12, 36, -48, -48, -24, -66, -48, 18, 30, -42;
     -12, -96, -72, -12, -96, -24, -72, -48, -120, 12;
     -48, -144, -168, -108, -204, -96, -108, -72, -120, -72;
     -12, 84, 108, 48, 144, 36, 48, 12, 60, 12;
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
theorem pair24_09_13_certificate :
    pair24_09_13Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_09_13Rows id +
      pair24_09_13Inverse * integerInformationSelector pair24_09_13Free = (60 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_09_13_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_09_13Inverse.mulVec (fun t => if b t then 1 else -1) k = 60 ∨
      pair24_09_13Inverse.mulVec (fun t => if b t then 1 else -1) k = -60) →
    IntegerScaledHalfPattern 60 (1)
      (∑ k, encodedIntFrame base24Masks 9 k * pair24_09_13Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 13 k * pair24_09_13Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_09_13_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {9, 13} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 9 k * x k) (∑ k, base24Frame 13 k * x k) := by
  have h := order24_integer_pair_lift 9 13 pair24_09_13Rows pair24_09_13Free
    pair24_09_13Left pair24_09_13Inverse 60 (1) (by norm_num) (by decide +kernel)
    pair24_09_13_certificate pair24_09_13_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
