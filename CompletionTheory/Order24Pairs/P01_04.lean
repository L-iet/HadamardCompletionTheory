/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P00_15
@[expose] public section
namespace CompletionTheory

def pair24_01_04Rows : Fin 14 → Fin 16 := ![0, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def pair24_01_04Free : Fin 10 → Fin 24 := ![13, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_01_04Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![1, 2, 0, 0, -2, -2, 1, 4, 2, 2, 3, 0, 3, -2;
     1, 0, 2, 4, 2, 2, -5, -6, 2, 0, -3, 0, -7, 8;
     1, 1, -5, -4, -6, -3, 4, 8, -1, 1, 6, 0, 7, -9;
     1, -2, 7, 2, 12, 6, -8, -16, 2, -2, -6, 3, -14, 15;
     1, 0, 5, 4, 8, 2, -8, -12, 2, 0, -6, 3, -10, 11;
     1, 2, 0, 0, -2, -2, 1, 1, 2, -1, 0, 0, 0, -2;
     1, -3, 11, 4, 14, 5, -14, -21, 5, 0, -9, 6, -22, 23;
     1, 0, -4, -2, -4, -4, 1, 6, 2, 0, 3, 0, 5, -4;
     1, -1, 0, 0, -2, 1, 1, 1, -1, 2, 0, -3, 3, -2;
     1, -1, -3, 0, -2, 1, 4, 4, -1, -1, 0, 0, 3, -5;
     1, 0, -7, -2, -10, -4, 10, 12, -4, 0, 6, -3, 14, -13;
     1, -1, 3, 0, 4, 1, -2, -2, -1, -1, 0, 0, -3, 1;
     0, 2, -8, -4, -10, -4, 12, 16, -6, 2, 6, -6, 16, -16;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 1, -1, -2, -2, 1, 3, 5, -3, -2, 0, 0, 5, -5;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def pair24_01_04Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![12, 0, -24, -12, 0, -12, 0, 12, 0, 12;
     -12, -24, 24, 12, -24, 36, 24, -24, 0, -24;
     24, 24, -36, -24, 12, -48, -24, 36, 0, 24;
     -36, -60, 72, 48, -24, 78, 24, -54, -18, -42;
     -24, -48, 48, 24, -24, 66, 24, -42, -6, -30;
     0, 0, -12, -12, 0, 0, 0, 12, 0, 0;
     -36, -96, 96, 60, -48, 120, 48, -72, -24, -60;
     24, 12, -24, -24, 0, -24, -12, 24, 0, 12;
     0, 12, -12, 0, 0, -18, 0, -6, 6, 6;
     0, 24, -12, -12, 12, -24, -12, 12, 0, 0;
     24, 60, -60, -36, 24, -78, -36, 42, 18, 30;
     -12, -12, 12, 12, 0, 12, 0, -12, -12, 0;
     24, 72, -72, -36, 36, -96, -36, 48, 24, 48;
     12, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 24, -12, -12, 24, -24, -12, 12, 0, 12;
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
theorem pair24_01_04_certificate :
    pair24_01_04Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_01_04Rows id +
      pair24_01_04Inverse * integerInformationSelector pair24_01_04Free = (12 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_01_04_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_01_04Inverse.mulVec (fun t => if b t then 1 else -1) k = 12 ∨
      pair24_01_04Inverse.mulVec (fun t => if b t then 1 else -1) k = -12) →
    IntegerScaledHalfPattern 12 (-1)
      (∑ k, encodedIntFrame base24Masks 1 k * pair24_01_04Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 4 k * pair24_01_04Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_01_04_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {1, 4} x →
    HalfCorrelationPattern 24 (rationalRealCast (-1))
      (∑ k, base24Frame 1 k * x k) (∑ k, base24Frame 4 k * x k) := by
  have h := order24_integer_pair_lift 1 4 pair24_01_04Rows pair24_01_04Free
    pair24_01_04Left pair24_01_04Inverse 12 (-1) (by norm_num) (by decide +kernel)
    pair24_01_04_certificate pair24_01_04_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
