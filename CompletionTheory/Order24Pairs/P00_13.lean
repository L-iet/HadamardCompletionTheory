/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P00_12
@[expose] public section
namespace CompletionTheory

def pair24_00_13Rows : Fin 14 → Fin 16 := ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15]
def pair24_00_13Free : Fin 10 → Fin 24 := ![13, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_00_13Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![4, 9, 1, 2, 0, -6, -5, 5, 15, 5, 6, 8, 11, -7;
     4, 1, 9, 2, 16, 10, 11, -19, -25, 5, -2, -16, -29, 33;
     4, 5, -19, 2, -16, -22, -9, 17, 31, -7, 2, 20, 27, -35;
     4, -4, 8, -4, -4, 20, 12, -4, -20, -4, -4, -4, -12, 16;
     4, 4, 0, -4, 4, 4, -4, -4, -4, -4, 4, -4, 4, 0;
     4, 9, 1, 2, 0, -6, -5, 5, 3, 5, -6, -4, -1, -7;
     4, -5, 3, -10, -8, -2, -7, -1, 5, -1, 10, 8, 1, 3;
     4, 1, -15, 2, -8, -14, -13, 5, 23, 5, -2, 8, 19, -15;
     4, -6, 22, 8, 12, 24, 22, -22, -42, 2, 0, -28, -34, 38;
     4, -3, -11, 2, 0, -6, 7, 17, 15, -7, -6, -4, 11, -19;
     4, -2, -6, 8, 4, -8, 2, 14, 2, -10, -8, -4, 10, -6;
     4, -3, 13, 2, 0, 18, 7, -7, -9, -7, -6, -4, -13, 5;
     0, 2, 10, 12, 8, 20, 14, -6, -26, -6, -4, -24, -26, 26;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 4, -4, 0, -8, -8, 4, 12, 20, -12, -8, 0, 20, -20;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def pair24_00_13Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![36, 12, -72, -36, 24, -36, 12, 48, 12, 48;
     -60, -84, 120, 60, -72, 156, 108, -96, 12, -96;
     84, 108, -120, -84, 72, -180, -84, 144, 12, 96;
     -48, -48, 96, 96, 0, 72, 0, -72, -24, -24;
     0, 0, 0, 0, 0, 24, 0, -24, 24, 24;
     -12, 12, -24, -36, 24, 12, 12, 48, 12, 0;
     60, -12, -24, 36, -24, -12, -12, 0, -12, 48;
     84, 60, -72, -84, 24, -84, -36, 96, 12, 48;
     -120, -120, 192, 120, -48, 192, 120, -168, 0, -120;
     -12, 108, -24, -36, 72, -84, -36, 48, 12, 0;
     -24, 72, 0, -24, 48, -48, -24, 24, 48, -24;
     -60, -36, 72, 60, 24, 60, 12, -48, -36, 0;
     -120, -72, 144, 72, 0, 120, 72, -96, 24, -96;
     48, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 96, -48, -48, 96, -96, -48, 48, 0, 48;
     0, 48, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 48, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 48, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 48, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 48, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 48, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 48, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 48, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 48]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_00_13_certificate :
    pair24_00_13Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_00_13Rows id +
      pair24_00_13Inverse * integerInformationSelector pair24_00_13Free = (48 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_00_13_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_00_13Inverse.mulVec (fun t => if b t then 1 else -1) k = 48 ∨
      pair24_00_13Inverse.mulVec (fun t => if b t then 1 else -1) k = -48) →
    IntegerScaledHalfPattern 48 (1)
      (∑ k, encodedIntFrame base24Masks 0 k * pair24_00_13Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 13 k * pair24_00_13Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_00_13_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {0, 13} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 0 k * x k) (∑ k, base24Frame 13 k * x k) := by
  have h := order24_integer_pair_lift 0 13 pair24_00_13Rows pair24_00_13Free
    pair24_00_13Left pair24_00_13Inverse 48 (1) (by norm_num) (by decide +kernel)
    pair24_00_13_certificate pair24_00_13_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
