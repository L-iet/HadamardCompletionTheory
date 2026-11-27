/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P00_03
@[expose] public section
namespace CompletionTheory

def pair24_00_04Rows : Fin 14 → Fin 16 := ![1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def pair24_00_04Free : Fin 10 → Fin 24 := ![13, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_00_04Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![2, 5, -3, -2, -8, -5, 7, 15, 1, 4, 8, -2, 13, -11;
     2, 1, 1, 6, 0, 3, -5, -5, 1, 0, -4, -2, -7, 9;
     2, 3, -13, -10, -16, -7, 13, 23, -5, 2, 14, -2, 21, -25;
     2, -3, 11, 2, 20, 11, -11, -25, 1, -4, -10, 4, -21, 23;
     2, 1, 7, 6, 12, 3, -11, -17, 1, 0, -10, 4, -13, 15;
     2, 5, -3, -2, -8, -5, 7, 9, 1, -2, 2, -2, 7, -11;
     2, -5, 19, 6, 24, 9, -23, -35, 7, 0, -16, 10, -37, 39;
     2, 1, -11, -6, -12, -9, 7, 19, 1, 0, 8, -2, 17, -15;
     2, -1, -3, -2, -8, 1, 7, 9, -5, 4, 2, -8, 13, -11;
     2, -1, -9, -2, -8, 1, 13, 15, -5, -2, 2, -2, 13, -17;
     2, 1, -17, -6, -24, -9, 25, 31, -11, 0, 14, -8, 35, -33;
     2, -1, 3, -2, 4, 1, 1, 3, -5, -2, 2, -2, 1, -5;
     0, 4, -16, -8, -20, -8, 24, 32, -12, 4, 12, -12, 32, -32;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 2, -2, -4, -4, 2, 6, 10, -6, -4, 0, 0, 10, -10;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def pair24_00_04Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![36, 36, -72, -36, 24, -60, -12, 48, 12, 48;
     -12, -12, 24, 12, -24, 36, 36, -24, 12, -24;
     60, 84, -96, -60, 48, -132, -60, 96, 12, 72;
     -60, -84, 120, 84, -24, 120, 36, -84, -24, -60;
     -36, -60, 72, 36, -24, 96, 36, -60, 0, -36;
     12, 36, -48, -36, 24, -36, -12, 48, 12, 24;
     -60, -156, 168, 108, -72, 204, 84, -120, -36, -96;
     60, 60, -72, -60, 24, -84, -36, 72, 12, 48;
     12, 60, -48, -12, 24, -72, -12, 12, 24, 36;
     12, 84, -48, -36, 48, -84, -36, 48, 12, 24;
     60, 156, -144, -84, 72, -192, -84, 108, 48, 84;
     -12, 12, 0, 12, 24, -12, -12, 0, -12, 24;
     48, 144, -144, -72, 72, -192, -72, 96, 48, 96;
     24, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 48, -24, -24, 48, -48, -24, 24, 0, 24;
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
theorem pair24_00_04_certificate :
    pair24_00_04Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_00_04Rows id +
      pair24_00_04Inverse * integerInformationSelector pair24_00_04Free = (24 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_00_04_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_00_04Inverse.mulVec (fun t => if b t then 1 else -1) k = 24 ∨
      pair24_00_04Inverse.mulVec (fun t => if b t then 1 else -1) k = -24) →
    IntegerScaledHalfPattern 24 (1)
      (∑ k, encodedIntFrame base24Masks 0 k * pair24_00_04Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 4 k * pair24_00_04Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_00_04_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {0, 4} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 0 k * x k) (∑ k, base24Frame 4 k * x k) := by
  have h := order24_integer_pair_lift 0 4 pair24_00_04Rows pair24_00_04Free
    pair24_00_04Left pair24_00_04Inverse 24 (1) (by norm_num) (by decide +kernel)
    pair24_00_04_certificate pair24_00_04_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
