/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P00_11
@[expose] public section
namespace CompletionTheory

def pair24_00_12Rows : Fin 14 → Fin 16 := ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15]
def pair24_00_12Free : Fin 10 → Fin 24 := ![13, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_00_12Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![8, 16, 16, 8, 8, 8, 0, -8, 0, 16, 8, 8, -8, 16;
     8, 6, -10, -4, 16, -20, 2, -2, 10, -2, 4, -16, 2, 6;
     8, 5, -3, 14, -12, 6, 7, -11, -13, 1, -6, 20, -21, 5;
     8, -7, 9, -10, -12, 30, 19, 1, -25, -11, -6, -4, -9, 17;
     8, 9, -7, -10, 4, -2, -13, 1, 7, -11, 10, -4, 23, -15;
     8, 19, -5, 2, -4, -22, -15, 19, 21, 7, -10, -4, 13, -29;
     8, -12, 20, -16, -8, 16, -4, -20, -20, 4, 16, 8, -28, 36;
     8, 0, -16, 8, -8, -8, -16, -8, 16, 16, -8, 8, 8, 0;
     8, -5, -5, 2, -4, -22, 9, 19, 21, -17, 14, -28, 37, -29;
     8, -5, -29, 2, -4, -22, 9, 43, 45, -17, -10, -4, 37, -53;
     8, -3, -19, 14, 4, -26, -1, 37, 19, -23, -14, -4, 35, -27;
     8, -5, 19, 2, -4, 26, 9, -5, -3, -17, -10, -4, -11, -5;
     0, 10, -22, 12, -8, -20, -2, 42, 38, -30, 4, -24, 38, -38;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 8, -8, 0, -16, -16, 8, 24, 40, -24, -16, 0, 40, -40;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def pair24_00_12Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![0, -96, 0, 0, 0, 96, 96, 0, 0, 0;
     24, 72, -48, -24, -48, -24, 72, 0, 72, 0;
     -12, -84, 120, 12, 24, 60, 12, 48, -36, -48;
     -60, -36, 120, 156, 24, 60, -36, -96, -36, 0;
     36, 60, -72, -36, 24, -36, -36, 0, 60, 96;
     12, 84, -120, -108, 72, -60, -12, 144, 36, 48;
     48, -144, 96, 144, -96, 144, 48, -96, -48, 0;
     96, 0, 0, -96, 0, 0, 0, 96, 0, 0;
     12, 180, -120, -12, 72, -204, -12, 0, 84, 96;
     12, 276, -120, -108, 168, -252, -108, 144, 36, 48;
     -12, 204, -72, -84, 120, -180, -84, 96, 108, 0;
     -84, -12, 72, 84, 72, 36, -12, -48, -60, 48;
     -24, 216, -144, -72, 144, -264, -72, 96, 120, 96;
     96, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 192, -96, -96, 192, -192, -96, 96, 0, 96;
     0, 96, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 96, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 96, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 96, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 96, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 96, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 96, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 96, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 96]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_00_12_certificate :
    pair24_00_12Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_00_12Rows id +
      pair24_00_12Inverse * integerInformationSelector pair24_00_12Free = (96 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_00_12_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_00_12Inverse.mulVec (fun t => if b t then 1 else -1) k = 96 ∨
      pair24_00_12Inverse.mulVec (fun t => if b t then 1 else -1) k = -96) →
    IntegerScaledHalfPattern 96 (1)
      (∑ k, encodedIntFrame base24Masks 0 k * pair24_00_12Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 12 k * pair24_00_12Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_00_12_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {0, 12} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 0 k * x k) (∑ k, base24Frame 12 k * x k) := by
  have h := order24_integer_pair_lift 0 12 pair24_00_12Rows pair24_00_12Free
    pair24_00_12Left pair24_00_12Inverse 96 (1) (by norm_num) (by decide +kernel)
    pair24_00_12_certificate pair24_00_12_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
