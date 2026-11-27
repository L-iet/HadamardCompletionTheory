/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P01_08
@[expose] public section
namespace CompletionTheory

def pair24_01_12Rows : Fin 14 → Fin 16 := ![0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15]
def pair24_01_12Free : Fin 10 → Fin 24 := ![13, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_01_12Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![8, 13, 21, 6, 12, 14, -1, -19, -13, 25, 10, 12, -21, 29;
     8, 3, -5, -6, 20, -14, 1, -13, -3, 7, 6, -12, -11, 19;
     8, 2, 2, 12, -8, 12, 6, -22, -26, 10, -4, 24, -34, 18;
     8, -10, 14, -12, -8, 36, 18, -10, -38, -2, -4, 0, -22, 30;
     8, 6, -2, -12, 8, 4, -14, -10, -6, -2, 12, 0, 10, -2;
     8, 16, 0, 0, 0, -16, -16, 8, 8, 16, -8, 0, 0, -16;
     8, -15, 25, -18, -4, 22, -5, -31, -33, 13, 18, 12, -41, 49;
     8, -3, -11, 6, -4, -2, -17, -19, 3, 25, -6, 12, -5, 13;
     8, -8, 0, 0, 0, -16, 8, 8, 8, -8, 16, -24, 24, -16;
     8, -8, -24, 0, 0, -16, 8, 32, 32, -8, -8, 0, 24, -40;
     8, -6, -14, 12, 8, -20, -2, 26, 6, -14, -12, 0, 22, -14;
     8, -8, 24, 0, 0, 32, 8, -16, -16, -8, -8, 0, -24, 8;
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

def pair24_01_12Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-12, -180, 24, 12, -72, 156, 108, -48, -36, -48;
     12, -12, -24, -12, -120, 36, 84, -48, 36, -48;
     -24, -168, 144, 24, -48, 120, 24, 0, -72, -96;
     -72, -120, 144, 168, -48, 120, -24, -144, -72, -48;
     24, -24, -48, -24, -48, 24, -24, -48, 24, 48;
     0, 0, -96, -96, 0, 0, 0, 96, 0, 0;
     36, -228, 120, 156, -168, 204, 60, -144, -84, -48;
     84, -84, 24, -84, -72, 60, 12, 48, -36, -48;
     0, 96, -96, 0, 0, -144, 0, -48, 48, 48;
     0, 192, -96, -96, 96, -192, -96, 96, 0, 0;
     -24, 120, -48, -72, 48, -120, -72, 48, 72, -48;
     -96, -96, 96, 96, 0, 96, 0, -96, -96, 0;
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
theorem pair24_01_12_certificate :
    pair24_01_12Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_01_12Rows id +
      pair24_01_12Inverse * integerInformationSelector pair24_01_12Free = (96 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_01_12_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_01_12Inverse.mulVec (fun t => if b t then 1 else -1) k = 96 ∨
      pair24_01_12Inverse.mulVec (fun t => if b t then 1 else -1) k = -96) →
    IntegerScaledHalfPattern 96 (1)
      (∑ k, encodedIntFrame base24Masks 1 k * pair24_01_12Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 12 k * pair24_01_12Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_01_12_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {1, 12} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 1 k * x k) (∑ k, base24Frame 12 k * x k) := by
  have h := order24_integer_pair_lift 1 12 pair24_01_12Rows pair24_01_12Free
    pair24_01_12Left pair24_01_12Inverse 96 (1) (by norm_num) (by decide +kernel)
    pair24_01_12_certificate pair24_01_12_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
