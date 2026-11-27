/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P00_14
@[expose] public section
namespace CompletionTheory

def pair24_00_15Rows : Fin 14 → Fin 16 := ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
def pair24_00_15Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_00_15Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![15, 36, 24, 15, 3, 3, 6, 3, 30, 12, 3, 0, 15, 15;
     15, 16, -16, -5, 23, -37, 16, 3, 30, -18, -7, -10, -25, 15;
     15, 10, -10, 25, -25, 5, 10, -15, -15, 0, -10, 5, 35, -30;
     15, -13, -2, -25, -29, 31, 17, 21, -15, -21, 1, 25, -20, 15;
     15, 15, 0, -15, 15, 15, -15, -15, -15, -15, 15, -15, 0, 15;
     15, 26, 4, 5, 13, -17, -34, 3, -15, 42, -2, -5, -5, -30;
     15, -4, 34, -25, -47, 13, 26, 3, 30, -48, -17, -20, 25, 15;
     15, 10, -10, 25, -25, 5, 10, -15, 30, 0, -55, -40, 35, 15;
     15, -19, 4, 5, 13, -17, 11, 3, -15, -3, 43, -5, -50, 15;
     15, -28, -32, 5, 31, 1, 2, 21, -15, 24, 16, -5, -5, -30;
     15, -17, -28, 25, 29, -31, -17, 39, -15, -9, -1, 5, -10, 15;
     15, -20, 20, -5, 5, 35, -20, -15, -15, 0, 20, 35, -25, -30;
     0, 2, -32, 20, 16, -14, -28, 36, 0, -6, 46, 10, -50, 0;
     0, 10, 20, 10, -10, 20, 40, 0, 0, -30, -40, -40, 20, 0;
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

def pair24_00_15Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-72, -36, -72, -72, 144, 36, 108, 72, 0, 72;
     -72, 204, -72, -72, 24, -84, 108, 12, 120, 12;
     0, -120, 180, 0, 60, 60, 0, 120, -60, -60;
     36, 48, 36, 216, 48, -78, -144, -66, -30, 114;
     0, 0, 0, 0, 0, 90, 0, -90, 90, 90;
     108, -96, -72, -72, -96, 156, 108, 132, 60, -48;
     -252, 84, 108, 108, 264, -24, -72, -48, -120, 132;
     -180, 60, 180, -180, 240, 60, 0, 120, -60, -60;
     108, 84, -72, 108, -96, -114, 108, -138, 150, 42;
     216, 48, 36, 36, -132, 12, 36, 24, 60, -156;
     144, 132, -36, -36, -48, -102, -36, 66, 210, -114;
     180, -120, 0, 180, -120, 60, 0, -60, -60, 120;
     216, 48, -144, 36, -132, -168, 36, 24, 240, 24;
     -180, 60, 180, 0, 240, 60, 0, -60, -60, -60;
     180, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 180, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 180, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 180, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 180, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 180, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 180, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 180, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 180, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 180]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_00_15_certificate :
    pair24_00_15Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_00_15Rows id +
      pair24_00_15Inverse * integerInformationSelector pair24_00_15Free = (180 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_00_15_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_00_15Inverse.mulVec (fun t => if b t then 1 else -1) k = 180 ∨
      pair24_00_15Inverse.mulVec (fun t => if b t then 1 else -1) k = -180) →
    IntegerScaledHalfPattern 180 (1)
      (∑ k, encodedIntFrame base24Masks 0 k * pair24_00_15Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 15 k * pair24_00_15Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_00_15_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {0, 15} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 0 k * x k) (∑ k, base24Frame 15 k * x k) := by
  have h := order24_integer_pair_lift 0 15 pair24_00_15Rows pair24_00_15Free
    pair24_00_15Left pair24_00_15Inverse 180 (1) (by norm_num) (by decide +kernel)
    pair24_00_15_certificate pair24_00_15_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
