/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P01_05
@[expose] public section
namespace CompletionTheory

def pair24_01_09Rows : Fin 14 → Fin 16 := ![0, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15]
def pair24_01_09Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_01_09Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![15, 28, 32, 10, 14, 14, -2, -21, 36, 14, 5, 20, -15, 30;
     15, 8, -8, -10, 34, -26, 8, -21, 6, 4, -5, -20, -15, 30;
     15, 11, -11, 20, -32, -2, 11, -12, -3, -17, 10, 40, -15, -15;
     15, -12, -3, -30, -36, 24, 18, 24, -24, -6, 30, -15, 30, -15;
     15, 16, -1, -20, 8, 8, -14, -12, -18, 8, -10, 5, 30, -15;
     15, 27, 3, 0, 6, -24, -33, 6, 39, -9, 0, 0, -15, -15;
     15, -12, 42, -30, -36, 24, 18, -21, -24, -6, -15, 30, -15, 30;
     15, 2, -2, 20, -14, 16, 2, -39, 24, -44, -35, 40, -15, 30;
     15, -18, 3, 0, 6, -24, 12, 6, -6, 36, 0, -45, 30, -15;
     15, -27, -33, 0, 24, -6, 3, 24, 21, 9, 0, 0, -15, -15;
     15, -16, -29, 20, 22, -38, -16, 42, -12, -8, 10, -5, 30, -15;
     15, -19, 19, -10, -2, 28, -19, -12, -3, 13, 40, -20, -15, -15;
     0, 2, -32, 20, 16, -14, -28, 36, -6, 46, 10, -50, 0, 0;
     0, 10, 20, 10, -10, 20, 40, 0, -30, -40, -40, 20, 0, 0;
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

def pair24_01_09Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-36, -228, -36, -36, -48, 168, 144, -24, -60, -24;
     -36, 12, -36, -36, -168, 48, 144, -84, 60, -84;
     -72, -96, 108, -72, 84, -24, -72, 132, -120, -48;
     -36, 72, -36, 144, 72, -162, -216, -54, -90, 126;
     -72, 24, -72, -72, 24, 6, -72, -78, 30, 102;
     36, -72, -144, -144, -72, 72, 36, 144, 0, -36;
     -216, -108, 144, 144, 72, 108, -36, -144, -180, 36;
     -144, -132, 216, -144, 48, 192, 36, 24, -120, -156;
     36, 108, -144, 36, -72, -198, 36, -126, 90, 54;
     144, 72, -36, -36, -108, -72, -36, 36, 0, -144;
     72, 156, -108, -108, -24, -186, -108, 78, 150, -102;
     108, -96, -72, 108, -96, -24, -72, -48, -120, 132;
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
theorem pair24_01_09_certificate :
    pair24_01_09Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_01_09Rows id +
      pair24_01_09Inverse * integerInformationSelector pair24_01_09Free = (180 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_01_09_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_01_09Inverse.mulVec (fun t => if b t then 1 else -1) k = 180 ∨
      pair24_01_09Inverse.mulVec (fun t => if b t then 1 else -1) k = -180) →
    IntegerScaledHalfPattern 180 (1)
      (∑ k, encodedIntFrame base24Masks 1 k * pair24_01_09Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 9 k * pair24_01_09Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_01_09_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {1, 9} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 1 k * x k) (∑ k, base24Frame 9 k * x k) := by
  have h := order24_integer_pair_lift 1 9 pair24_01_09Rows pair24_01_09Free
    pair24_01_09Left pair24_01_09Inverse 180 (1) (by norm_num) (by decide +kernel)
    pair24_01_09_certificate pair24_01_09_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
