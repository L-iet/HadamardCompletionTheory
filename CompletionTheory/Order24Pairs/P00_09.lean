/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P00_08
@[expose] public section
namespace CompletionTheory

def pair24_00_09Rows : Fin 14 → Fin 16 := ![1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15]
def pair24_00_09Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_00_09Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![15, 30, 30, 15, 15, 15, 0, -15, 30, 15, 0, 15, -15, 30;
     15, 10, -10, -5, 35, -25, 10, -15, 0, 5, -10, -25, -15, 30;
     15, 13, -13, 25, -31, -1, 13, -6, -9, -16, 5, 35, -15, -15;
     15, -10, -5, -25, -35, 25, 20, 30, -30, -5, 25, -20, 30, -15;
     15, 18, -3, -15, 9, 9, -12, -6, -24, 9, -15, 0, 30, -15;
     15, 29, 1, 5, 7, -23, -31, 12, 33, -8, -5, -5, -15, -15;
     15, -10, 40, -25, -35, 25, 20, -15, -30, -5, -20, 25, -15, 30;
     15, 4, -4, 25, -13, 17, 4, -33, 18, -43, -40, 35, -15, 30;
     15, -16, 1, 5, 7, -23, 14, 12, -12, 37, -5, -50, 30, -15;
     15, -25, -35, 5, 25, -5, 5, 30, 15, 10, -5, -5, -15, -15;
     15, -14, -31, 25, 23, -37, -14, 48, -18, -7, 5, -10, 30, -15;
     15, -17, 17, -5, -1, 29, -17, -6, -9, 14, 35, -25, -15, -15;
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

def pair24_00_09Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![0, -180, 0, 0, 0, 180, 180, 0, 0, 0;
     0, 60, 0, 0, -120, 60, 180, -60, 120, -60;
     -36, -48, 144, -36, 132, -12, -36, 156, -60, -24;
     0, 120, 0, 180, 120, -150, -180, -30, -30, 150;
     -36, 72, -36, -36, 72, 18, -36, -54, 90, 126;
     72, -24, -108, -108, -24, 84, 72, 168, 60, -12;
     -180, -60, 180, 180, 120, 120, 0, -120, -120, 60;
     -108, -84, 252, -108, 96, 204, 72, 48, -60, -132;
     72, 156, -108, 72, -24, -186, 72, -102, 150, 78;
     180, 120, 0, 0, -60, -60, 0, 60, 60, -120;
     108, 204, -72, -72, 24, -174, -72, 102, 210, -78;
     144, -48, -36, 144, -48, -12, -36, -24, -60, 156;
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
theorem pair24_00_09_certificate :
    pair24_00_09Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_00_09Rows id +
      pair24_00_09Inverse * integerInformationSelector pair24_00_09Free = (180 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_00_09_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_00_09Inverse.mulVec (fun t => if b t then 1 else -1) k = 180 ∨
      pair24_00_09Inverse.mulVec (fun t => if b t then 1 else -1) k = -180) →
    IntegerScaledHalfPattern 180 (1)
      (∑ k, encodedIntFrame base24Masks 0 k * pair24_00_09Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 9 k * pair24_00_09Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_00_09_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {0, 9} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 0 k * x k) (∑ k, base24Frame 9 k * x k) := by
  have h := order24_integer_pair_lift 0 9 pair24_00_09Rows pair24_00_09Free
    pair24_00_09Left pair24_00_09Inverse 180 (1) (by norm_num) (by decide +kernel)
    pair24_00_09_certificate pair24_00_09_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
