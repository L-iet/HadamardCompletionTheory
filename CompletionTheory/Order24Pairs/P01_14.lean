/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P01_10
@[expose] public section
namespace CompletionTheory

def pair24_01_14Rows : Fin 14 → Fin 16 := ![0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15]
def pair24_01_14Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_01_14Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![15, 31, 29, 10, 8, 8, 1, -12, 15, 27, 8, 5, 20, 15;
     15, 11, -11, -10, 28, -32, 11, -12, 15, -3, -2, -5, -20, 15;
     15, 14, -14, 20, -38, -8, 14, -3, 15, -12, -23, 10, 40, -30;
     15, -18, 3, -30, -24, 36, 12, 6, -30, -6, 6, 30, -15, 15;
     15, 10, 5, -20, 20, 20, -20, -30, -30, 0, 20, -10, 5, 15;
     15, 30, 0, 0, 0, -30, -30, 15, 15, 30, -15, 0, 0, -30;
     15, -9, 39, -30, -42, 18, 21, -12, 15, -33, -12, -15, 30, 15;
     15, 5, -5, 20, -20, 10, 5, -30, 15, 15, -50, -35, 40, 15;
     15, -24, 9, 0, 18, -12, 6, -12, -30, 12, 48, 0, -45, 15;
     15, -24, -36, 0, 18, -12, 6, 33, 15, 12, 3, 0, 0, -30;
     15, -22, -23, 20, 34, -26, -22, 24, -30, 6, 4, 10, -5, 15;
     15, -16, 16, -10, -8, 22, -16, -3, 15, -12, 7, 40, -20, -30;
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

def pair24_01_14Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-72, -156, -72, -72, 24, 96, 108, 12, -60, 12;
     -72, 84, -72, -72, -96, -24, 108, -48, 60, -48;
     -108, -24, 72, -108, 156, -96, -108, 168, -120, -12;
     36, -72, 36, 216, -72, -18, -144, -126, -90, 54;
     0, -120, 0, 0, -120, 150, 0, -150, 30, 30;
     0, 0, -180, -180, 0, 0, 0, 180, 0, 0;
     -252, -36, 108, 108, 144, 36, -72, -108, -180, 72;
     -180, -60, 180, -180, 120, 120, 0, 60, -120, -120;
     108, -36, -72, 108, -216, -54, 108, -198, 90, -18;
     108, 144, -72, -72, -36, -144, -72, 72, 0, -108;
     144, 12, -36, -36, -168, -42, -36, 6, 150, -174;
     72, -24, -108, 72, -24, -96, -108, -12, -120, 168;
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
theorem pair24_01_14_certificate :
    pair24_01_14Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_01_14Rows id +
      pair24_01_14Inverse * integerInformationSelector pair24_01_14Free = (180 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_01_14_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_01_14Inverse.mulVec (fun t => if b t then 1 else -1) k = 180 ∨
      pair24_01_14Inverse.mulVec (fun t => if b t then 1 else -1) k = -180) →
    IntegerScaledHalfPattern 180 (1)
      (∑ k, encodedIntFrame base24Masks 1 k * pair24_01_14Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 14 k * pair24_01_14Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_01_14_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {1, 14} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 1 k * x k) (∑ k, base24Frame 14 k * x k) := by
  have h := order24_integer_pair_lift 1 14 pair24_01_14Rows pair24_01_14Free
    pair24_01_14Left pair24_01_14Inverse 180 (1) (by norm_num) (by decide +kernel)
    pair24_01_14_certificate pair24_01_14_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
