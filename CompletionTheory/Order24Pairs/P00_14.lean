/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P00_13
@[expose] public section
namespace CompletionTheory

def pair24_00_14Rows : Fin 14 → Fin 16 := ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15]
def pair24_00_14Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_00_14Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![15, 33, 27, 15, 9, 9, 3, -6, 15, 21, 9, 0, 15, 15;
     15, 13, -13, -5, 29, -31, 13, -6, 15, -9, -1, -10, -25, 15;
     15, 16, -16, 25, -37, -7, 16, 3, 15, -18, -22, 5, 35, -30;
     15, -16, 1, -25, -23, 37, 14, 12, -30, -12, 7, 25, -20, 15;
     15, 12, 3, -15, 21, 21, -18, -24, -30, -6, 21, -15, 0, 15;
     15, 32, -2, 5, 1, -29, -28, 21, 15, 24, -14, -5, -5, -30;
     15, -7, 37, -25, -41, 19, 23, -6, 15, -39, -11, -20, 25, 15;
     15, 7, -7, 25, -19, 11, 7, -24, 15, 9, -49, -40, 35, 15;
     15, -22, 7, 5, 19, -11, 8, -6, -30, 6, 49, -5, -50, 15;
     15, -22, -38, 5, 19, -11, 8, 39, 15, 6, 4, -5, -5, -30;
     15, -20, -25, 25, 35, -25, -20, 30, -30, 0, 5, 5, -10, 15;
     15, -14, 14, -5, -7, 23, -14, 3, 15, -18, 8, 35, -25, -30;
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

def pair24_00_14Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-36, -108, -36, -36, 72, 108, 144, 36, 0, 36;
     -36, 132, -36, -36, -48, -12, 144, -24, 120, -24;
     -72, 24, 108, -72, 204, -84, -72, 192, -60, 12;
     72, -24, 72, 252, -24, -6, -108, -102, -30, 78;
     36, -72, 36, 36, -72, 162, 36, -126, 90, 54;
     36, 48, -144, -144, 48, 12, 36, 204, 60, 24;
     -216, 12, 144, 144, 192, 48, -36, -84, -120, 96;
     -144, -12, 216, -144, 168, 132, 36, 84, -60, -96;
     144, 12, -36, 144, -168, -42, 144, -174, 150, 6;
     144, 192, -36, -36, 12, -132, -36, 96, 60, -84;
     180, 60, 0, 0, -120, -30, 0, 30, 210, -150;
     108, 24, -72, 108, 24, -84, -72, 12, -60, 192;
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
theorem pair24_00_14_certificate :
    pair24_00_14Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_00_14Rows id +
      pair24_00_14Inverse * integerInformationSelector pair24_00_14Free = (180 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_00_14_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_00_14Inverse.mulVec (fun t => if b t then 1 else -1) k = 180 ∨
      pair24_00_14Inverse.mulVec (fun t => if b t then 1 else -1) k = -180) →
    IntegerScaledHalfPattern 180 (1)
      (∑ k, encodedIntFrame base24Masks 0 k * pair24_00_14Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 14 k * pair24_00_14Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_00_14_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {0, 14} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 0 k * x k) (∑ k, base24Frame 14 k * x k) := by
  have h := order24_integer_pair_lift 0 14 pair24_00_14Rows pair24_00_14Free
    pair24_00_14Left pair24_00_14Inverse 180 (1) (by norm_num) (by decide +kernel)
    pair24_00_14_certificate pair24_00_14_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
