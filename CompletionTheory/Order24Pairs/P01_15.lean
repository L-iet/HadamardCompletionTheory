/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P01_11
@[expose] public section
namespace CompletionTheory

def pair24_01_15Rows : Fin 14 → Fin 16 := ![0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
def pair24_01_15Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_01_15Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![15, 34, 26, 10, 2, 2, 4, -3, 30, 18, 2, 5, 20, 15;
     15, 14, -14, -10, 22, -38, 14, -3, 30, -12, -8, -5, -20, 15;
     15, 8, -8, 20, -26, 4, 8, -21, -15, 6, -11, 10, 40, -30;
     15, -15, 0, -30, -30, 30, 15, 15, -15, -15, 0, 30, -15, 15;
     15, 13, 2, -20, 14, 14, -17, -21, -15, -9, 14, -10, 5, 15;
     15, 24, 6, 0, 12, -18, -36, -3, -15, 48, -3, 0, 0, -30;
     15, -6, 36, -30, -48, 12, 24, -3, 30, -42, -18, -15, 30, 15;
     15, 8, -8, 20, -26, 4, 8, -21, 30, 6, -56, -35, 40, 15;
     15, -21, 6, 0, 12, -18, 9, -3, -15, 3, 42, 0, -45, 15;
     15, -30, -30, 0, 30, 0, 0, 15, -15, 30, 15, 0, 0, -30;
     15, -19, -26, 20, 28, -32, -19, 33, -15, -3, -2, 10, -5, 15;
     15, -22, 22, -10, 4, 34, -22, -21, -15, 6, 19, 40, -20, -30;
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

def pair24_01_15Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-108, -84, -108, -108, 96, 24, 72, 48, -60, 48;
     -108, 156, -108, -108, -24, -96, 72, -12, 60, -12;
     -36, -168, 144, -36, 12, 48, -36, 96, -120, -84;
     0, 0, 0, 180, 0, -90, -180, -90, -90, 90;
     -36, -48, -36, -36, -48, 78, -36, -114, 30, 66;
     72, -144, -108, -108, -144, 144, 72, 108, 0, -72;
     -288, 36, 72, 72, 216, -36, -108, -72, -180, 108;
     -216, 12, 144, -216, 192, 48, -36, 96, -120, -84;
     72, 36, -108, 72, -144, -126, 72, -162, 90, 18;
     180, 0, 0, 0, -180, 0, 0, 0, 0, -180;
     108, 84, -72, -72, -96, -114, -72, 42, 150, -138;
     144, -168, -36, 144, -168, 48, -36, -84, -120, 96;
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
theorem pair24_01_15_certificate :
    pair24_01_15Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_01_15Rows id +
      pair24_01_15Inverse * integerInformationSelector pair24_01_15Free = (180 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_01_15_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_01_15Inverse.mulVec (fun t => if b t then 1 else -1) k = 180 ∨
      pair24_01_15Inverse.mulVec (fun t => if b t then 1 else -1) k = -180) →
    IntegerScaledHalfPattern 180 (1)
      (∑ k, encodedIntFrame base24Masks 1 k * pair24_01_15Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 15 k * pair24_01_15Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_01_15_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {1, 15} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 1 k * x k) (∑ k, base24Frame 15 k * x k) := by
  have h := order24_integer_pair_lift 1 15 pair24_01_15Rows pair24_01_15Free
    pair24_01_15Left pair24_01_15Inverse 180 (1) (by norm_num) (by decide +kernel)
    pair24_01_15_certificate pair24_01_15_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
