/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P00_02
@[expose] public section
namespace CompletionTheory

def pair24_00_03Rows : Fin 14 → Fin 16 := ![1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def pair24_00_03Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_00_03Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![3, 12, 3, -9, -9, 6, 15, 30, -12, -9, 0, 3, 27, -24;
     3, 0, -1, 11, -1, 0, -9, -10, 6, 5, -2, -5, -13, 16;
     3, 0, 5, -1, 5, 0, -9, -13, 6, 2, 1, 7, -16, 10;
     3, -3, -5, -5, 7, 3, 3, -5, -3, 1, 5, -4, 1, 2;
     3, 3, -3, 3, 3, -3, -3, -3, -3, 3, -3, 0, 3, 0;
     3, 6, 1, 1, -5, -6, 3, 1, 6, -2, -1, -1, -2, -4;
     3, 6, -5, -23, -11, 12, 21, 40, -30, -17, -4, 5, 37, -34;
     3, 0, 5, -1, 5, 0, -9, -4, 6, -7, -8, 7, -7, 10;
     3, -3, 1, 1, -5, 3, 3, 1, -3, 7, -1, -10, 7, -4;
     3, -12, 1, 19, 13, -6, -15, -35, 24, 16, -1, -1, -38, 32;
     3, -9, 5, 17, 5, -9, -9, -31, 15, 11, 1, -2, -25, 28;
     3, 0, -1, -7, -1, 0, 9, 17, -12, -4, 7, -5, 14, -20;
     0, -6, 4, 16, 10, -12, -12, -32, 18, 22, 2, -10, -32, 32;
     0, 6, 2, -10, -4, 12, 12, 20, -18, -16, -8, 4, 20, -20;
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

def pair24_00_03Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-72, 108, -72, -72, 144, -108, -36, 72, 0, 72;
     24, -36, 24, 24, -72, 60, 60, -36, 24, -36;
     24, -72, 60, 24, -36, 60, 24, 0, -12, -36;
     12, 0, 12, 48, 0, -6, -24, -18, -6, 18;
     0, 0, 0, 0, 0, 18, 0, -18, 18, 18;
     12, 0, -24, -24, 0, 12, 12, 36, 12, 0;
     -132, 180, -60, -60, 216, -168, -96, 72, -24, 108;
     -12, -36, 60, -12, 0, 60, 24, 0, -12, -36;
     12, 36, -24, 12, 0, -42, 12, -18, 30, 18;
     120, -144, 84, 84, -180, 156, 84, -72, 12, -108;
     96, -108, 60, 60, -144, 114, 60, -54, 42, -90;
     -12, 72, -48, -12, 72, -84, -48, 36, -12, 72;
     120, -144, 48, 84, -180, 120, 84, -72, 48, -72;
     -84, 108, -12, -48, 144, -84, -48, 36, -12, 36;
     36, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 36, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 36, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 36, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 36, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 36, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 36, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 36, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 36, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 36]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_00_03_certificate :
    pair24_00_03Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_00_03Rows id +
      pair24_00_03Inverse * integerInformationSelector pair24_00_03Free = (36 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_00_03_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_00_03Inverse.mulVec (fun t => if b t then 1 else -1) k = 36 ∨
      pair24_00_03Inverse.mulVec (fun t => if b t then 1 else -1) k = -36) →
    IntegerScaledHalfPattern 36 (1)
      (∑ k, encodedIntFrame base24Masks 0 k * pair24_00_03Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 3 k * pair24_00_03Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_00_03_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {0, 3} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 0 k * x k) (∑ k, base24Frame 3 k * x k) := by
  have h := order24_integer_pair_lift 0 3 pair24_00_03Rows pair24_00_03Free
    pair24_00_03Left pair24_00_03Inverse 36 (1) (by norm_num) (by decide +kernel)
    pair24_00_03_certificate pair24_00_03_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
