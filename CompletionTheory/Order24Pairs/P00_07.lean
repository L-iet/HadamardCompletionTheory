/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P00_06
@[expose] public section
namespace CompletionTheory

def pair24_00_07Rows : Fin 14 → Fin 16 := ![1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15]
def pair24_00_07Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_00_07Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![3, 6, 6, 3, 3, 3, -3, 0, 6, 3, 0, 3, -3, 6;
     3, 0, 0, -1, 11, -1, -9, -10, 6, 5, -2, -5, -13, 16;
     3, 0, 0, 5, -1, 5, -9, -13, 6, 2, 1, 7, -16, 10;
     3, -6, 3, -5, 1, 13, -6, -20, 6, 7, 5, -4, -14, 17;
     3, 6, -3, -3, -3, -3, 6, 12, -12, -3, -3, 0, 18, -15;
     3, 12, -6, 1, -11, -17, 21, 31, -12, -14, -1, -1, 28, -34;
     3, -6, 12, -5, 1, 13, -15, -20, 6, 7, -4, 5, -23, 26;
     3, 0, 0, 5, -1, 5, -9, -4, 6, -7, -8, 7, -7, 10;
     3, -6, 3, 1, 7, 1, -6, -14, 6, 13, -1, -10, -8, 11;
     3, -6, -6, 1, 7, 1, 3, -5, 6, 4, -1, -1, -8, 2;
     3, 0, -9, 5, -1, -13, 18, 14, -12, -7, 1, -2, 20, -17;
     3, 0, 0, -1, -7, -1, 9, 17, -12, -4, 7, -5, 14, -20;
     0, 6, -12, 4, -8, -14, 24, 28, -18, -2, 2, -10, 28, -28;
     0, -6, 12, 2, 14, 20, -24, -40, 18, 8, -8, 4, -40, 40;
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

def pair24_00_07Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![0, -36, 0, 0, 0, 36, 36, 0, 0, 0;
     24, -36, 24, 24, -72, 60, 60, -36, 24, -36;
     24, -72, 60, 24, -36, 60, 24, 0, -12, -36;
     48, -72, 48, 84, -72, 66, 12, -54, -6, -18;
     -36, 72, -36, -36, 72, -54, -36, 18, 18, 54;
     -60, 144, -96, -96, 144, -132, -60, 108, 12, 72;
     12, -108, 84, 84, -72, 120, 48, -72, -24, -36;
     -12, -36, 60, -12, 0, 60, 24, 0, -12, -36;
     48, -36, 12, 48, -72, 30, 48, -54, 30, -18;
     48, 0, 12, 12, -36, 12, 12, 0, 12, -36;
     -12, 108, -48, -48, 72, -102, -48, 54, 42, 18;
     -12, 72, -48, -12, 72, -84, -48, 36, -12, 72;
     -24, 144, -96, -60, 108, -168, -60, 72, 48, 72;
     60, -180, 132, 96, -144, 204, 96, -108, -12, -108;
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
theorem pair24_00_07_certificate :
    pair24_00_07Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_00_07Rows id +
      pair24_00_07Inverse * integerInformationSelector pair24_00_07Free = (36 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_00_07_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_00_07Inverse.mulVec (fun t => if b t then 1 else -1) k = 36 ∨
      pair24_00_07Inverse.mulVec (fun t => if b t then 1 else -1) k = -36) →
    IntegerScaledHalfPattern 36 (1)
      (∑ k, encodedIntFrame base24Masks 0 k * pair24_00_07Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 7 k * pair24_00_07Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_00_07_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {0, 7} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 0 k * x k) (∑ k, base24Frame 7 k * x k) := by
  have h := order24_integer_pair_lift 0 7 pair24_00_07Rows pair24_00_07Free
    pair24_00_07Left pair24_00_07Inverse 36 (1) (by norm_num) (by decide +kernel)
    pair24_00_07_certificate pair24_00_07_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
