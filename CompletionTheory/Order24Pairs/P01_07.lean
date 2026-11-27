/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P01_03
@[expose] public section
namespace CompletionTheory

def pair24_01_07Rows : Fin 14 → Fin 16 := ![0, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15]
def pair24_01_07Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_01_07Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![3, 6, 6, 2, 2, 2, -3, 2, 6, 2, 1, 4, -1, 4;
     3, 0, 0, -2, 10, -2, -9, -8, 6, 4, -1, -4, -11, 14;
     3, 0, 0, 4, -2, 4, -9, -11, 6, 1, 2, 8, -14, 8;
     3, -6, 3, -6, 0, 12, -6, -18, 6, 6, 6, -3, -12, 15;
     3, 6, -3, -4, -4, -4, 6, 14, -12, -4, -2, 1, 20, -17;
     3, 12, -6, 0, -12, -18, 21, 33, -12, -15, 0, 0, 30, -36;
     3, -6, 12, -6, 0, 12, -15, -18, 6, 6, -3, 6, -21, 24;
     3, 0, 0, 4, -2, 4, -9, -2, 6, -8, -7, 8, -5, 8;
     3, -6, 3, 0, 6, 0, -6, -12, 6, 12, 0, -9, -6, 9;
     3, -6, -6, 0, 6, 0, 3, -3, 6, 3, 0, 0, -6, 0;
     3, 0, -9, 4, -2, -14, 18, 16, -12, -8, 2, -1, 22, -19;
     3, 0, 0, -2, -8, -2, 9, 19, -12, -5, 8, -4, 16, -22;
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

def pair24_01_07Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-12, -36, -12, -12, 0, 24, 24, 0, -12, 0;
     12, -36, 12, 12, -72, 48, 48, -36, 12, -36;
     12, -72, 48, 12, -36, 48, 12, 0, -24, -36;
     36, -72, 36, 72, -72, 54, 0, -54, -18, -18;
     -48, 72, -48, -48, 72, -66, -48, 18, 6, 54;
     -72, 144, -108, -108, 144, -144, -72, 108, 0, 72;
     0, -108, 72, 72, -72, 108, 36, -72, -36, -36;
     -24, -36, 48, -24, 0, 48, 12, 0, -24, -36;
     36, -36, 0, 36, -72, 18, 36, -54, 18, -18;
     36, 0, 0, 0, -36, 0, 0, 0, 0, -36;
     -24, 108, -60, -60, 72, -114, -60, 54, 30, 18;
     -24, 72, -60, -24, 72, -96, -60, 36, -24, 72;
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
theorem pair24_01_07_certificate :
    pair24_01_07Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_01_07Rows id +
      pair24_01_07Inverse * integerInformationSelector pair24_01_07Free = (36 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_01_07_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_01_07Inverse.mulVec (fun t => if b t then 1 else -1) k = 36 ∨
      pair24_01_07Inverse.mulVec (fun t => if b t then 1 else -1) k = -36) →
    IntegerScaledHalfPattern 36 (1)
      (∑ k, encodedIntFrame base24Masks 1 k * pair24_01_07Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 7 k * pair24_01_07Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_01_07_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {1, 7} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 1 k * x k) (∑ k, base24Frame 7 k * x k) := by
  have h := order24_integer_pair_lift 1 7 pair24_01_07Rows pair24_01_07Free
    pair24_01_07Left pair24_01_07Inverse 36 (1) (by norm_num) (by decide +kernel)
    pair24_01_07_certificate pair24_01_07_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
