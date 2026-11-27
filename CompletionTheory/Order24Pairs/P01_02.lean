/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P00_15
@[expose] public section
namespace CompletionTheory

def pair24_01_02Rows : Fin 14 → Fin 16 := ![0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def pair24_01_02Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_01_02Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![3, 12, 2, 14, 14, -6, -21, -28, 24, 14, 1, 4, -31, 34;
     3, 0, -2, 10, -2, 0, -9, -8, 6, 4, -1, -4, -11, 14;
     3, 0, 4, -2, 4, 0, -9, -11, 6, 1, 2, 8, -14, 8;
     3, -3, -6, -12, 0, 6, 12, 12, -12, -6, 6, -3, 18, -15;
     3, 3, -4, 8, 8, -6, -12, -16, 6, 8, -2, 1, -10, 13;
     3, 6, 0, 12, 6, -12, -15, -27, 24, 9, 0, 0, -30, 24;
     3, 6, -6, -12, 0, 6, 3, 12, -12, -6, -3, 6, 9, -6;
     3, 0, 4, -2, 4, 0, -9, -2, 6, -8, -7, 8, -5, 8;
     3, -3, 0, -6, -12, 6, 12, 18, -12, 0, 0, -9, 24, -21;
     3, -12, 0, -6, -12, 6, 21, 27, -12, -9, 0, 0, 24, -30;
     3, -9, 4, -2, -14, 0, 18, 16, -12, -8, 2, -1, 22, -19;
     3, 0, -2, -8, -2, 0, 9, 19, -12, -5, 8, -4, 16, -22;
     0, -6, 4, 4, -2, -6, 6, -2, 0, 10, 2, -10, -2, 2;
     0, 6, 2, 2, 8, 6, -6, -10, 0, -4, -8, 4, -10, 10;
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

def pair24_01_02Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![60, -180, 60, 60, -144, 168, 96, -72, -12, -72;
     12, -36, 12, 12, -72, 48, 48, -36, 12, -36;
     12, -72, 48, 12, -36, 48, 12, 0, -24, -36;
     -36, 72, -36, 0, 72, -90, -72, 18, -18, 54;
     24, -72, 24, 24, -72, 78, 24, -54, 6, -18;
     72, -144, 36, 36, -144, 144, 72, -36, 0, -72;
     -72, 36, 0, 0, 72, -36, -36, 0, -36, 36;
     -24, -36, 48, -24, 0, 48, 12, 0, -24, -36;
     -36, 108, -72, -36, 72, -126, -36, 18, 18, 54;
     -36, 144, -72, -72, 108, -144, -72, 72, 0, 36;
     -24, 108, -60, -60, 72, -114, -60, 54, 30, 18;
     -24, 72, -60, -24, 72, -96, -60, 36, -24, 72;
     48, 0, -24, 12, -36, -24, 12, 0, 48, 0;
     -12, -36, 60, 24, 0, 60, 24, -36, -12, -36;
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
theorem pair24_01_02_certificate :
    pair24_01_02Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_01_02Rows id +
      pair24_01_02Inverse * integerInformationSelector pair24_01_02Free = (36 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_01_02_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_01_02Inverse.mulVec (fun t => if b t then 1 else -1) k = 36 ∨
      pair24_01_02Inverse.mulVec (fun t => if b t then 1 else -1) k = -36) →
    IntegerScaledHalfPattern 36 (1)
      (∑ k, encodedIntFrame base24Masks 1 k * pair24_01_02Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 2 k * pair24_01_02Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_01_02_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {1, 2} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 1 k * x k) (∑ k, base24Frame 2 k * x k) := by
  have h := order24_integer_pair_lift 1 2 pair24_01_02Rows pair24_01_02Free
    pair24_01_02Left pair24_01_02Inverse 36 (1) (by norm_num) (by decide +kernel)
    pair24_01_02_certificate pair24_01_02_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
