/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P00_01
@[expose] public section
namespace CompletionTheory

def pair24_00_02Rows : Fin 14 → Fin 16 := ![1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def pair24_00_02Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_00_02Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![3, 12, 3, 15, 15, -6, -21, -30, 24, 15, 0, 3, -33, 36;
     3, 0, -1, 11, -1, 0, -9, -10, 6, 5, -2, -5, -13, 16;
     3, 0, 5, -1, 5, 0, -9, -13, 6, 2, 1, 7, -16, 10;
     3, -3, -5, -11, 1, 6, 12, 10, -12, -5, 5, -4, 16, -13;
     3, 3, -3, 9, 9, -6, -12, -18, 6, 9, -3, 0, -12, 15;
     3, 6, 1, 13, 7, -12, -15, -29, 24, 10, -1, -1, -32, 26;
     3, 6, -5, -11, 1, 6, 3, 10, -12, -5, -4, 5, 7, -4;
     3, 0, 5, -1, 5, 0, -9, -4, 6, -7, -8, 7, -7, 10;
     3, -3, 1, -5, -11, 6, 12, 16, -12, 1, -1, -10, 22, -19;
     3, -12, 1, -5, -11, 6, 21, 25, -12, -8, -1, -1, 22, -28;
     3, -9, 5, -1, -13, 0, 18, 14, -12, -7, 1, -2, 20, -17;
     3, 0, -1, -7, -1, 0, 9, 17, -12, -4, 7, -5, 14, -20;
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

def pair24_00_02Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![72, -180, 72, 72, -144, 180, 108, -72, 0, -72;
     24, -36, 24, 24, -72, 60, 60, -36, 24, -36;
     24, -72, 60, 24, -36, 60, 24, 0, -12, -36;
     -24, 72, -24, 12, 72, -78, -60, 18, -6, 54;
     36, -72, 36, 36, -72, 90, 36, -54, 18, -18;
     84, -144, 48, 48, -144, 156, 84, -36, 12, -72;
     -60, 36, 12, 12, 72, -24, -24, 0, -24, 36;
     -12, -36, 60, -12, 0, 60, 24, 0, -12, -36;
     -24, 108, -60, -24, 72, -114, -24, 18, 30, 54;
     -24, 144, -60, -60, 108, -132, -60, 72, 12, 36;
     -12, 108, -48, -48, 72, -102, -48, 54, 42, 18;
     -12, 72, -48, -12, 72, -84, -48, 36, -12, 72;
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
theorem pair24_00_02_certificate :
    pair24_00_02Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_00_02Rows id +
      pair24_00_02Inverse * integerInformationSelector pair24_00_02Free = (36 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_00_02_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_00_02Inverse.mulVec (fun t => if b t then 1 else -1) k = 36 ∨
      pair24_00_02Inverse.mulVec (fun t => if b t then 1 else -1) k = -36) →
    IntegerScaledHalfPattern 36 (1)
      (∑ k, encodedIntFrame base24Masks 0 k * pair24_00_02Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 2 k * pair24_00_02Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_00_02_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {0, 2} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 0 k * x k) (∑ k, base24Frame 2 k * x k) := by
  have h := order24_integer_pair_lift 0 2 pair24_00_02Rows pair24_00_02Free
    pair24_00_02Left pair24_00_02Inverse 36 (1) (by norm_num) (by decide +kernel)
    pair24_00_02_certificate pair24_00_02_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
