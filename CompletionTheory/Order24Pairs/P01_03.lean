/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P00_15
@[expose] public section
namespace CompletionTheory

def pair24_01_03Rows : Fin 14 → Fin 16 := ![0, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def pair24_01_03Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_01_03Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![3, 12, 2, -10, -10, 6, 15, 32, -12, -10, 1, 4, 29, -26;
     3, 0, -2, 10, -2, 0, -9, -8, 6, 4, -1, -4, -11, 14;
     3, 0, 4, -2, 4, 0, -9, -11, 6, 1, 2, 8, -14, 8;
     3, -3, -6, -6, 6, 3, 3, -3, -3, 0, 6, -3, 3, 0;
     3, 3, -4, 2, 2, -3, -3, -1, -3, 2, -2, 1, 5, -2;
     3, 6, 0, 0, -6, -6, 3, 3, 6, -3, 0, 0, 0, -6;
     3, 6, -6, -24, -12, 12, 21, 42, -30, -18, -3, 6, 39, -36;
     3, 0, 4, -2, 4, 0, -9, -2, 6, -8, -7, 8, -5, 8;
     3, -3, 0, 0, -6, 3, 3, 3, -3, 6, 0, -9, 9, -6;
     3, -12, 0, 18, 12, -6, -15, -33, 24, 15, 0, 0, -36, 30;
     3, -9, 4, 16, 4, -9, -9, -29, 15, 10, 2, -1, -23, 26;
     3, 0, -2, -8, -2, 0, 9, 19, -12, -5, 8, -4, 16, -22;
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

def pair24_01_03Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-84, 108, -84, -84, 144, -120, -48, 72, -12, 72;
     12, -36, 12, 12, -72, 48, 48, -36, 12, -36;
     12, -72, 48, 12, -36, 48, 12, 0, -24, -36;
     0, 0, 0, 36, 0, -18, -36, -18, -18, 18;
     -12, 0, -12, -12, 0, 6, -12, -18, 6, 18;
     0, 0, -36, -36, 0, 0, 0, 36, 0, 0;
     -144, 180, -72, -72, 216, -180, -108, 72, -36, 108;
     -24, -36, 48, -24, 0, 48, 12, 0, -24, -36;
     0, 36, -36, 0, 0, -54, 0, -18, 18, 18;
     108, -144, 72, 72, -180, 144, 72, -72, 0, -108;
     84, -108, 48, 48, -144, 102, 48, -54, 30, -90;
     -24, 72, -60, -24, 72, -96, -60, 36, -24, 72;
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
theorem pair24_01_03_certificate :
    pair24_01_03Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_01_03Rows id +
      pair24_01_03Inverse * integerInformationSelector pair24_01_03Free = (36 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_01_03_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_01_03Inverse.mulVec (fun t => if b t then 1 else -1) k = 36 ∨
      pair24_01_03Inverse.mulVec (fun t => if b t then 1 else -1) k = -36) →
    IntegerScaledHalfPattern 36 (1)
      (∑ k, encodedIntFrame base24Masks 1 k * pair24_01_03Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 3 k * pair24_01_03Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_01_03_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {1, 3} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 1 k * x k) (∑ k, base24Frame 3 k * x k) := by
  have h := order24_integer_pair_lift 1 3 pair24_01_03Rows pair24_01_03Free
    pair24_01_03Left pair24_01_03Inverse 36 (1) (by norm_num) (by decide +kernel)
    pair24_01_03_certificate pair24_01_03_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
