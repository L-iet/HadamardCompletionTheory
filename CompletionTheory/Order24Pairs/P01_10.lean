/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P01_06
@[expose] public section
namespace CompletionTheory

def pair24_01_10Rows : Fin 14 → Fin 16 := ![0, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15]
def pair24_01_10Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_01_10Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![3, 8, 4, 2, -2, -2, 2, 3, 12, -2, 1, 4, 9, -6;
     3, 2, -2, -2, 6, -6, 2, -3, 2, 0, -1, -4, -1, 4;
     3, 2, -2, 4, -6, 0, 2, -3, -1, -3, 2, 8, -4, -2;
     3, -4, 1, -6, -4, 8, 2, 0, -8, 2, 6, -3, -2, 5;
     3, 2, 1, -4, 4, 4, -4, -6, -6, 4, -2, 1, 0, 3;
     3, 8, -2, 0, -4, -10, -4, 9, 13, -7, 0, 0, 10, -16;
     3, -4, 10, -6, -4, 8, 2, -9, -8, 2, -3, 6, -11, 14;
     3, 2, -2, 4, -6, 0, 2, -3, 8, -12, -7, 8, 5, -2;
     3, -4, 1, 0, 2, -4, 2, 0, -2, 8, 0, -9, 4, -1;
     3, -4, -8, 0, 2, -4, 2, 9, 7, -1, 0, 0, 4, -10;
     3, -4, -5, 4, 6, -6, -4, 6, -4, 0, 2, -1, 2, 1;
     3, -4, 4, -2, 0, 6, -4, -3, -1, 3, 8, -4, -4, -2;
     0, 0, -6, 4, 4, -2, -6, 6, -2, 10, 2, -10, -2, 2;
     0, 0, 6, 2, 2, 8, 6, -6, -10, -4, -8, 4, -10, 10;
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

def pair24_01_10Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-36, 12, -36, -36, 48, -24, 0, 24, -12, 24;
     -12, 12, -12, -12, -24, 0, 24, -12, 12, -12;
     -12, -24, 24, -12, 12, 0, -12, 24, -24, -12;
     12, -24, 12, 48, -24, 6, -24, -30, -18, 6;
     0, -24, 0, 0, -24, 30, 0, -30, 6, 6;
     -24, 48, -60, -60, 48, -48, -24, 60, 0, 24;
     -24, -60, 48, 48, -24, 60, 12, -48, -36, -12;
     -48, 12, 24, -48, 48, 0, -12, 24, -24, -12;
     12, 12, -24, 12, -24, -30, 12, -30, 18, 6;
     12, 48, -24, -24, 12, -48, -24, 24, 0, -12;
     24, 12, -12, -12, -24, -18, -12, 6, 30, -30;
     24, -24, -12, 24, -24, 0, -12, -12, -24, 24;
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
theorem pair24_01_10_certificate :
    pair24_01_10Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_01_10Rows id +
      pair24_01_10Inverse * integerInformationSelector pair24_01_10Free = (36 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_01_10_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_01_10Inverse.mulVec (fun t => if b t then 1 else -1) k = 36 ∨
      pair24_01_10Inverse.mulVec (fun t => if b t then 1 else -1) k = -36) →
    IntegerScaledHalfPattern 36 (1)
      (∑ k, encodedIntFrame base24Masks 1 k * pair24_01_10Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 10 k * pair24_01_10Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_01_10_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {1, 10} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 1 k * x k) (∑ k, base24Frame 10 k * x k) := by
  have h := order24_integer_pair_lift 1 10 pair24_01_10Rows pair24_01_10Free
    pair24_01_10Left pair24_01_10Inverse 36 (1) (by norm_num) (by decide +kernel)
    pair24_01_10_certificate pair24_01_10_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
