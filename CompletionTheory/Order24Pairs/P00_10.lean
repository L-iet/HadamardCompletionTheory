/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P00_09
@[expose] public section
namespace CompletionTheory

def pair24_00_10Rows : Fin 14 → Fin 16 := ![1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15]
def pair24_00_10Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_00_10Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![3, 8, 4, 3, -1, -1, 2, 3, 10, -1, 0, 3, 7, -4;
     3, 2, -2, -1, 7, -5, 2, -3, 0, 1, -2, -5, -3, 6;
     3, 2, -2, 5, -5, 1, 2, -3, -3, -2, 1, 7, -6, 0;
     3, -4, 1, -5, -3, 9, 2, 0, -10, 3, 5, -4, -4, 7;
     3, 2, 1, -3, 5, 5, -4, -6, -8, 5, -3, 0, -2, 5;
     3, 8, -2, 1, -3, -9, -4, 9, 11, -6, -1, -1, 8, -14;
     3, -4, 10, -5, -3, 9, 2, -9, -10, 3, -4, 5, -13, 16;
     3, 2, -2, 5, -5, 1, 2, -3, 6, -11, -8, 7, 3, 0;
     3, -4, 1, 1, 3, -3, 2, 0, -4, 9, -1, -10, 2, 1;
     3, -4, -8, 1, 3, -3, 2, 9, 5, 0, -1, -1, 2, -8;
     3, -4, -5, 5, 7, -5, -4, 6, -6, 1, 1, -2, 0, 3;
     3, -4, 4, -1, 1, 7, -4, -3, -3, 4, 7, -5, -6, 0;
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

def pair24_00_10Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-24, 12, -24, -24, 48, -12, 12, 24, 0, 24;
     0, 12, 0, 0, -24, 12, 36, -12, 24, -12;
     0, -24, 36, 0, 12, 12, 0, 24, -12, -12;
     24, -24, 24, 60, -24, 18, -12, -30, -6, 6;
     12, -24, 12, 12, -24, 42, 12, -30, 18, 6;
     -12, 48, -48, -48, 48, -36, -12, 60, 12, 24;
     -12, -60, 60, 60, -24, 72, 24, -48, -24, -12;
     -36, 12, 36, -36, 48, 12, 0, 24, -12, -12;
     24, 12, -12, 24, -24, -18, 24, -30, 30, 6;
     24, 48, -12, -12, 12, -36, -12, 24, 12, -12;
     36, 12, 0, 0, -24, -6, 0, 6, 42, -30;
     36, -24, 0, 36, -24, 12, 0, -12, -12, 24;
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
theorem pair24_00_10_certificate :
    pair24_00_10Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_00_10Rows id +
      pair24_00_10Inverse * integerInformationSelector pair24_00_10Free = (36 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_00_10_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_00_10Inverse.mulVec (fun t => if b t then 1 else -1) k = 36 ∨
      pair24_00_10Inverse.mulVec (fun t => if b t then 1 else -1) k = -36) →
    IntegerScaledHalfPattern 36 (1)
      (∑ k, encodedIntFrame base24Masks 0 k * pair24_00_10Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 10 k * pair24_00_10Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_00_10_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {0, 10} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 0 k * x k) (∑ k, base24Frame 10 k * x k) := by
  have h := order24_integer_pair_lift 0 10 pair24_00_10Rows pair24_00_10Free
    pair24_00_10Left pair24_00_10Inverse 36 (1) (by norm_num) (by decide +kernel)
    pair24_00_10_certificate pair24_00_10_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
