/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P05_09
@[expose] public section
namespace CompletionTheory

def pair24_05_13Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 14, 15]
def pair24_05_13Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_05_13Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![-6, 8, 6, 2, 4, 0, 2, 4, 6, -2, 0, -2, 4, -2;
     10, -8, 2, -2, -4, -8, 2, 0, 10, -2, -4, 2, 8, -6;
     -14, 16, 2, -2, 8, 4, 2, 0, -8, -2, 2, -4, -10, 6;
     8, -6, -5, 3, -6, 8, -1, -7, -13, 7, 4, 6, -9, 11;
     0, 2, 3, -1, -2, 0, -1, 1, 3, -5, 0, -2, 7, -5;
     2, 0, 4, 0, 0, -4, -4, 2, 2, 4, -2, 0, 0, -4;
     -10, 12, -2, 6, 0, 8, 2, -4, -10, -2, 4, -6, -12, 14;
     -14, 16, 2, -2, 8, 4, 2, 0, -2, -2, -4, -10, -4, 6;
     20, -18, -5, 3, -6, -4, -1, -7, -1, 7, 4, 6, 3, -1;
     2, 0, -2, -6, 0, -4, 2, 8, 8, -2, -2, 0, 6, -10;
     4, -2, -1, -5, 2, -8, -1, 9, 7, -5, -4, 2, 11, -9;
     10, -8, -4, 4, -4, 4, -4, -6, -2, 4, 2, 8, -4, 0;
     20, -20, -2, -2, -4, -4, -6, -2, 2, 6, 4, 8, 2, -2;
     -8, 8, 2, 2, 4, 4, 6, 2, -2, -6, -4, -8, -2, 2;
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

def pair24_05_13Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![0, 24, 0, 0, 48, 0, 24, 24, 24, 24;
     -48, 24, -48, -48, 0, -48, -24, 0, -24, 0;
     48, 0, 72, 48, 24, 48, 48, 24, 48, 0;
     12, -72, 12, 36, -72, 36, -12, -48, -36, -24;
     -12, 24, -12, -12, 24, -12, -12, 0, 12, 24;
     0, 0, -24, -24, 0, 0, 0, 24, 0, 0;
     24, -24, 72, 72, 0, 72, 48, -24, 24, 0;
     24, 24, 72, 24, 48, 48, 48, 24, 48, 0;
     -36, -48, -60, -36, -72, -36, -36, -48, -60, -24;
     0, 48, -24, -24, 24, -48, -24, 24, 0, 0;
     -12, 48, -36, -36, 24, -60, -36, 24, 12, 0;
     0, -48, -24, 0, -48, 0, -24, -24, -48, 0;
     -24, -48, -72, -48, -72, -48, -48, -24, -48, -24;
     0, 24, 48, 24, 48, 24, 24, 0, 24, 0;
     24, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 24, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 24, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 24, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 24, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 24, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 24, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 24, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 24, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 24]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_05_13_certificate :
    pair24_05_13Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_05_13Rows id +
      pair24_05_13Inverse * integerInformationSelector pair24_05_13Free = (24 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_05_13_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_05_13Inverse.mulVec (fun t => if b t then 1 else -1) k = 24 ∨
      pair24_05_13Inverse.mulVec (fun t => if b t then 1 else -1) k = -24) →
    IntegerScaledHalfPattern 24 (-1)
      (∑ k, encodedIntFrame base24Masks 5 k * pair24_05_13Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 13 k * pair24_05_13Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_05_13_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {5, 13} x →
    HalfCorrelationPattern 24 (rationalRealCast (-1))
      (∑ k, base24Frame 5 k * x k) (∑ k, base24Frame 13 k * x k) := by
  have h := order24_integer_pair_lift 5 13 pair24_05_13Rows pair24_05_13Free
    pair24_05_13Left pair24_05_13Inverse 24 (-1) (by norm_num) (by decide +kernel)
    pair24_05_13_certificate pair24_05_13_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
