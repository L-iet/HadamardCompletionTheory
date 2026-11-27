/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P06_09
@[expose] public section
namespace CompletionTheory

def pair24_06_13Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 14, 15]
def pair24_06_13Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_06_13Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![-6, 8, 6, 2, 4, 0, 2, 4, 6, -2, 0, -2, 4, -2;
     10, -8, -2, 2, -4, 8, -2, -12, -10, 10, 4, 2, -12, 14;
     -14, 16, 4, -4, 8, -4, 4, 6, 2, -8, -2, -4, 0, -4;
     8, -6, -1, -1, -6, -8, 3, 5, 7, -5, -4, 6, 11, -9;
     0, 2, 3, -1, -2, 0, -1, 1, 3, -5, 0, -2, 7, -5;
     2, 0, 2, 2, 0, 4, -6, -4, -8, 10, 2, 0, -10, 6;
     -10, 12, 2, 2, 0, -8, 6, 8, 10, -14, -4, -6, 8, -6;
     -14, 16, 4, -4, 8, -4, 4, 6, 8, -8, -8, -10, 6, -4;
     20, -18, -7, 5, -6, 4, -3, -13, -11, 13, 8, 6, -7, 9;
     2, 0, -4, -4, 0, 4, 0, 2, -2, 4, 2, 0, -4, 0;
     4, -2, -5, -1, 2, 8, -5, -3, -13, 7, 4, 2, -9, 11;
     10, -8, -2, 2, -4, -4, -2, 0, 8, -2, -2, 8, 6, -10;
     20, -20, -4, 0, -4, 4, -8, -8, -8, 12, 8, 8, -8, 8;
     -8, 8, 4, 0, 4, -4, 8, 8, 8, -12, -8, -8, 8, -8;
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

def pair24_06_13Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![0, 24, 0, 0, 48, 0, 24, 24, 24, 24;
     0, -72, 0, 0, -96, 48, 24, -48, -24, -48;
     24, 48, 48, 24, 72, 0, 24, 48, 48, 24;
     -36, 24, -36, -12, 24, -60, -60, 0, -36, 24;
     -12, 24, -12, -12, 24, -12, -12, 0, 12, 24;
     24, -48, 0, 0, -48, 48, 24, 0, 0, -24;
     -24, 72, 24, 24, 96, -24, 0, 24, 24, 48;
     0, 72, 48, 0, 96, 0, 24, 48, 48, 24;
     -12, -96, -36, -12, -120, 12, -12, -72, -60, -48;
     24, 0, 0, 0, -24, 0, 0, 0, 0, -24;
     36, -48, 12, 12, -72, 36, 12, -24, 12, -48;
     -24, 0, -48, -24, 0, -48, -48, 0, -48, 24;
     0, -96, -48, -24, -120, 0, -24, -48, -48, -48;
     -24, 72, 24, 0, 96, -24, 0, 24, 24, 24;
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
theorem pair24_06_13_certificate :
    pair24_06_13Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_06_13Rows id +
      pair24_06_13Inverse * integerInformationSelector pair24_06_13Free = (24 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_06_13_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_06_13Inverse.mulVec (fun t => if b t then 1 else -1) k = 24 ∨
      pair24_06_13Inverse.mulVec (fun t => if b t then 1 else -1) k = -24) →
    IntegerScaledHalfPattern 24 (-1)
      (∑ k, encodedIntFrame base24Masks 6 k * pair24_06_13Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 13 k * pair24_06_13Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_06_13_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {6, 13} x →
    HalfCorrelationPattern 24 (rationalRealCast (-1))
      (∑ k, base24Frame 6 k * x k) (∑ k, base24Frame 13 k * x k) := by
  have h := order24_integer_pair_lift 6 13 pair24_06_13Rows pair24_06_13Free
    pair24_06_13Left pair24_06_13Inverse 24 (-1) (by norm_num) (by decide +kernel)
    pair24_06_13_certificate pair24_06_13_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
