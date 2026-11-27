/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P10_13
@[expose] public section
namespace CompletionTheory

def pair24_11_13Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15]
def pair24_11_13Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_11_13Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![-6, 8, 6, 2, 4, 0, 0, 2, 4, 6, -2, -2, 4, -2;
     10, -8, 0, 0, -4, 4, -4, 0, -6, 0, 4, 2, -2, 4;
     -14, 16, 3, -3, 8, -2, 2, 3, 3, -3, -5, -4, -5, 1;
     8, -6, -3, 1, -6, -4, 4, 1, -1, -3, 1, 6, 1, 1;
     0, 2, 3, -1, -2, 0, 0, -1, 1, 3, -5, -2, 7, -5;
     2, 0, 3, 1, 0, 2, -2, -5, -1, -3, 7, 0, -5, 1;
     -10, 12, 0, 4, 0, -4, 4, 4, 2, 0, -8, -6, -2, 4;
     -14, 16, 0, 0, 8, 4, 8, 0, -6, -12, 4, -10, -14, 16;
     20, -18, -3, 1, -6, -4, -8, 1, -1, 9, 1, 6, 13, -11;
     2, 0, -3, -5, 0, 2, -2, 1, 5, 3, 1, 0, 1, -5;
     4, -2, -3, -3, 2, 4, -4, -3, 3, -3, 1, 2, 1, 1;
     10, -8, -3, 3, -4, -2, 2, -3, -3, 3, 1, 8, 1, -5;
     20, -20, 0, -4, -4, -4, -8, -4, 4, 12, 0, 8, 12, -12;
     -8, 8, 0, 4, 4, 4, 8, 4, -4, -12, 0, -8, -12, 12;
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

def pair24_11_13Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![0, 24, 0, 0, 48, 0, 24, 24, 24, 24;
     -24, -24, -24, -24, -48, 0, 0, -24, -24, -24;
     36, 24, 60, 36, 48, 24, 36, 36, 48, 12;
     -12, -24, -12, 12, -24, -12, -36, -24, -36, 0;
     -12, 24, -12, -12, 24, -12, -12, 0, 12, 24;
     12, -24, -12, -12, -24, 24, 12, 12, 0, -12;
     0, 24, 48, 48, 48, 24, 24, 0, 24, 24;
     48, -24, 96, 48, 0, 96, 72, 0, 48, -24;
     -60, 0, -84, -60, -24, -84, -60, -24, -60, 0;
     12, 24, -12, -12, 0, -24, -12, 12, 0, -12;
     12, 0, -12, -12, -24, -12, -12, 0, 12, -24;
     -12, -24, -36, -12, -24, -24, -36, -12, -48, 12;
     -48, 0, -96, -72, -24, -96, -72, 0, -48, 0;
     24, -24, 72, 48, 0, 72, 48, -24, 24, -24;
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
theorem pair24_11_13_certificate :
    pair24_11_13Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_11_13Rows id +
      pair24_11_13Inverse * integerInformationSelector pair24_11_13Free = (24 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_11_13_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_11_13Inverse.mulVec (fun t => if b t then 1 else -1) k = 24 ∨
      pair24_11_13Inverse.mulVec (fun t => if b t then 1 else -1) k = -24) →
    IntegerScaledHalfPattern 24 (1)
      (∑ k, encodedIntFrame base24Masks 11 k * pair24_11_13Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 13 k * pair24_11_13Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_11_13_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {11, 13} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 11 k * x k) (∑ k, base24Frame 13 k * x k) := by
  have h := order24_integer_pair_lift 11 13 pair24_11_13Rows pair24_11_13Free
    pair24_11_13Left pair24_11_13Inverse 24 (1) (by norm_num) (by decide +kernel)
    pair24_11_13_certificate pair24_11_13_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
