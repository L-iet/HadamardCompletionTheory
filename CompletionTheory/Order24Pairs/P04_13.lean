/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P04_09
@[expose] public section
namespace CompletionTheory

def pair24_04_13Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15]
def pair24_04_13Free : Fin 10 → Fin 24 := ![13, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_04_13Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![2, 0, 4, 0, 0, -4, -4, 2, 8, 4, 4, 6, 6, -4;
     2, 0, 0, 4, 8, 4, 4, -10, -12, 4, 0, -6, -14, 16;
     2, 0, 2, -10, -8, -12, -6, 8, 16, -2, 2, 12, 14, -18;
     -4, 6, -1, 5, -2, 12, 9, -1, -11, -5, -4, -6, -7, 9;
     -4, 6, 3, 1, 2, 4, 1, -1, -3, -5, 0, -6, 1, 1;
     2, 0, 4, 0, 0, -4, -4, 2, 2, 4, -2, 0, 0, -4;
     -10, 12, 0, 4, -4, 4, 4, 2, 0, -8, 0, -6, -2, 4;
     2, 0, 0, -8, -4, -8, -8, 2, 12, 4, 0, 6, 10, -8;
     8, -6, -5, 9, 6, 8, 5, -13, -19, 7, 4, -6, -15, 17;
     2, 0, -2, -6, 0, -4, 2, 8, 8, -2, -2, 0, 6, -10;
     8, -6, -3, -5, 2, -8, -5, 5, 3, 1, 0, 6, 7, -5;
     2, 0, -2, 6, 0, 8, 2, -4, -4, -2, -2, 0, -6, 2;
     12, -12, -2, 2, 4, 4, -2, -6, -10, 6, 4, 0, -10, 10;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 2, -2, -4, -4, 2, 6, 10, -6, -4, 0, 10, -10;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def pair24_04_13Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![24, 0, -48, -24, 0, -24, 0, 24, 0, 24;
     -24, -48, 48, 24, -48, 72, 48, -48, 0, -48;
     48, 48, -72, -48, 24, -96, -48, 72, 0, 48;
     -36, -12, 72, 60, 24, 48, 12, -36, 0, -12;
     -12, 12, 24, 12, 24, 24, 12, -12, 24, 12;
     0, 0, -24, -24, 0, 0, 0, 24, 0, 0;
     0, 24, 48, 48, 48, 24, 24, 0, 24, 24;
     48, 24, -48, -48, 0, -48, -24, 48, 0, 24;
     -36, -84, 48, 36, -72, 72, 36, -84, -24, -60;
     0, 48, -24, -24, 24, -48, -24, 24, 0, 0;
     12, 12, -48, -36, -24, -48, -36, 12, 0, -12;
     -24, -24, 24, 24, 0, 24, 0, -24, -24, 0;
     -24, -72, 0, 0, -72, 24, 0, -48, -24, -48;
     24, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 48, -24, -24, 48, -48, -24, 24, 0, 24;
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
theorem pair24_04_13_certificate :
    pair24_04_13Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_04_13Rows id +
      pair24_04_13Inverse * integerInformationSelector pair24_04_13Free = (24 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_04_13_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_04_13Inverse.mulVec (fun t => if b t then 1 else -1) k = 24 ∨
      pair24_04_13Inverse.mulVec (fun t => if b t then 1 else -1) k = -24) →
    IntegerScaledHalfPattern 24 (1)
      (∑ k, encodedIntFrame base24Masks 4 k * pair24_04_13Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 13 k * pair24_04_13Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_04_13_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {4, 13} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 4 k * x k) (∑ k, base24Frame 13 k * x k) := by
  have h := order24_integer_pair_lift 4 13 pair24_04_13Rows pair24_04_13Free
    pair24_04_13Left pair24_04_13Inverse 24 (1) (by norm_num) (by decide +kernel)
    pair24_04_13_certificate pair24_04_13_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
