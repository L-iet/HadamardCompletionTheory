/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P07_11
@[expose] public section
namespace CompletionTheory

def pair24_07_15Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14]
def pair24_07_15Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_07_15Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![6, -4, 4, 4, 0, 0, 0, -2, 4, 4, 0, 2, 4, 2;
     16, -14, 0, 0, -6, 2, -6, -6, 4, 4, -2, 4, 2, 2;
     10, -8, 0, 0, 0, -4, 0, -6, -2, 4, -2, 4, 8, -4;
     17, -15, -4, 2, -9, -5, 3, -4, -2, 4, -1, 9, 3, 2;
     -15, 17, 4, -2, 3, 3, 3, 4, -2, -8, 3, -7, -5, 2;
     -34, 36, 8, -4, 12, 4, 0, 14, -2, -8, 2, -12, -12, -4;
     26, -24, -4, 8, -12, -8, 0, -10, 4, 4, -4, 6, 12, 2;
     10, -8, 0, 0, 0, -4, 0, -6, 4, 4, -8, -2, 8, 2;
     11, -9, -4, 2, -3, 1, -3, -4, -2, 4, 5, 3, -3, 2;
     2, 0, -4, -4, 0, 4, 0, 2, -2, 4, 2, 0, 0, -4;
     -17, 19, 0, -6, 9, 5, -3, 12, -2, -8, 1, -5, -7, 2;
     -20, 22, 0, 0, 6, 2, 6, 6, -2, -8, 4, -2, -10, -4;
     -28, 28, 4, -8, 12, 4, 0, 16, 0, -12, 8, -8, -16, 0;
     40, -40, -4, 8, -12, -4, 0, -16, 0, 12, -8, 8, 16, 0;
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

def pair24_07_15Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-24, -24, -24, -24, 0, 0, 0, 0, -24, 0;
     -48, -24, -48, -48, -48, -24, -24, -24, -48, -24;
     -24, -48, 0, -24, -24, 0, -24, 0, -48, -24;
     -36, -48, -36, -12, -48, -24, -60, -36, -72, -12;
     36, 48, 36, 36, 48, 24, 36, 12, 72, 36;
     96, 96, 72, 72, 96, 48, 96, 72, 144, 48;
     -96, -72, -48, -48, -48, -24, -72, -48, -120, -24;
     -48, -24, 0, -48, 0, 0, -24, 0, -48, -24;
     -12, -24, -36, -12, -48, -24, -12, -36, -24, -12;
     24, 0, 0, 0, -24, 0, 0, 0, 0, -24;
     60, 72, 36, 36, 48, 0, 36, 36, 96, 12;
     72, 48, 48, 72, 48, 24, 48, 24, 72, 48;
     96, 96, 48, 72, 72, 0, 72, 48, 144, 48;
     -120, -120, -72, -96, -96, -24, -96, -72, -168, -72;
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
theorem pair24_07_15_certificate :
    pair24_07_15Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_07_15Rows id +
      pair24_07_15Inverse * integerInformationSelector pair24_07_15Free = (24 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_07_15_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_07_15Inverse.mulVec (fun t => if b t then 1 else -1) k = 24 ∨
      pair24_07_15Inverse.mulVec (fun t => if b t then 1 else -1) k = -24) →
    IntegerScaledHalfPattern 24 (-1)
      (∑ k, encodedIntFrame base24Masks 7 k * pair24_07_15Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 15 k * pair24_07_15Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_07_15_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {7, 15} x →
    HalfCorrelationPattern 24 (rationalRealCast (-1))
      (∑ k, base24Frame 7 k * x k) (∑ k, base24Frame 15 k * x k) := by
  have h := order24_integer_pair_lift 7 15 pair24_07_15Rows pair24_07_15Free
    pair24_07_15Left pair24_07_15Inverse 24 (-1) (by norm_num) (by decide +kernel)
    pair24_07_15_certificate pair24_07_15_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
