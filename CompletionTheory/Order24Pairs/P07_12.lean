/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P07_08
@[expose] public section
namespace CompletionTheory

def pair24_07_12Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 13, 14, 15]
def pair24_07_12Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_07_12Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![0, 1, 2, 2, 1, 1, 1, -1, 0, 2, 1, 1, -1, 2;
     2, -1, 0, 0, -1, 3, -1, -3, -2, 2, 1, -1, -3, 4;
     -1, 2, 0, 0, 2, 0, 2, -3, -5, 2, 1, 2, -6, 4;
     -5, 6, -2, 1, 0, 2, 6, -2, -10, 2, 4, -3, -8, 9;
     3, -2, 2, -1, -2, -2, -2, 2, 6, -4, -2, 1, 8, -7;
     1, 0, 4, -2, 0, -4, -6, 7, 11, -4, -5, 0, 10, -12;
     4, -3, -2, 4, -3, -1, 3, -5, -4, 2, 1, 3, -5, 6;
     8, -7, 0, 0, -1, -3, -1, -3, 4, 2, -5, 5, 3, -2;
     1, 0, -2, 1, 0, 2, 0, -2, -4, 2, 4, -3, -2, 3;
     1, 0, -2, -2, 0, 2, 0, 1, -1, 2, 1, 0, -2, 0;
     -1, 2, 0, -3, 2, 0, -4, 6, 4, -4, -2, -1, 6, -5;
     -7, 8, 0, 0, 2, 0, 2, 3, 1, -4, 1, -4, 0, -2;
     -2, 2, 2, -4, 2, -2, -4, 8, 8, -6, 0, -4, 8, -8;
     8, -8, -2, 4, -2, 2, 4, -8, -8, 6, 0, 4, -8, 8;
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

def pair24_07_12Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![0, -12, 0, 0, 0, 12, 12, 0, 0, 0;
     0, -12, 0, 0, -24, 12, 12, -12, 0, -12;
     12, -24, 24, 12, -12, 24, 12, 0, 0, -12;
     36, -24, 36, 48, -24, 42, 24, -18, 18, -6;
     -24, 24, -24, -24, 24, -30, -24, 6, -6, 18;
     -24, 48, -36, -36, 48, -48, -24, 36, 0, 24;
     -12, -36, 12, 12, -24, 24, 0, -24, -24, -12;
     -36, -12, -12, -36, 0, -12, -24, 0, -36, -12;
     12, -12, 0, 12, -24, 6, 12, -18, 6, -6;
     12, 0, 0, 0, -12, 0, 0, 0, 0, -12;
     0, 36, -12, -12, 24, -30, -12, 18, 18, 6;
     24, 24, 12, 24, 24, 0, 12, 12, 24, 24;
     0, 48, -24, -12, 36, -48, -12, 24, 24, 24;
     -12, -60, 12, 0, -48, 36, 0, -36, -36, -36;
     12, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 12, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 12, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 12, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 12, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 12, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 12, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 12, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 12, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 12]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_07_12_certificate :
    pair24_07_12Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_07_12Rows id +
      pair24_07_12Inverse * integerInformationSelector pair24_07_12Free = (12 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_07_12_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_07_12Inverse.mulVec (fun t => if b t then 1 else -1) k = 12 ∨
      pair24_07_12Inverse.mulVec (fun t => if b t then 1 else -1) k = -12) →
    IntegerScaledHalfPattern 12 (1)
      (∑ k, encodedIntFrame base24Masks 7 k * pair24_07_12Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 12 k * pair24_07_12Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_07_12_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {7, 12} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 7 k * x k) (∑ k, base24Frame 12 k * x k) := by
  have h := order24_integer_pair_lift 7 12 pair24_07_12Rows pair24_07_12Free
    pair24_07_12Left pair24_07_12Inverse 12 (1) (by norm_num) (by decide +kernel)
    pair24_07_12_certificate pair24_07_12_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
