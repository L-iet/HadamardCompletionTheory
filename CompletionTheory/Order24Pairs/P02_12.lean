/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P02_08
@[expose] public section
namespace CompletionTheory

def pair24_02_12Rows : Fin 14 → Fin 16 := ![0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15]
def pair24_02_12Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_02_12Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![0, 1, 4, 1, 5, 5, -2, -7, -10, 8, 5, 1, -11, 12;
     2, -1, 0, -1, 3, -1, 0, -3, -2, 2, 1, -1, -3, 4;
     -1, 2, 0, 2, 0, 2, 0, -3, -5, 2, 1, 2, -6, 4;
     -5, 6, -1, 0, -2, 2, 2, 4, 0, -4, 0, -3, 2, -1;
     3, -2, 1, -2, 2, 2, -2, -4, -4, 2, 2, 1, -2, 3;
     1, 0, 2, 0, 4, 2, -4, -5, -9, 8, 3, 0, -10, 8;
     4, -3, 2, -3, -5, -1, 2, 1, 6, -4, -3, 3, 5, -4;
     8, -7, 0, -1, -3, -1, 0, -3, 4, 2, -5, 5, 3, -2;
     1, 0, -1, 0, -2, -4, 2, 4, 6, -4, 0, -3, 8, -7;
     1, 0, -4, 0, -2, -4, 2, 7, 9, -4, -3, 0, 8, -10;
     -1, 2, -3, 2, 0, -4, 0, 6, 4, -4, -2, -1, 6, -5;
     -7, 8, 0, 2, 0, 2, 0, 3, 1, -4, 1, -4, 0, -2;
     -2, 2, -2, 2, 2, 0, -2, 2, -2, 0, 4, -4, -2, 2;
     8, -8, 2, -2, -2, 0, 2, -2, 2, 0, -4, 4, 2, -2;
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

def pair24_02_12Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![24, -60, 24, 24, -48, 60, 36, -24, 0, -24;
     0, -12, 0, 0, -24, 12, 12, -12, 0, -12;
     12, -24, 24, 12, -12, 24, 12, 0, 0, -12;
     12, 24, 12, 24, 24, -6, 0, 6, 18, 18;
     0, -24, 0, 0, -24, 18, 0, -18, -6, -6;
     24, -48, 12, 12, -48, 48, 24, -12, 0, -24;
     -36, 12, -12, -12, 24, -24, -24, 0, -24, 12;
     -36, -12, -12, -36, 0, -12, -24, 0, -36, -12;
     -12, 36, -24, -12, 24, -42, -12, 6, 6, 18;
     -12, 48, -24, -24, 36, -48, -24, 24, 0, 12;
     0, 36, -12, -12, 24, -30, -12, 18, 18, 6;
     24, 24, 12, 24, 24, 0, 12, 12, 24, 24;
     24, 0, 0, 12, -12, 0, 12, 0, 24, 0;
     -36, -12, -12, -24, 0, -12, -24, -12, -36, -12;
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
theorem pair24_02_12_certificate :
    pair24_02_12Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_02_12Rows id +
      pair24_02_12Inverse * integerInformationSelector pair24_02_12Free = (12 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_02_12_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_02_12Inverse.mulVec (fun t => if b t then 1 else -1) k = 12 ∨
      pair24_02_12Inverse.mulVec (fun t => if b t then 1 else -1) k = -12) →
    IntegerScaledHalfPattern 12 (1)
      (∑ k, encodedIntFrame base24Masks 2 k * pair24_02_12Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 12 k * pair24_02_12Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_02_12_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {2, 12} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 2 k * x k) (∑ k, base24Frame 12 k * x k) := by
  have h := order24_integer_pair_lift 2 12 pair24_02_12Rows pair24_02_12Free
    pair24_02_12Left pair24_02_12Inverse 12 (1) (by norm_num) (by decide +kernel)
    pair24_02_12_certificate pair24_02_12_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
