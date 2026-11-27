/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P06_08
@[expose] public section
namespace CompletionTheory

def pair24_06_12Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 14, 15]
def pair24_06_12Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_06_12Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![0, 2, 5, 3, 2, 0, 1, 1, 5, 1, 0, 2, 3, -1;
     4, -2, -1, 1, -2, 8, -1, -9, -9, 7, 4, -2, -11, 13;
     -2, 4, 2, -2, 4, -4, 2, 0, 0, -2, -2, 4, -2, -2;
     -10, 12, 2, -4, 0, -8, 6, 14, 10, -14, -4, -6, 14, -12;
     6, -4, 2, 0, -4, 0, -2, -2, 2, -2, 0, 2, 6, -4;
     2, 0, 2, 2, 0, 4, -6, -4, -8, 10, 2, 0, -10, 6;
     8, -6, -1, 5, -6, -8, 3, -1, 7, -5, -4, 6, 5, -3;
     16, -14, -1, 1, -2, -4, -1, -9, 3, 7, -8, 10, 1, 1;
     2, 0, -4, 2, 0, 4, 0, -4, -8, 4, 8, -6, -4, 6;
     2, 0, -4, -4, 0, 4, 0, 2, -2, 4, 2, 0, -4, 0;
     -2, 4, -4, -2, 4, 8, -4, 0, -12, 4, 4, -2, -8, 10;
     -14, 16, 2, -2, 4, -4, 2, 12, 12, -14, -2, -8, 10, -14;
     -4, 4, 0, -4, 4, 4, -4, 4, -4, 0, 8, -8, -4, 4;
     16, -16, 0, 4, -4, -4, 4, -4, 4, 0, -8, 8, 4, -4;
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

def pair24_06_12Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-12, 0, -12, -12, 24, 0, 12, 12, 0, 12;
     12, -48, 12, 12, -72, 48, 36, -36, 0, -36;
     0, 0, 24, 0, 24, 0, 0, 24, 0, 0;
     0, 96, 0, 24, 96, -60, -24, 36, 36, 60;
     -24, 0, -24, -24, 0, -12, -24, -12, -12, 12;
     24, -48, 0, 0, -48, 48, 24, 0, 0, -24;
     -60, 0, -12, -12, 24, -24, -36, -12, -48, 12;
     -60, -48, -12, -60, -24, 0, -36, -12, -72, -36;
     24, -24, 0, 24, -48, 12, 24, -36, 12, -12;
     24, 0, 0, 0, -24, 0, 0, 0, 0, -24;
     48, -24, 24, 24, -48, 36, 24, -12, 36, -36;
     24, 96, 0, 24, 96, -48, 0, 48, 48, 72;
     48, 0, 0, 24, -24, 0, 24, 0, 48, 0;
     -72, -24, -24, -48, 0, -24, -48, -24, -72, -24;
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
theorem pair24_06_12_certificate :
    pair24_06_12Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_06_12Rows id +
      pair24_06_12Inverse * integerInformationSelector pair24_06_12Free = (24 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_06_12_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_06_12Inverse.mulVec (fun t => if b t then 1 else -1) k = 24 ∨
      pair24_06_12Inverse.mulVec (fun t => if b t then 1 else -1) k = -24) →
    IntegerScaledHalfPattern 24 (1)
      (∑ k, encodedIntFrame base24Masks 6 k * pair24_06_12Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 12 k * pair24_06_12Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_06_12_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {6, 12} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 6 k * x k) (∑ k, base24Frame 12 k * x k) := by
  have h := order24_integer_pair_lift 6 12 pair24_06_12Rows pair24_06_12Free
    pair24_06_12Left pair24_06_12Inverse 24 (1) (by norm_num) (by decide +kernel)
    pair24_06_12_certificate pair24_06_12_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
