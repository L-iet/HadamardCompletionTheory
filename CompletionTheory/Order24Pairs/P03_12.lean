/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P03_08
@[expose] public section
namespace CompletionTheory

def pair24_03_12Rows : Fin 14 → Fin 16 := ![0, 1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15]
def pair24_03_12Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_03_12Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![0, 1, 4, 1, -3, -3, 2, 5, 10, -4, -3, 1, 9, -8;
     2, -1, 0, -1, 3, -1, 0, -3, -2, 2, 1, -1, -3, 4;
     -1, 2, 0, 2, 0, 2, 0, -3, -5, 2, 1, 2, -6, 4;
     -5, 6, -1, 0, 0, 4, 1, 1, -5, -1, 2, -3, -3, 4;
     3, -2, 1, -2, 0, 0, -1, -1, 1, -1, 0, 1, 3, -2;
     1, 0, 2, 0, 0, -2, -2, 1, 1, 2, -1, 0, 0, -2;
     4, -3, 2, -3, -9, -5, 4, 7, 16, -10, -7, 3, 15, -14;
     8, -7, 0, -1, -3, -1, 0, -3, 4, 2, -5, 5, 3, -2;
     1, 0, -1, 0, 0, -2, 1, 1, 1, -1, 2, -3, 3, -2;
     1, 0, -4, 0, 6, 4, -2, -5, -11, 8, 5, 0, -12, 10;
     -1, 2, -3, 2, 6, 2, -3, -3, -11, 5, 4, -1, -9, 10;
     -7, 8, 0, 2, 0, 2, 0, 3, 1, -4, 1, -4, 0, -2;
     -2, 2, -2, 2, 6, 4, -4, -4, -12, 6, 8, -4, -12, 12;
     8, -8, 2, -2, -6, -4, 4, 4, 12, -6, -8, 4, 12, -12;
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

def pair24_03_12Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-24, 36, -24, -24, 48, -36, -12, 24, 0, 24;
     0, -12, 0, 0, -24, 12, 12, -12, 0, -12;
     12, -24, 24, 12, -12, 24, 12, 0, 0, -12;
     24, 0, 24, 36, 0, 18, 12, -6, 18, 6;
     -12, 0, -12, -12, 0, -6, -12, -6, -6, 6;
     0, 0, -12, -12, 0, 0, 0, 12, 0, 0;
     -60, 60, -36, -36, 72, -72, -48, 24, -24, 36;
     -36, -12, -12, -36, 0, -12, -24, 0, -36, -12;
     0, 12, -12, 0, 0, -18, 0, -6, 6, 6;
     36, -48, 24, 24, -60, 48, 24, -24, 0, -36;
     36, -36, 24, 24, -48, 42, 24, -18, 18, -30;
     24, 24, 12, 24, 24, 0, 12, 12, 24, 24;
     48, -48, 24, 36, -60, 48, 36, -24, 24, -24;
     -60, 36, -36, -48, 48, -60, -48, 12, -36, 12;
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
theorem pair24_03_12_certificate :
    pair24_03_12Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_03_12Rows id +
      pair24_03_12Inverse * integerInformationSelector pair24_03_12Free = (12 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_03_12_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_03_12Inverse.mulVec (fun t => if b t then 1 else -1) k = 12 ∨
      pair24_03_12Inverse.mulVec (fun t => if b t then 1 else -1) k = -12) →
    IntegerScaledHalfPattern 12 (1)
      (∑ k, encodedIntFrame base24Masks 3 k * pair24_03_12Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 12 k * pair24_03_12Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_03_12_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {3, 12} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 3 k * x k) (∑ k, base24Frame 12 k * x k) := by
  have h := order24_integer_pair_lift 3 12 pair24_03_12Rows pair24_03_12Free
    pair24_03_12Left pair24_03_12Inverse 12 (1) (by norm_num) (by decide +kernel)
    pair24_03_12_certificate pair24_03_12_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
