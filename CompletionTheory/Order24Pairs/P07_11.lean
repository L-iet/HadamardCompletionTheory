/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P06_15
@[expose] public section
namespace CompletionTheory

def pair24_07_11Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 15]
def pair24_07_11Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_07_11Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![3, -2, 2, 2, 0, 0, 0, -1, 2, 2, 1, 2, 1, 0;
     5, -4, 0, 0, -2, 2, -2, -3, 0, 2, 1, 0, -1, 2;
     2, -1, 0, 0, 1, -1, 1, -3, -3, 2, 1, 3, -4, 2;
     7, -6, -2, 1, -4, -2, 2, -2, -2, 2, 4, 1, 0, 1;
     -3, 4, 2, -1, 0, 0, 0, 2, 2, -4, -2, -1, 4, -3;
     -14, 15, 4, -2, 5, 1, -1, 7, 1, -4, -5, -5, 0, -2;
     7, -6, -2, 4, -4, -2, 2, -5, -2, 2, 1, 4, -3, 4;
     -7, 8, 0, 0, 4, 2, 4, -3, -6, 2, -5, 0, -7, 8;
     13, -12, -2, 1, -4, -2, -4, -2, 4, 2, 4, 1, 6, -5;
     4, -3, -2, -2, -1, 1, -1, 1, 1, 2, 1, 1, 0, -2;
     -7, 8, 0, -3, 4, 2, -2, 6, 0, -4, -2, -3, 2, -1;
     -4, 5, 0, 0, 1, -1, 1, 3, 3, -4, 1, -3, 2, -4;
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

def pair24_07_11Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-12, -12, -12, -12, 0, 0, 0, 0, -12, 0;
     -12, -12, -12, -12, -24, 0, 0, -12, -12, -12;
     0, -24, 12, 0, -12, 12, 0, 0, -12, -12;
     -12, -24, -12, 0, -24, -6, -24, -18, -30, -6;
     0, 24, 0, 0, 24, -6, 0, 6, 18, 18;
     36, 48, 24, 24, 48, 12, 36, 36, 60, 24;
     -24, -36, 0, 0, -24, 12, -12, -24, -36, -12;
     24, -12, 48, 24, 0, 48, 36, 0, 24, -12;
     -36, -12, -48, -36, -24, -42, -36, -18, -42, -6;
     0, 0, -12, -12, -12, -12, -12, 0, -12, -12;
     24, 36, 12, 12, 24, -6, 12, 18, 42, 6;
     12, 24, 0, 12, 24, -12, 0, 12, 12, 24;
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
theorem pair24_07_11_certificate :
    pair24_07_11Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_07_11Rows id +
      pair24_07_11Inverse * integerInformationSelector pair24_07_11Free = (12 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_07_11_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_07_11Inverse.mulVec (fun t => if b t then 1 else -1) k = 12 ∨
      pair24_07_11Inverse.mulVec (fun t => if b t then 1 else -1) k = -12) →
    IntegerScaledHalfPattern 12 (1)
      (∑ k, encodedIntFrame base24Masks 7 k * pair24_07_11Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 11 k * pair24_07_11Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_07_11_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {7, 11} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 7 k * x k) (∑ k, base24Frame 11 k * x k) := by
  have h := order24_integer_pair_lift 7 11 pair24_07_11Rows pair24_07_11Free
    pair24_07_11Left pair24_07_11Inverse 12 (1) (by norm_num) (by decide +kernel)
    pair24_07_11_certificate pair24_07_11_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
