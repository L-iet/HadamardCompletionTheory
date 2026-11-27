/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P02_07
@[expose] public section
namespace CompletionTheory

def pair24_02_11Rows : Fin 14 → Fin 16 := ![0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15]
def pair24_02_11Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_02_11Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![15, -14, 4, -4, 0, 0, -2, -7, 0, 8, 5, 6, -1, 2;
     5, -4, 0, -2, 2, -2, 0, -3, 0, 2, 1, 0, -1, 2;
     2, -1, 0, 1, -1, 1, 0, -3, -3, 2, 1, 3, -4, 2;
     -5, 6, -1, 0, -2, 2, 2, 4, 0, -4, 0, -3, 2, -1;
     9, -8, 1, -4, 0, 0, -2, -4, 0, 2, 2, 3, 2, -1;
     10, -9, 2, -3, 1, -1, -4, -5, -3, 8, 3, 3, -4, 2;
     -5, 6, 2, 0, -2, 2, 2, 1, 0, -4, -3, 0, -1, 2;
     -7, 8, 0, 4, 2, 4, 0, -3, -6, 2, -5, 0, -7, 8;
     1, 0, -1, 0, -2, -4, 2, 4, 6, -4, 0, -3, 8, -7;
     -8, 9, -4, 3, 1, -1, 2, 7, 3, -4, -3, -3, 2, -4;
     -7, 8, -3, 4, 2, -2, 0, 6, 0, -4, -2, -3, 2, -1;
     -4, 5, 0, 1, -1, 1, 0, 3, 3, -4, 1, -3, 2, -4;
     10, -10, -2, -2, -2, -4, -2, 2, 6, 0, 4, 0, 6, -6;
     -4, 4, 2, 2, 2, 4, 2, -2, -6, 0, -4, 0, -6, 6;
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

def pair24_02_11Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-36, -60, -36, -36, -48, 0, -24, -24, -60, -24;
     -12, -12, -12, -12, -24, 0, 0, -12, -12, -12;
     0, -24, 12, 0, -12, 12, 0, 0, -12, -12;
     12, 24, 12, 24, 24, -6, 0, 6, 18, 18;
     -24, -24, -24, -24, -24, -6, -24, -18, -30, -6;
     -12, -48, -24, -24, -48, 12, -12, -12, -36, -24;
     0, 12, 24, 24, 24, 12, 12, 0, 12, 12;
     24, -12, 48, 24, 0, 48, 36, 0, 24, -12;
     -12, 36, -24, -12, 24, -42, -12, 6, 6, 18;
     24, 48, 12, 12, 36, -12, 12, 24, 36, 12;
     24, 36, 12, 12, 24, -6, 12, 18, 42, 6;
     12, 24, 0, 12, 24, -12, 0, 12, 12, 24;
     -24, 0, -48, -36, -12, -48, -36, 0, -24, 0;
     12, -12, 36, 24, 0, 36, 24, -12, 12, -12;
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
theorem pair24_02_11_certificate :
    pair24_02_11Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_02_11Rows id +
      pair24_02_11Inverse * integerInformationSelector pair24_02_11Free = (12 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_02_11_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_02_11Inverse.mulVec (fun t => if b t then 1 else -1) k = 12 ∨
      pair24_02_11Inverse.mulVec (fun t => if b t then 1 else -1) k = -12) →
    IntegerScaledHalfPattern 12 (1)
      (∑ k, encodedIntFrame base24Masks 2 k * pair24_02_11Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 11 k * pair24_02_11Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_02_11_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {2, 11} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 2 k * x k) (∑ k, base24Frame 11 k * x k) := by
  have h := order24_integer_pair_lift 2 11 pair24_02_11Rows pair24_02_11Free
    pair24_02_11Left pair24_02_11Inverse 12 (1) (by norm_num) (by decide +kernel)
    pair24_02_11_certificate pair24_02_11_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
