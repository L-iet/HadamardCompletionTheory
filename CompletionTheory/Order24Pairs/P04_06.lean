/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P03_13
@[expose] public section
namespace CompletionTheory

def pair24_04_06Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def pair24_04_06Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_04_06Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![3, -2, 2, 2, 0, 0, -1, 2, 2, 0, 1, 2, 1, 0;
     -1, 2, 0, 0, 4, 0, -3, -4, 2, 2, -1, -2, -5, 6;
     5, -4, 0, 0, -2, 0, -3, -1, 2, -1, 2, 4, -2, 0;
     -5, 6, 1, -2, -4, 3, 7, 5, -7, -2, 0, -3, 7, -6;
     -3, 4, 2, -1, 0, 0, 2, 2, -4, 0, -2, -1, 4, -3;
     1, 0, 1, 1, 2, -3, -2, -4, 5, 1, 0, 0, -5, 3;
     -5, 6, 1, 1, -4, 3, 4, 5, -7, -2, -3, 0, 4, -3;
     5, -4, 0, 0, -2, 0, -3, 2, 2, -4, -1, 4, 1, 0;
     1, 0, -2, 1, 2, 0, -2, -4, 2, 4, 0, -3, -2, 3;
     1, 0, -2, -2, 2, 0, 1, -1, 2, 1, 0, 0, -2, 0;
     5, -4, -3, 0, 4, -3, -3, -7, 5, 2, 2, 1, -5, 6;
     -1, 2, 0, 0, -2, 0, 3, 5, -4, -1, 2, -2, 4, -6;
     4, -4, -1, -1, 2, -3, -1, -3, 3, 4, 2, -2, -3, 3;
     2, -2, 1, 1, -2, 3, 1, 3, -3, -4, -2, 2, 3, -3;
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

def pair24_04_06Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-12, -12, -12, -12, 0, 0, 0, 0, -12, 0;
     12, -12, 12, 12, -24, 24, 24, -12, 12, -12;
     -12, -24, 0, -12, -12, 0, -12, 0, -24, -12;
     0, 48, 0, 12, 48, -30, -12, 18, 18, 30;
     0, 24, 0, 0, 24, -6, 0, 6, 18, 18;
     12, -24, 0, 0, -24, 24, 12, 0, 0, -12;
     -12, 36, 12, 12, 48, -12, 0, 12, 12, 24;
     -24, -12, 0, -24, 0, 0, -12, 0, -24, -12;
     12, -12, 0, 12, -24, 6, 12, -18, 6, -6;
     12, 0, 0, 0, -12, 0, 0, 0, 0, -12;
     12, -36, 0, 0, -48, 18, 0, -18, -6, -30;
     0, 24, -12, 0, 24, -24, -12, 12, 0, 24;
     12, -24, -12, 0, -36, 0, 0, -12, 0, -12;
     -24, 12, 0, -12, 24, -12, -12, 0, -12, 0;
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
theorem pair24_04_06_certificate :
    pair24_04_06Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_04_06Rows id +
      pair24_04_06Inverse * integerInformationSelector pair24_04_06Free = (12 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_04_06_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_04_06Inverse.mulVec (fun t => if b t then 1 else -1) k = 12 ∨
      pair24_04_06Inverse.mulVec (fun t => if b t then 1 else -1) k = -12) →
    IntegerScaledHalfPattern 12 (-1)
      (∑ k, encodedIntFrame base24Masks 4 k * pair24_04_06Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 6 k * pair24_04_06Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_04_06_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {4, 6} x →
    HalfCorrelationPattern 24 (rationalRealCast (-1))
      (∑ k, base24Frame 4 k * x k) (∑ k, base24Frame 6 k * x k) := by
  have h := order24_integer_pair_lift 4 6 pair24_04_06Rows pair24_04_06Free
    pair24_04_06Left pair24_04_06Inverse 12 (-1) (by norm_num) (by decide +kernel)
    pair24_04_06_certificate pair24_04_06_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
