/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P04_12
@[expose] public section
namespace CompletionTheory

def pair24_05_06Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def pair24_05_06Free : Fin 10 → Fin 24 := ![13, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_05_06Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![-3, 4, 3, 1, 2, 1, 2, 3, -1, 0, -1, 0, 2, -1;
     -15, 16, 5, -1, 6, 9, 8, 5, -13, -6, -11, -4, 4, -3;
     9, -8, -2, 0, -2, -4, -7, -5, 8, 3, 6, 4, -6, 4;
     15, -14, -5, 0, -8, -7, -7, -5, 11, 6, 12, 1, -3, 4;
     -3, 4, 2, -1, 0, 0, 2, 2, -4, 0, -2, -1, 4, -3;
     -3, 4, 3, 1, 2, 1, 2, 0, -1, -3, -4, 0, -1, -1;
     9, -8, -4, 2, -6, -6, -7, -4, 8, 6, 7, 2, -5, 6;
     3, -2, -1, -1, 0, -3, -4, -1, 5, 0, 1, 2, -2, 3;
     -3, 4, 0, 1, 2, 4, 2, 0, -4, 0, -4, -3, 2, -1;
     -3, 4, 0, -2, 2, 4, 5, 3, -4, -3, -4, 0, 2, -4;
     -9, 10, 2, -1, 6, 6, 8, 2, -10, -6, -8, -1, 4, -3;
     9, -8, -3, 1, -4, -5, -4, 0, 5, 3, 8, 0, -1, -1;
     0, 0, 1, -1, 2, 1, 3, 1, -3, 0, -2, -2, 1, -1;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     6, -6, -1, 1, -2, -1, -3, -1, 3, 0, 2, 2, -1, 1;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def pair24_05_06Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![0, 12, 0, 0, 24, 0, 12, 12, 12, 12;
     -24, 84, 48, 24, 96, 0, 36, 24, 60, 24;
     12, -60, -12, -12, -60, 12, -12, -12, -36, -24;
     24, -72, -48, -12, -96, -6, -36, -30, -54, -18;
     0, 24, 0, 0, 24, -6, 0, 6, 18, 18;
     -12, 12, 12, 0, 24, 12, 12, 12, 12, 0;
     24, -60, -24, 0, -72, 12, -12, -24, -36, -12;
     12, -24, 0, -12, -24, 12, 0, 0, -12, -12;
     -12, 24, 12, 12, 24, -6, 12, -6, 18, 6;
     -12, 36, 12, 0, 36, -12, 0, 12, 12, 0;
     -24, 60, 36, 12, 72, -6, 12, 18, 42, 6;
     12, -36, -36, -12, -48, -12, -24, -12, -36, 0;
     -12, 12, 0, 0, 12, -12, 0, 0, 12, 0;
     12, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, -24, -12, -12, -24, 0, -12, -12, -24, -12;
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
theorem pair24_05_06_certificate :
    pair24_05_06Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_05_06Rows id +
      pair24_05_06Inverse * integerInformationSelector pair24_05_06Free = (12 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_05_06_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_05_06Inverse.mulVec (fun t => if b t then 1 else -1) k = 12 ∨
      pair24_05_06Inverse.mulVec (fun t => if b t then 1 else -1) k = -12) →
    IntegerScaledHalfPattern 12 (1)
      (∑ k, encodedIntFrame base24Masks 5 k * pair24_05_06Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 6 k * pair24_05_06Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_05_06_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {5, 6} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 5 k * x k) (∑ k, base24Frame 6 k * x k) := by
  have h := order24_integer_pair_lift 5 6 pair24_05_06Rows pair24_05_06Free
    pair24_05_06Left pair24_05_06Inverse 12 (1) (by norm_num) (by decide +kernel)
    pair24_05_06_certificate pair24_05_06_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
