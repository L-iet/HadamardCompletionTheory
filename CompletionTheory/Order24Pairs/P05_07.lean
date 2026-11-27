/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P04_13
@[expose] public section
namespace CompletionTheory

def pair24_05_07Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 6, 8, 9, 10, 11, 12, 13, 14, 15]
def pair24_05_07Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_05_07Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![3, -2, 2, 2, 0, 0, -1, 2, 2, 0, 1, 2, 1, 0;
     11, -10, 0, 0, -4, -4, -3, 4, 2, -2, 3, 2, 3, -2;
     -1, 2, 0, 0, 2, 2, -3, -5, 2, 1, 0, 2, -6, 4;
     1, 0, -2, 1, -2, 4, -2, -6, 2, 2, 2, -1, -4, 5;
     -3, 4, 2, -1, 0, 0, 2, 2, -4, 0, -2, -1, 4, -3;
     -11, 12, 4, -2, 4, -2, 7, 3, -4, -1, -4, -4, 2, -4;
     1, 0, -2, 4, -2, 4, -5, -6, 2, 2, -1, 2, -7, 8;
     -1, 2, 0, 0, 2, 2, -3, -2, 2, -2, -3, 2, -3, 4;
     7, -6, -2, 1, -2, -2, -2, 0, 2, 2, 2, -1, 2, -1;
     7, -6, -2, -2, -2, -2, 1, 3, 2, -1, 2, 2, 2, -4;
     -1, 2, 0, -3, 2, -4, 6, 4, -4, -2, 0, -1, 6, -5;
     -7, 8, 0, 0, 2, 2, 3, 1, -4, 1, 0, -4, 0, -2;
     -8, 8, 2, -4, 4, -2, 8, 4, -6, 2, -2, -6, 4, -4;
     14, -14, -2, 4, -4, 2, -8, -4, 6, -2, 2, 6, -4, 4;
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

def pair24_05_07Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-12, -12, -12, -12, 0, 0, 0, 0, -12, 0;
     -36, -12, -36, -36, -24, -24, -24, -12, -36, -12;
     12, -24, 24, 12, -12, 24, 12, 0, 0, -12;
     12, -24, 12, 24, -24, 18, 0, -18, -6, -6;
     0, 24, 0, 0, 24, -6, 0, 6, 18, 18;
     24, 48, 12, 12, 48, 0, 24, 36, 48, 24;
     0, -36, 24, 24, -24, 36, 12, -24, -12, -12;
     0, -12, 24, 0, 0, 24, 12, 0, 0, -12;
     -12, -12, -24, -12, -24, -18, -12, -18, -18, -6;
     -12, 0, -24, -24, -12, -24, -24, 0, -24, -12;
     0, 36, -12, -12, 24, -30, -12, 18, 18, 6;
     24, 24, 12, 24, 24, 0, 12, 12, 24, 24;
     24, 48, 0, 12, 36, -24, 12, 24, 48, 24;
     -36, -60, -12, -24, -48, 12, -24, -36, -60, -36;
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
theorem pair24_05_07_certificate :
    pair24_05_07Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_05_07Rows id +
      pair24_05_07Inverse * integerInformationSelector pair24_05_07Free = (12 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_05_07_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_05_07Inverse.mulVec (fun t => if b t then 1 else -1) k = 12 ∨
      pair24_05_07Inverse.mulVec (fun t => if b t then 1 else -1) k = -12) →
    IntegerScaledHalfPattern 12 (1)
      (∑ k, encodedIntFrame base24Masks 5 k * pair24_05_07Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 7 k * pair24_05_07Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_05_07_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {5, 7} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 5 k * x k) (∑ k, base24Frame 7 k * x k) := by
  have h := order24_integer_pair_lift 5 7 pair24_05_07Rows pair24_05_07Free
    pair24_05_07Left pair24_05_07Inverse 12 (1) (by norm_num) (by decide +kernel)
    pair24_05_07_certificate pair24_05_07_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
