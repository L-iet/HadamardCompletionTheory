/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P02_03
@[expose] public section
namespace CompletionTheory

def pair24_02_07Rows : Fin 14 → Fin 16 := ![0, 1, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15]
def pair24_02_07Free : Fin 10 → Fin 24 := ![13, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_02_07Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![5, -4, 6, 0, 4, 6, -9, -10, 8, 2, -1, 4, -11, 12;
     2, -1, 0, -1, 3, -1, -3, -2, 2, 1, 0, -1, -3, 4;
     2, -1, 0, 1, -1, 1, -3, -3, 2, 0, 1, 3, -4, 2;
     -1, 2, -3, -2, -4, -2, 6, 6, -4, 0, 4, -3, 8, -7;
     2, -1, 3, -1, 3, 5, -6, -8, 2, 1, -3, 2, -6, 7;
     5, -4, 6, 0, 4, 6, -9, -13, 8, -1, -4, 4, -14, 12;
     -4, 5, 0, -1, -3, -1, 3, 4, -4, 1, 0, -1, 3, -2;
     -1, 2, 0, 2, 0, 2, -3, -2, 2, -2, -3, 2, -3, 4;
     -1, 2, -3, 0, -2, -6, 6, 8, -4, 2, 2, -5, 10, -9;
     -1, 2, -6, 0, -2, -6, 9, 11, -4, -1, 2, -2, 10, -12;
     -1, 2, -3, 2, 0, -4, 6, 4, -4, -2, 0, -1, 6, -5;
     -1, 2, 0, 0, -2, 0, 3, 5, -4, -1, 2, -2, 4, -6;
     3, -3, 0, 1, 1, 1, 0, -2, 0, 1, -1, -1, -2, 2;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     3, -3, 0, -1, -1, -1, 0, 2, 0, -1, 1, 1, 2, -2;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def pair24_02_07Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-12, -72, 24, 12, -48, 60, 24, -36, -24, -36;
     0, -12, 0, 0, -24, 12, 12, -12, 0, -12;
     0, -24, 12, 0, -12, 12, 0, 0, -12, -12;
     12, 36, -24, 0, 24, -42, -24, 18, 6, 30;
     -12, -36, 24, 12, -24, 42, 12, -30, -6, -18;
     -24, -72, 36, 12, -48, 72, 24, -36, -24, -48;
     12, 24, 0, 12, 24, -12, 0, 12, 12, 24;
     0, -12, 24, 0, 0, 24, 12, 0, 0, -12;
     12, 48, -36, -12, 24, -54, -12, 18, 18, 30;
     12, 60, -36, -24, 36, -60, -24, 36, 12, 24;
     0, 36, -12, -12, 24, -30, -12, 18, 18, 6;
     0, 24, -12, 0, 24, -24, -12, 12, 0, 24;
     -12, -12, 0, 0, -12, 0, 0, -12, 0, -12;
     12, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, -12, -12, 0, -12, -12, 0, -12, 0;
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
theorem pair24_02_07_certificate :
    pair24_02_07Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_02_07Rows id +
      pair24_02_07Inverse * integerInformationSelector pair24_02_07Free = (12 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_02_07_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_02_07Inverse.mulVec (fun t => if b t then 1 else -1) k = 12 ∨
      pair24_02_07Inverse.mulVec (fun t => if b t then 1 else -1) k = -12) →
    IntegerScaledHalfPattern 12 (1)
      (∑ k, encodedIntFrame base24Masks 2 k * pair24_02_07Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 7 k * pair24_02_07Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_02_07_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {2, 7} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 2 k * x k) (∑ k, base24Frame 7 k * x k) := by
  have h := order24_integer_pair_lift 2 7 pair24_02_07Rows pair24_02_07Free
    pair24_02_07Left pair24_02_07Inverse 12 (1) (by norm_num) (by decide +kernel)
    pair24_02_07_certificate pair24_02_07_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
