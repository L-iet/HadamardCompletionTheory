/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P02_13
@[expose] public section
namespace CompletionTheory

def pair24_03_05Rows : Fin 14 → Fin 16 := ![0, 1, 2, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def pair24_03_05Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_03_05Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![-9, 10, 4, 4, 0, 2, 5, 4, -4, 0, -3, -2, 3, -2;
     11, -10, 0, -4, -4, 0, -3, 4, 2, -2, 3, 2, 3, -2;
     -1, 2, 0, 2, 2, 0, -3, -5, 2, 1, 0, 2, -6, 4;
     -5, 6, -1, 0, 4, 1, 1, -5, -1, 2, 0, -3, -3, 4;
     3, -2, 1, -2, 0, -1, -1, 1, -1, 0, 0, 1, 3, -2;
     1, 0, 2, 0, -2, -2, 1, 1, 2, -1, 0, 0, 0, -2;
     -23, 24, 2, 6, 4, 4, 7, -2, -10, 2, -9, -6, -3, 4;
     -1, 2, 0, 2, 2, 0, -3, -2, 2, -2, -3, 2, -3, 4;
     1, 0, -1, 0, -2, 1, 1, 1, -1, 2, 0, -3, 3, -2;
     19, -18, -4, -6, -2, -2, -5, 1, 8, -1, 6, 6, 0, -2;
     17, -16, -3, -4, -4, -3, -3, 1, 5, -2, 6, 5, 3, -2;
     -7, 8, 0, 2, 2, 0, 3, 1, -4, 1, 0, -4, 0, -2;
     16, -16, -2, -4, -2, -4, -4, 0, 6, 2, 6, 2, 0, 0;
     -10, 10, 2, 4, 2, 4, 4, 0, -6, -2, -6, -2, 0, 0;
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

def pair24_03_05Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![12, 36, 12, 12, 48, 0, 24, 24, 36, 24;
     -36, -12, -36, -36, -24, -24, -24, -12, -36, -12;
     12, -24, 24, 12, -12, 24, 12, 0, 0, -12;
     24, 0, 24, 36, 0, 18, 12, -6, 18, 6;
     -12, 0, -12, -12, 0, -6, -12, -6, -6, 6;
     0, 0, -12, -12, 0, 0, 0, 12, 0, 0;
     48, 60, 72, 72, 72, 36, 60, 24, 84, 36;
     0, -12, 24, 0, 0, 24, 12, 0, 0, -12;
     0, 12, -12, 0, 0, -18, 0, -6, 6, 6;
     -36, -48, -48, -48, -60, -24, -48, -24, -72, -36;
     -36, -36, -48, -48, -48, -30, -48, -18, -54, -30;
     24, 24, 12, 24, 24, 0, 12, 12, 24, 24;
     -24, -48, -48, -36, -60, -24, -36, -24, -48, -24;
     12, 36, 36, 24, 48, 12, 24, 12, 36, 12;
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
theorem pair24_03_05_certificate :
    pair24_03_05Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_03_05Rows id +
      pair24_03_05Inverse * integerInformationSelector pair24_03_05Free = (12 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_03_05_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_03_05Inverse.mulVec (fun t => if b t then 1 else -1) k = 12 ∨
      pair24_03_05Inverse.mulVec (fun t => if b t then 1 else -1) k = -12) →
    IntegerScaledHalfPattern 12 (1)
      (∑ k, encodedIntFrame base24Masks 3 k * pair24_03_05Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 5 k * pair24_03_05Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_03_05_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {3, 5} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 3 k * x k) (∑ k, base24Frame 5 k * x k) := by
  have h := order24_integer_pair_lift 3 5 pair24_03_05Rows pair24_03_05Free
    pair24_03_05Left pair24_03_05Inverse 12 (1) (by norm_num) (by decide +kernel)
    pair24_03_05_certificate pair24_03_05_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
