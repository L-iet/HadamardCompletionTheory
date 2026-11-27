/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P03_11
@[expose] public section
namespace CompletionTheory

def pair24_03_15Rows : Fin 14 → Fin 16 := ![0, 1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
def pair24_03_15Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_03_15Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![-12, 13, 4, 5, 1, 1, 2, 5, 2, -4, 1, -4, -3, 1;
     8, -7, 0, -3, 1, -3, 0, -3, 2, 2, -1, 2, 1, 1;
     5, -4, 0, 0, -2, 0, 0, -3, -1, 2, -1, 2, 4, -2;
     1, 0, -1, -2, -2, 2, 1, 1, -1, -1, 0, 2, -1, 1;
     0, 1, 1, -1, 1, 1, -1, -1, -1, -1, 1, -1, 0, 1;
     -2, 3, 2, 1, 1, -1, -2, 1, -1, 2, 0, -1, -1, -2;
     -17, 18, 2, 4, -2, 2, 4, 7, 2, -10, 0, -7, -4, 1;
     5, -4, 0, 0, -2, 0, 0, -3, 2, 2, -4, -1, 4, 1;
     -2, 3, -1, 1, 1, -1, 1, 1, -1, -1, 3, -1, -4, 1;
     16, -15, -4, -5, 1, -1, -2, -5, -1, 8, 0, 5, 5, -2;
     14, -13, -3, -3, 1, -3, -3, -3, -1, 5, -1, 5, 4, 1;
     -10, 11, 0, 3, 1, 3, 0, 3, -1, -4, 2, -1, -5, -2;
     16, -16, -2, -4, 0, -2, -4, -4, 0, 6, 2, 6, 2, 0;
     -10, 10, 2, 4, 0, 2, 4, 4, 0, -6, -2, -6, -2, 0;
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

def pair24_03_15Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![24, 36, 24, 24, 48, 12, 36, 24, 48, 24;
     -24, -12, -24, -24, -24, -12, -12, -12, -24, -12;
     -12, -24, 0, -12, -12, 0, -12, 0, -24, -12;
     0, 0, 0, 12, 0, -6, -12, -6, -6, 6;
     0, 0, 0, 0, 0, 6, 0, -6, 6, 6;
     12, 0, 0, 0, 0, 12, 12, 12, 12, 0;
     24, 60, 48, 48, 72, 12, 36, 24, 60, 36;
     -24, -12, 0, -24, 0, 0, -12, 0, -24, -12;
     12, 12, 0, 12, 0, -6, 12, -6, 18, 6;
     -24, -48, -36, -36, -60, -12, -36, -24, -60, -36;
     -24, -36, -36, -36, -48, -18, -36, -18, -42, -30;
     36, 24, 24, 36, 24, 12, 24, 12, 36, 24;
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
theorem pair24_03_15_certificate :
    pair24_03_15Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_03_15Rows id +
      pair24_03_15Inverse * integerInformationSelector pair24_03_15Free = (12 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_03_15_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_03_15Inverse.mulVec (fun t => if b t then 1 else -1) k = 12 ∨
      pair24_03_15Inverse.mulVec (fun t => if b t then 1 else -1) k = -12) →
    IntegerScaledHalfPattern 12 (-1)
      (∑ k, encodedIntFrame base24Masks 3 k * pair24_03_15Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 15 k * pair24_03_15Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_03_15_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {3, 15} x →
    HalfCorrelationPattern 24 (rationalRealCast (-1))
      (∑ k, base24Frame 3 k * x k) (∑ k, base24Frame 15 k * x k) := by
  have h := order24_integer_pair_lift 3 15 pair24_03_15Rows pair24_03_15Free
    pair24_03_15Left pair24_03_15Inverse 12 (-1) (by norm_num) (by decide +kernel)
    pair24_03_15_certificate pair24_03_15_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
