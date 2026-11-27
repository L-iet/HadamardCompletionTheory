/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P06_10
@[expose] public section
namespace CompletionTheory

def pair24_06_14Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 15]
def pair24_06_14Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_06_14Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![9, -8, 1, 3, -2, 0, -1, -4, 1, 5, 0, 3, 4, 1;
     -31, 32, 5, -5, 10, 4, 5, 12, 1, -13, 2, -11, -12, 1;
     -7, 8, 2, -2, 4, -2, 2, 3, 1, -4, -1, -2, 0, -2;
     37, -36, -6, 5, -14, -4, -4, -14, -2, 14, -2, 14, 11, 1;
     21, -20, -2, 3, -8, 0, -4, -10, -2, 8, 0, 6, 7, 1;
     -29, 30, 6, -4, 10, 2, 2, 13, 1, -10, 1, -10, -10, -2;
     19, -18, -3, 5, -8, -4, -1, -8, 1, 5, -2, 5, 8, 1;
     11, -10, -1, 1, -2, -2, -1, -6, 1, 5, -4, 1, 6, 1;
     -11, 12, 0, -1, 4, 2, 2, 4, -2, -4, 4, -4, -7, 1;
     -11, 12, 0, -4, 4, 2, 2, 7, 1, -4, 1, -4, -4, -2;
     -25, 26, 2, -5, 10, 4, 2, 12, -2, -10, 2, -8, -9, 1;
     23, -22, -4, 4, -8, -2, -4, -9, 1, 8, -1, 10, 6, -2;
     -14, 14, 2, -4, 6, 2, 0, 8, 0, -6, 4, -4, -8, 0;
     20, -20, -2, 4, -6, -2, 0, -8, 0, 6, -4, 4, 8, 0;
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

def pair24_06_14Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-24, -36, -24, -24, -24, 0, -12, -12, -36, -12;
     72, 108, 72, 72, 96, 24, 84, 48, 132, 48;
     12, 24, 24, 12, 36, 0, 12, 24, 24, 12;
     -84, -120, -84, -72, -120, -30, -96, -66, -150, -54;
     -48, -72, -48, -48, -72, -6, -48, -42, -78, -30;
     72, 96, 60, 60, 96, 24, 72, 60, 120, 48;
     -60, -60, -36, -36, -48, -12, -48, -36, -84, -24;
     -36, -36, -12, -36, -24, 0, -24, -12, -48, -24;
     36, 36, 24, 36, 24, 6, 36, 6, 54, 18;
     36, 48, 24, 24, 36, 0, 24, 24, 48, 12;
     72, 84, 60, 60, 72, 18, 60, 42, 114, 30;
     -48, -72, -60, -48, -72, -24, -60, -36, -96, -24;
     48, 48, 24, 36, 36, 0, 36, 24, 72, 24;
     -60, -60, -36, -48, -48, -12, -48, -36, -84, -36;
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
theorem pair24_06_14_certificate :
    pair24_06_14Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_06_14Rows id +
      pair24_06_14Inverse * integerInformationSelector pair24_06_14Free = (12 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_06_14_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_06_14Inverse.mulVec (fun t => if b t then 1 else -1) k = 12 ∨
      pair24_06_14Inverse.mulVec (fun t => if b t then 1 else -1) k = -12) →
    IntegerScaledHalfPattern 12 (1)
      (∑ k, encodedIntFrame base24Masks 6 k * pair24_06_14Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 14 k * pair24_06_14Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_06_14_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {6, 14} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 6 k * x k) (∑ k, base24Frame 14 k * x k) := by
  have h := order24_integer_pair_lift 6 14 pair24_06_14Rows pair24_06_14Free
    pair24_06_14Left pair24_06_14Inverse 12 (1) (by norm_num) (by decide +kernel)
    pair24_06_14_certificate pair24_06_14_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
