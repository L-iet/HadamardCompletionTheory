/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P02_10
@[expose] public section
namespace CompletionTheory

def pair24_02_14Rows : Fin 14 → Fin 16 := ![0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15]
def pair24_02_14Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_02_14Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![33, -31, 8, -9, -1, -1, -4, -14, 2, 16, -1, 11, 13, 2;
     13, -11, 0, -5, 3, -5, 0, -6, 2, 4, -1, 3, 1, 2;
     16, -14, 0, -2, -6, -2, 0, -6, 2, 4, -4, 6, 10, -4;
     -16, 18, -2, 2, -2, 6, 4, 8, -4, -8, 2, -2, -8, 2;
     12, -10, 2, -6, 2, 2, -4, -8, -4, 4, 2, 2, 4, 2;
     32, -30, 4, -10, -2, -6, -8, -10, 2, 16, -4, 10, 10, -4;
     -7, 9, 4, -1, -5, 3, 4, 2, 2, -8, -1, -5, 1, 2;
     7, -5, 0, 1, -3, 1, 0, -6, 2, 4, -7, -3, 7, 2;
     -22, 24, -2, 8, 4, 0, 4, 8, -4, -8, 8, -8, -14, 2;
     -22, 24, -8, 8, 4, 0, 4, 14, 2, -8, 2, -8, -8, -4;
     -20, 22, -6, 10, 6, -2, 0, 12, -4, -8, 2, -6, -8, 2;
     -14, 16, 0, 4, 0, 4, 0, 6, 2, -8, 2, 0, -8, -4;
     2, -2, -4, 2, 2, -2, -4, 4, 0, 0, 6, 2, -6, 0;
     10, -10, 4, -2, -2, 2, 4, -4, 0, 0, -6, -2, 6, 0;
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

def pair24_02_14Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-84, -120, -84, -84, -96, -12, -60, -48, -132, -48;
     -36, -24, -36, -36, -48, -12, -12, -24, -36, -24;
     -48, -48, -24, -48, -24, -24, -48, 0, -72, -24;
     48, 48, 48, 72, 48, 12, 24, 12, 60, 36;
     -24, -48, -24, -24, -48, 12, -24, -36, -36, -12;
     -72, -96, -96, -96, -96, -24, -72, -24, -120, -48;
     -12, 24, 36, 36, 48, 12, 12, 0, 12, 24;
     -36, -24, 12, -36, 0, 12, -12, 0, -36, -24;
     72, 72, 48, 72, 48, 12, 72, 12, 108, 36;
     72, 96, 48, 48, 72, 0, 48, 48, 96, 24;
     72, 72, 48, 48, 48, 12, 48, 36, 108, 12;
     48, 48, 24, 48, 48, 0, 24, 24, 48, 48;
     24, 0, -24, 0, -24, -24, 0, 0, 24, 0;
     -48, -24, 0, -24, 0, 0, -24, -24, -48, -24;
     24, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 24, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 24, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 24, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 24, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 24, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 24, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 24, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 24, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 24]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_02_14_certificate :
    pair24_02_14Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_02_14Rows id +
      pair24_02_14Inverse * integerInformationSelector pair24_02_14Free = (24 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_02_14_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_02_14Inverse.mulVec (fun t => if b t then 1 else -1) k = 24 ∨
      pair24_02_14Inverse.mulVec (fun t => if b t then 1 else -1) k = -24) →
    IntegerScaledHalfPattern 24 (1)
      (∑ k, encodedIntFrame base24Masks 2 k * pair24_02_14Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 14 k * pair24_02_14Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_02_14_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {2, 14} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 2 k * x k) (∑ k, base24Frame 14 k * x k) := by
  have h := order24_integer_pair_lift 2 14 pair24_02_14Rows pair24_02_14Free
    pair24_02_14Left pair24_02_14Inverse 24 (1) (by norm_num) (by decide +kernel)
    pair24_02_14_certificate pair24_02_14_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
