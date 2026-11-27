/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P04_10
@[expose] public section
namespace CompletionTheory

def pair24_04_14Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15]
def pair24_04_14Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_04_14Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![15, -10, 9, 11, 2, 2, -1, -8, 5, 13, 2, 5, 10, 5;
     -5, 10, 5, -5, 10, -10, 5, 0, 5, -5, 0, -5, -10, 5;
     25, -20, 2, -2, -14, -4, 2, -9, 5, 4, -9, 10, 20, -10;
     -25, 30, -2, -3, -6, 14, 8, 14, -10, -14, 4, 0, -15, 5;
     -15, 20, 6, -1, 8, 8, -4, -2, -10, -8, 8, -10, -5, 5;
     5, 0, 10, 0, 0, -10, -10, 5, 5, 10, -5, 0, 0, -10;
     -25, 30, 1, 9, -12, 8, 11, 8, 5, -23, -2, -15, 0, 5;
     25, -20, -1, 1, -8, 2, -1, -18, 5, 13, -18, -5, 20, 5;
     5, 0, -8, 3, 6, -4, 2, -4, -10, 4, 16, 0, -15, 5;
     5, 0, -8, -12, 6, -4, 2, 11, 5, 4, 1, 0, 0, -10;
     25, -20, -10, -5, 10, -10, -10, 0, -10, 10, 0, 10, 5, 5;
     -5, 10, -4, 4, -2, 8, -4, 3, 5, -8, 3, 10, -10, -10;
     20, -20, -2, -8, 4, -6, -12, 4, 0, 6, 14, 10, -10, 0;
     10, -10, 2, 8, -4, 6, 12, -4, 0, -6, -14, -10, 10, 0;
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

def pair24_04_14Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-48, -84, -48, -48, -24, 24, 12, -12, -60, -12;
     0, 60, 0, 0, 0, 0, 60, 0, 60, 0;
     -84, -72, -24, -84, -12, -48, -84, 24, -120, -36;
     84, 72, 84, 144, 72, 18, 24, 6, 90, 66;
     48, 24, 48, 48, 24, 66, 48, -18, 90, 42;
     0, 0, -60, -60, 0, 0, 0, 60, 0, 0;
     -12, 84, 108, 108, 144, 36, 48, 12, 60, 72;
     -108, -84, 12, -108, -24, 24, -48, -12, -120, -72;
     36, -12, -24, 36, -72, -18, 36, -66, 30, -6;
     36, 48, -24, -24, -12, -48, -24, 24, 0, -36;
     0, -60, -60, -60, -120, -30, -60, -30, -30, -90;
     48, 24, -12, 48, 24, -24, -12, 12, 0, 72;
     24, -48, -96, -36, -108, -72, -36, -24, 0, -24;
     -84, -12, 36, -24, 48, 12, -24, -36, -60, -36;
     60, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 60, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 60, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 60, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 60, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 60, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 60, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 60, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 60, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 60]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_04_14_certificate :
    pair24_04_14Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_04_14Rows id +
      pair24_04_14Inverse * integerInformationSelector pair24_04_14Free = (60 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_04_14_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_04_14Inverse.mulVec (fun t => if b t then 1 else -1) k = 60 ∨
      pair24_04_14Inverse.mulVec (fun t => if b t then 1 else -1) k = -60) →
    IntegerScaledHalfPattern 60 (1)
      (∑ k, encodedIntFrame base24Masks 4 k * pair24_04_14Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 14 k * pair24_04_14Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_04_14_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {4, 14} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 4 k * x k) (∑ k, base24Frame 14 k * x k) := by
  have h := order24_integer_pair_lift 4 14 pair24_04_14Rows pair24_04_14Free
    pair24_04_14Left pair24_04_14Inverse 60 (1) (by norm_num) (by decide +kernel)
    pair24_04_14_certificate pair24_04_14_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
