/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P11_13
@[expose] public section
namespace CompletionTheory

def pair24_12_14Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15]
def pair24_12_14Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_12_14Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![0, 5, 11, 9, 5, 3, 3, 1, -2, 5, 7, 3, 5, 5;
     10, -5, 3, -3, -5, 9, -11, 3, -6, 5, 1, -1, -5, 5;
     -5, 10, 6, -6, 10, -12, -2, 6, 3, 5, -8, -7, 10, -10;
     -25, 30, -2, -3, 0, -6, 14, 8, 14, -10, -14, 4, -15, 5;
     15, -10, 2, 3, -10, 6, 6, -8, -14, -10, 4, 6, 5, 5;
     5, 0, 10, 0, 0, 0, -10, -10, 5, 5, 10, -5, 0, -10;
     20, -15, -5, 15, -15, -15, 5, 5, -10, 5, -5, -5, 15, 5;
     40, -35, -3, 3, -5, -9, 1, -3, -24, 5, 19, -19, 25, 5;
     5, 0, -8, 3, 0, 6, -4, 2, -4, -10, 4, 16, -15, 5;
     5, 0, -8, -12, 0, 6, -4, 2, 11, 5, 4, 1, 0, -10;
     -5, 10, -6, -9, 10, 12, -8, -6, 12, -10, -2, 2, -5, 5;
     -35, 40, 0, 0, 10, 0, 10, 0, 15, 5, -20, 5, -20, -10;
     -10, 10, 2, -12, 10, 6, -4, -8, 16, 0, -6, 16, -20, 0;
     40, -40, -2, 12, -10, -6, 4, 8, -16, 0, 6, -16, 20, 0;
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

def pair24_12_14Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-12, -36, -12, -12, 24, 36, 48, 12, 0, 12;
     -36, 12, -36, -36, -48, -12, 24, -24, 0, -24;
     -12, 24, 48, -12, 84, -24, -12, 72, 0, 12;
     84, 72, 84, 144, 72, 18, 24, 6, 90, 66;
     -24, -72, -24, -24, -72, 42, -24, -66, -30, -6;
     0, 0, -60, -60, 0, 0, 0, 60, 0, 0;
     -120, -60, 0, 0, 0, 0, -60, -60, -120, 0;
     -144, -132, -24, -144, -72, 12, -84, -36, -180, -96;
     36, -12, -24, 36, -72, -18, 36, -66, 30, -6;
     36, 48, -24, -24, -12, -48, -24, 24, 0, -36;
     72, 36, 12, 12, -24, -6, 12, 18, 90, -42;
     120, 120, 60, 120, 120, 0, 60, 60, 120, 120;
     96, 48, -24, 36, -12, -48, 36, 24, 120, 24;
     -156, -108, -36, -96, -48, -12, -96, -84, -180, -84;
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
theorem pair24_12_14_certificate :
    pair24_12_14Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_12_14Rows id +
      pair24_12_14Inverse * integerInformationSelector pair24_12_14Free = (60 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_12_14_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_12_14Inverse.mulVec (fun t => if b t then 1 else -1) k = 60 ∨
      pair24_12_14Inverse.mulVec (fun t => if b t then 1 else -1) k = -60) →
    IntegerScaledHalfPattern 60 (1)
      (∑ k, encodedIntFrame base24Masks 12 k * pair24_12_14Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 14 k * pair24_12_14Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_12_14_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {12, 14} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 12 k * x k) (∑ k, base24Frame 14 k * x k) := by
  have h := order24_integer_pair_lift 12 14 pair24_12_14Rows pair24_12_14Free
    pair24_12_14Left pair24_12_14Inverse 60 (1) (by norm_num) (by decide +kernel)
    pair24_12_14_certificate pair24_12_14_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
