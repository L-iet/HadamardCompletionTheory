/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P11_15
@[expose] public section
namespace CompletionTheory

def pair24_13_14Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15]
def pair24_13_14Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_13_14Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![-15, 20, 13, 7, 10, 4, 4, 3, 4, 5, 1, 4, -5, 5;
     25, -20, 1, -1, -10, 8, -12, 1, -12, 5, 7, -2, 5, 5;
     -35, 40, 10, -10, 20, -10, 0, 10, 15, 5, -20, -5, -10, -10;
     20, -15, -8, 3, -15, -9, 11, 2, -4, -10, 4, 1, 15, 5;
     0, 5, 4, 1, -5, 7, 7, -6, -8, -10, -2, 7, -5, 5;
     5, 0, 10, 0, 0, 0, -10, -10, 5, 5, 10, -5, 0, -10;
     -25, 30, 1, 9, 0, -12, 8, 11, 8, 5, -23, -2, -15, 5;
     -35, 40, 7, -7, 20, -4, 6, 7, 6, 5, -11, -14, -25, 5;
     50, -45, -14, 9, -15, 3, -7, -4, -22, -10, 22, 13, 15, 5;
     5, 0, -8, -12, 0, 6, -4, 2, 11, 5, 4, 1, 0, -10;
     10, -5, -8, -7, 5, 11, -9, -8, 6, -10, 4, 1, 5, 5;
     25, -20, -8, 8, -10, -4, 6, -8, -9, 5, 4, 1, 20, -10;
     50, -50, -6, -4, -10, 2, -8, -16, -8, 0, 18, 12, 20, 0;
     -20, 20, 6, 4, 10, -2, 8, 16, 8, 0, -18, -12, -20, 0;
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

def pair24_13_14Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![24, 12, 24, 24, 72, 48, 84, 36, 60, 36;
     -72, -36, -72, -72, -96, -24, -12, -48, -60, -48;
     60, 120, 120, 60, 180, 0, 60, 120, 120, 60;
     -24, -72, -24, 36, -72, -18, -84, -66, -90, -6;
     12, -24, 12, 12, -24, 54, 12, -42, 30, 18;
     0, 0, -60, -60, 0, 0, 0, 60, 0, 0;
     -12, 84, 108, 108, 144, 36, 48, 12, 60, 72;
     36, 108, 156, 36, 168, 72, 96, 84, 120, 24;
     -72, -156, -132, -72, -216, -54, -72, -138, -150, -78;
     36, 48, -24, -24, -12, -48, -24, 24, 0, -36;
     36, -12, -24, -24, -72, -18, -24, -6, 30, -66;
     -24, -72, -84, -24, -72, -48, -84, -36, -120, 24;
     -48, -144, -168, -108, -204, -96, -108, -72, -120, -72;
     -12, 84, 108, 48, 144, 36, 48, 12, 60, 12;
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
theorem pair24_13_14_certificate :
    pair24_13_14Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_13_14Rows id +
      pair24_13_14Inverse * integerInformationSelector pair24_13_14Free = (60 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_13_14_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_13_14Inverse.mulVec (fun t => if b t then 1 else -1) k = 60 ∨
      pair24_13_14Inverse.mulVec (fun t => if b t then 1 else -1) k = -60) →
    IntegerScaledHalfPattern 60 (1)
      (∑ k, encodedIntFrame base24Masks 13 k * pair24_13_14Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 14 k * pair24_13_14Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_13_14_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {13, 14} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 13 k * x k) (∑ k, base24Frame 14 k * x k) := by
  have h := order24_integer_pair_lift 13 14 pair24_13_14Rows pair24_13_14Free
    pair24_13_14Left pair24_13_14Inverse 60 (1) (by norm_num) (by decide +kernel)
    pair24_13_14_certificate pair24_13_14_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
