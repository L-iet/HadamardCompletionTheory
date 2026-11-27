/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P11_12
@[expose] public section
namespace CompletionTheory

def pair24_12_13Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15]
def pair24_12_13Free : Fin 10 → Fin 24 := ![13, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_12_13Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![-8, 12, 11, 3, 6, 0, -2, 1, 7, 13, -1, 2, 9, -5;
     16, -12, -3, 5, -6, 16, 2, -1, -23, -21, 17, 6, -25, 29;
     -20, 24, 10, -14, 12, -16, -12, 6, 22, 26, -22, -8, 22, -30;
     4, 0, -5, 7, -6, -4, 18, 9, -5, -19, -1, -2, -11, 15;
     4, 0, 3, -1, -6, 4, 2, -7, -5, -3, -1, 6, 5, -1;
     4, 0, 8, 0, 0, 0, -8, -8, 4, 4, 8, -4, 0, -8;
     -8, 12, -3, 5, -6, -8, 2, -1, 1, 3, -7, 6, -1, 5;
     -8, 12, 3, -13, 6, -8, -10, -7, 7, 21, -1, -6, 17, -13;
     28, -24, -13, 15, -6, 12, 10, 1, -29, -35, 23, 14, -27, 31;
     4, 0, -4, -12, 0, 0, -8, 4, 16, 16, -4, -4, 12, -20;
     4, 0, -3, -7, 6, 4, -10, -1, 13, 3, -7, -6, 11, -7;
     4, 0, -4, 12, 0, 0, 16, 4, -8, -8, -4, -4, -12, 4;
     24, -24, -4, 4, 0, 8, 8, -4, -12, -20, 12, 8, -20, 20;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 4, -4, 0, -8, -8, 4, 12, 20, -12, -8, 20, -20;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def pair24_12_13Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![12, 36, -24, -12, 72, -12, 36, 48, 36, 48;
     -12, -132, 24, 12, -168, 108, 60, -96, -36, -96;
     24, 168, 0, -24, 192, -120, -24, 144, 72, 96;
     -36, -60, 72, 84, -24, 60, -12, -72, -36, -24;
     12, -12, -24, -12, -24, 12, -12, -24, 12, 24;
     0, 0, -48, -48, 0, 0, 0, 48, 0, 0;
     36, 12, 24, 60, 24, 12, 12, 0, 12, 48;
     60, 84, -24, -60, 72, -60, -12, 96, 36, 48;
     -36, -204, 24, 36, -216, 108, 36, -168, -84, -120;
     0, 96, -48, -48, 48, -96, -48, 48, 0, 0;
     -12, 60, -24, -36, 24, -60, -36, 24, 36, -24;
     -48, -48, 48, 48, 0, 48, 0, -48, -48, 0;
     -48, -144, 0, 0, -144, 48, 0, -96, -48, -96;
     48, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 96, -48, -48, 96, -96, -48, 48, 0, 48;
     0, 48, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 48, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 48, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 48, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 48, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 48, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 48, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 48, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 48]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_12_13_certificate :
    pair24_12_13Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_12_13Rows id +
      pair24_12_13Inverse * integerInformationSelector pair24_12_13Free = (48 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_12_13_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_12_13Inverse.mulVec (fun t => if b t then 1 else -1) k = 48 ∨
      pair24_12_13Inverse.mulVec (fun t => if b t then 1 else -1) k = -48) →
    IntegerScaledHalfPattern 48 (1)
      (∑ k, encodedIntFrame base24Masks 12 k * pair24_12_13Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 13 k * pair24_12_13Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_12_13_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {12, 13} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 12 k * x k) (∑ k, base24Frame 13 k * x k) := by
  have h := order24_integer_pair_lift 12 13 pair24_12_13Rows pair24_12_13Free
    pair24_12_13Left pair24_12_13Inverse 48 (1) (by norm_num) (by decide +kernel)
    pair24_12_13_certificate pair24_12_13_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
