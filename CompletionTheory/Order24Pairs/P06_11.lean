/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P06_07
@[expose] public section
namespace CompletionTheory

def pair24_06_11Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 12, 13, 14, 15]
def pair24_06_11Free : Fin 10 → Fin 24 := ![13, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_06_11Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![-12, 16, 12, 4, 8, 0, 4, 8, 12, -4, -4, 0, 8, -4;
     0, 4, 2, 2, 0, 12, 6, -10, -10, 2, -8, -4, -14, 18;
     6, -2, 1, -3, 4, -6, -1, -7, -5, 5, 6, 10, -9, 1;
     0, 4, -2, -6, -8, -12, 2, 14, 10, -10, 12, -8, 18, -14;
     -12, 16, 8, -4, 0, 0, 0, 8, 8, -16, -8, -4, 16, -12;
     18, -14, 3, 7, -4, 6, -11, -13, -15, 23, 2, 6, -19, 11;
     -24, 28, 2, 2, 0, -12, 6, 14, 14, -22, -8, -4, 10, -6;
     12, -8, -4, -4, 0, 0, -12, -16, -4, 20, 4, 8, -8, 12;
     -12, 16, 0, 4, 8, 0, 16, 8, 0, -16, -16, -12, 8, -4;
     18, -14, -9, -5, -4, 6, 1, -1, -3, 11, 2, 6, -7, -1;
     24, -20, -10, 2, 0, 12, -6, -10, -22, 14, 4, 8, -14, 18;
     6, -2, -3, 1, -4, -6, -5, 5, 15, -7, 14, -6, 11, -19;
     0, 0, 4, -4, 8, 0, 4, 12, 4, -12, -8, -8, 4, -4;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     24, -24, -4, 4, -8, 0, -4, -12, -4, 12, 8, 8, -4, 4;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def pair24_06_11Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![0, 48, 0, 0, 96, 0, 48, 48, 48, 48;
     -24, -24, 48, 24, -48, 72, 72, -48, 24, -48;
     12, -60, 24, -12, -24, 12, -12, 24, -36, -24;
     24, 72, -48, 24, 48, -96, -72, 24, 0, 72;
     0, 96, 0, 0, 96, -24, 0, 24, 72, 72;
     -12, -132, -24, -36, -120, 84, 12, -24, -60, -72;
     24, 120, 48, 72, 144, -24, 24, 48, 72, 96;
     48, -96, 0, -48, -96, 48, 0, 0, -48, -48;
     -48, 96, 48, 48, 96, -24, 48, -24, 72, 24;
     -12, -36, -24, -36, -72, -12, -36, -24, -60, -72;
     -24, -120, 0, -24, -144, 48, -24, -72, -48, -120;
     12, 36, -72, -12, 24, -84, -60, 24, -36, 72;
     -48, 48, 0, 0, 48, -48, 0, 0, 48, 0;
     48, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, -96, -48, -48, -96, 0, -48, -48, -96, -48;
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
theorem pair24_06_11_certificate :
    pair24_06_11Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_06_11Rows id +
      pair24_06_11Inverse * integerInformationSelector pair24_06_11Free = (48 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_06_11_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_06_11Inverse.mulVec (fun t => if b t then 1 else -1) k = 48 ∨
      pair24_06_11Inverse.mulVec (fun t => if b t then 1 else -1) k = -48) →
    IntegerScaledHalfPattern 48 (1)
      (∑ k, encodedIntFrame base24Masks 6 k * pair24_06_11Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 11 k * pair24_06_11Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_06_11_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {6, 11} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 6 k * x k) (∑ k, base24Frame 11 k * x k) := by
  have h := order24_integer_pair_lift 6 11 pair24_06_11Rows pair24_06_11Free
    pair24_06_11Left pair24_06_11Inverse 48 (1) (by norm_num) (by decide +kernel)
    pair24_06_11_certificate pair24_06_11_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
