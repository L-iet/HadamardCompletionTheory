/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P10_15
@[expose] public section
namespace CompletionTheory

def pair24_11_15Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14]
def pair24_11_15Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_11_15Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![3, -2, 2, 2, 0, 0, 0, 0, -1, 2, 2, 1, 2, 1;
     -7, 8, 2, -2, 2, 2, -2, 2, 3, 2, -4, -3, -4, 1;
     -10, 11, 2, -2, 5, -1, 1, 2, 3, -1, -4, -3, -1, -2;
     1, 0, -1, 0, -2, -2, 2, 1, 1, -1, -1, 2, -1, 1;
     15, -14, -1, 2, -6, 0, 0, -3, -7, -1, 5, 4, 5, 1;
     -2, 3, 2, 0, 1, 1, -1, -2, 1, -1, 2, -1, -1, -2;
     -17, 18, 2, 0, 4, -2, 2, 4, 7, 2, -10, -7, -4, 1;
     -55, 56, 8, -8, 20, 2, 4, 8, 21, 2, -22, -21, -16, 1;
     43, -42, -7, 6, -14, -2, -4, -5, -17, -1, 17, 14, 11, 1;
     16, -15, -4, 0, -5, 1, -1, -2, -5, -1, 8, 5, 5, -2;
     -1, 2, -1, -2, 2, 2, -2, -1, 3, -1, -1, 0, -1, 1;
     20, -19, -4, 4, -7, -1, 1, -4, -9, -1, 8, 9, 5, -2;
     46, -46, -6, 4, -14, -2, -4, -8, -16, 0, 18, 16, 12, 0;
     -40, 40, 6, -4, 14, 2, 4, 8, 16, 0, -18, -16, -12, 0;
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

def pair24_11_15Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-12, -12, -12, -12, 0, 0, 0, 0, -12, 0;
     12, 36, 12, 12, 24, 0, 24, 12, 36, 12;
     24, 24, 36, 24, 36, 12, 24, 24, 36, 12;
     0, 0, 0, 12, 0, -6, -12, -6, -6, 6;
     -36, -48, -36, -36, -48, -6, -36, -30, -54, -18;
     12, 0, 0, 0, 0, 12, 12, 12, 12, 0;
     24, 60, 48, 48, 72, 12, 36, 24, 60, 36;
     120, 180, 144, 120, 192, 48, 132, 96, 216, 84;
     -96, -132, -108, -96, -144, -42, -96, -78, -162, -66;
     -24, -48, -36, -36, -60, -12, -36, -24, -60, -36;
     12, 12, 0, 0, 0, -6, 0, 6, 18, -6;
     -36, -72, -48, -36, -72, -12, -48, -36, -84, -24;
     -96, -144, -120, -108, -156, -48, -108, -72, -168, -72;
     84, 132, 108, 96, 144, 36, 96, 60, 156, 60;
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
theorem pair24_11_15_certificate :
    pair24_11_15Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_11_15Rows id +
      pair24_11_15Inverse * integerInformationSelector pair24_11_15Free = (12 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_11_15_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_11_15Inverse.mulVec (fun t => if b t then 1 else -1) k = 12 ∨
      pair24_11_15Inverse.mulVec (fun t => if b t then 1 else -1) k = -12) →
    IntegerScaledHalfPattern 12 (1)
      (∑ k, encodedIntFrame base24Masks 11 k * pair24_11_15Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 15 k * pair24_11_15Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_11_15_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {11, 15} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 11 k * x k) (∑ k, base24Frame 15 k * x k) := by
  have h := order24_integer_pair_lift 11 15 pair24_11_15Rows pair24_11_15Free
    pair24_11_15Left pair24_11_15Inverse 12 (1) (by norm_num) (by decide +kernel)
    pair24_11_15_certificate pair24_11_15_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
