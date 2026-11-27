/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P08_13
@[expose] public section
namespace CompletionTheory

def pair24_09_11Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 13, 14, 15]
def pair24_09_11Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_09_11Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![15, -14, 0, 4, -4, 0, 0, -2, -7, 8, 5, 6, -1, 2;
     5, -4, 0, 0, -2, 2, -2, 0, -3, 2, 1, 0, -1, 2;
     -16, 17, 3, -3, 7, -1, 1, 3, 6, -7, -5, -3, -1, -1;
     -5, 6, 0, -1, 0, -2, 2, 2, 4, -4, 0, -3, 2, -1;
     9, -8, 0, 1, -4, 0, 0, -2, -4, 2, 2, 3, 2, -1;
     -8, 9, 3, -1, 3, 1, -1, -1, 4, -1, -3, -3, -1, -1;
     -5, 6, 0, 2, 0, -2, 2, 2, 1, -4, -3, 0, -1, 2;
     -43, 44, 6, -6, 16, 2, 4, 6, 15, -16, -17, -12, -1, 2;
     37, -36, -6, 5, -12, -2, -4, -4, -14, 14, 12, 9, 2, -1;
     10, -9, -3, -1, -3, 1, -1, -1, -2, 5, 3, 3, -1, -1;
     -7, 8, 0, -3, 4, 2, -2, 0, 6, -4, -2, -3, 2, -1;
     14, -13, -3, 3, -5, -1, 1, -3, -6, 5, 7, 3, -1, -1;
     46, -46, -6, 4, -14, -2, -4, -8, -16, 18, 16, 12, 0, 0;
     -40, 40, 6, -4, 14, 2, 4, 8, 16, -18, -16, -12, 0, 0;
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

def pair24_09_11Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-36, -60, -36, -36, -48, 0, -24, -24, -60, -24;
     -12, -12, -12, -12, -24, 0, 0, -12, -12, -12;
     36, 48, 48, 36, 60, 12, 36, 36, 60, 24;
     12, 24, 12, 24, 24, -6, 0, 6, 18, 18;
     -24, -24, -24, -24, -24, -6, -24, -18, -30, -6;
     24, 24, 12, 12, 24, 12, 24, 24, 36, 12;
     0, 12, 24, 24, 24, 12, 12, 0, 12, 12;
     96, 132, 120, 96, 144, 48, 108, 72, 168, 60;
     -84, -108, -96, -84, -120, -42, -84, -66, -138, -54;
     -12, -24, -24, -24, -36, -12, -24, -12, -36, -24;
     24, 36, 12, 12, 24, -6, 12, 18, 42, 6;
     -24, -48, -36, -24, -48, -12, -36, -24, -60, -12;
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
theorem pair24_09_11_certificate :
    pair24_09_11Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_09_11Rows id +
      pair24_09_11Inverse * integerInformationSelector pair24_09_11Free = (12 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_09_11_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_09_11Inverse.mulVec (fun t => if b t then 1 else -1) k = 12 ∨
      pair24_09_11Inverse.mulVec (fun t => if b t then 1 else -1) k = -12) →
    IntegerScaledHalfPattern 12 (1)
      (∑ k, encodedIntFrame base24Masks 9 k * pair24_09_11Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 11 k * pair24_09_11Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_09_11_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {9, 11} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 9 k * x k) (∑ k, base24Frame 11 k * x k) := by
  have h := order24_integer_pair_lift 9 11 pair24_09_11Rows pair24_09_11Free
    pair24_09_11Left pair24_09_11Inverse 12 (1) (by norm_num) (by decide +kernel)
    pair24_09_11_certificate pair24_09_11_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
