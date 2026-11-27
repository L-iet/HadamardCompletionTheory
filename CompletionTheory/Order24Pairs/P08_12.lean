/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P07_15
@[expose] public section
namespace CompletionTheory

def pair24_08_12Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 14, 15]
def pair24_08_12Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_08_12Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![0, 3, 7, 5, 3, 1, 1, 1, 5, 3, 1, 3, 2, 1;
     6, -3, 3, -3, -3, 3, -9, 3, 9, -3, -3, -3, 6, -3;
     -3, 6, 3, -3, 6, -6, 0, 3, 0, -3, -3, 6, -3, -3;
     -15, 18, -4, 1, 0, 2, 14, 2, -20, 0, 8, -9, -14, 17;
     9, -6, 4, -1, -6, -2, -2, -2, 8, -6, -2, 3, 14, -11;
     3, 0, 5, 1, 0, 2, -4, -7, -2, 9, -1, 0, -5, -1;
     12, -9, -1, 7, -9, -13, -1, 5, 13, -9, -7, 9, 10, -7;
     24, -21, 3, -3, -3, -15, -9, 3, 27, -3, -21, 15, 24, -21;
     3, 0, -4, 1, 0, 2, -4, 2, -2, 0, 8, -9, 4, -1;
     3, 0, -7, -5, 0, 8, 2, -1, -8, 9, 5, 0, -11, 5;
     -3, 6, -6, -3, 6, 12, 0, -6, -18, 6, 6, -3, -12, 15;
     -21, 24, -3, 3, 6, 6, 12, -3, -12, -3, 9, -12, -15, 9;
     -6, 6, -2, -4, 6, 10, 4, -8, -16, 6, 16, -12, -16, 16;
     24, -24, 2, 4, -6, -10, -4, 8, 16, -6, -16, 12, 16, -16;
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

def pair24_08_12Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-12, -12, -12, -12, 24, 12, 24, 12, 0, 12;
     -36, 36, -36, -36, 0, -36, 0, 0, 0, 0;
     0, 0, 36, 0, 36, 0, 0, 36, 0, 0;
     84, -24, 84, 120, -24, 78, 48, -30, 54, 6;
     -48, 24, -48, -48, 24, -42, -48, -6, -18, 30;
     12, -24, -24, -24, -24, 24, 12, 24, 0, -12;
     -96, 12, -24, -24, 48, -48, -60, -12, -72, 24;
     -144, 36, -72, -144, 72, -108, -108, 36, -108, 0;
     12, 12, -24, 12, -24, -30, 12, -30, 18, 6;
     48, -24, 12, 12, -60, 24, 12, -12, 0, -48;
     72, -36, 36, 36, -72, 54, 36, -18, 54, -54;
     108, 0, 72, 108, 0, 72, 72, 0, 72, 36;
     96, -48, 24, 60, -84, 48, 60, -24, 72, -24;
     -132, 12, -60, -96, 48, -84, -96, -12, -108, -12;
     36, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 36, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 36, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 36, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 36, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 36, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 36, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 36, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 36, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 36]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_08_12_certificate :
    pair24_08_12Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_08_12Rows id +
      pair24_08_12Inverse * integerInformationSelector pair24_08_12Free = (36 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_08_12_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_08_12Inverse.mulVec (fun t => if b t then 1 else -1) k = 36 ∨
      pair24_08_12Inverse.mulVec (fun t => if b t then 1 else -1) k = -36) →
    IntegerScaledHalfPattern 36 (1)
      (∑ k, encodedIntFrame base24Masks 8 k * pair24_08_12Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 12 k * pair24_08_12Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_08_12_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {8, 12} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 8 k * x k) (∑ k, base24Frame 12 k * x k) := by
  have h := order24_integer_pair_lift 8 12 pair24_08_12Rows pair24_08_12Free
    pair24_08_12Left pair24_08_12Inverse 36 (1) (by norm_num) (by decide +kernel)
    pair24_08_12_certificate pair24_08_12_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
