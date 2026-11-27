/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P10_12
@[expose] public section
namespace CompletionTheory

def pair24_11_12Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 14, 15]
def pair24_11_12Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_11_12Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![0, 2, 5, 3, 2, 0, 0, 1, 1, 5, 1, 2, 3, -1;
     4, -2, 1, -1, -2, 4, -4, 1, -3, 1, 1, -2, -1, 3;
     -2, 4, 1, -1, 4, -2, 2, 1, -3, -5, 1, 4, -7, 3;
     -10, 12, 0, -2, 0, -4, 4, 4, 8, 0, -8, -6, 4, -2;
     6, -4, 2, 0, -4, 0, 0, -2, -2, 2, -2, 2, 6, -4;
     2, 0, 3, 1, 0, 2, -2, -5, -1, -3, 7, 0, -5, 1;
     8, -6, -3, 7, -6, -4, 4, 1, -7, -3, 1, 6, -5, 7;
     16, -14, -5, 5, -2, 4, 8, -5, -21, -17, 19, 10, -19, 21;
     2, 0, 0, -2, 0, -4, -8, 4, 8, 12, -8, -6, 16, -14;
     2, 0, -3, -5, 0, 2, -2, 1, 5, 3, 1, 0, 1, -5;
     -2, 4, -2, -4, 4, 4, -4, -2, 6, -2, -2, -2, 2, 0;
     -14, 16, 1, -1, 4, -2, 2, 1, 9, 7, -11, -8, 5, -9;
     -4, 4, 4, -8, 4, -4, -8, 0, 16, 16, -12, -8, 16, -16;
     16, -16, -4, 8, -4, 4, 8, 0, -16, -16, 12, 8, -16, 16;
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

def pair24_11_12Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-12, 0, -12, -12, 24, 0, 12, 12, 0, 12;
     -12, 0, -12, -12, -24, 0, 12, -12, 0, -12;
     12, -24, 36, 12, 0, 24, 12, 12, 0, -12;
     24, 48, 24, 48, 48, -12, 0, 12, 36, 36;
     -24, 0, -24, -24, 0, -12, -24, -12, -12, 12;
     12, -24, -12, -12, -24, 24, 12, 12, 0, -12;
     -36, -48, 12, 12, -24, 24, -12, -36, -48, -12;
     -12, -144, 36, -12, -120, 96, 12, -60, -72, -84;
     -24, 72, -48, -24, 48, -84, -24, 12, 12, 36;
     12, 24, -12, -12, 0, -24, -12, 12, 0, -12;
     24, 24, 0, 0, 0, -12, 0, 12, 36, -12;
     36, 72, 12, 36, 72, -24, 12, 36, 48, 60;
     0, 96, -48, -24, 72, -96, -24, 48, 48, 48;
     -24, -120, 24, 0, -96, 72, 0, -72, -72, -72;
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
theorem pair24_11_12_certificate :
    pair24_11_12Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_11_12Rows id +
      pair24_11_12Inverse * integerInformationSelector pair24_11_12Free = (24 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_11_12_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_11_12Inverse.mulVec (fun t => if b t then 1 else -1) k = 24 ∨
      pair24_11_12Inverse.mulVec (fun t => if b t then 1 else -1) k = -24) →
    IntegerScaledHalfPattern 24 (1)
      (∑ k, encodedIntFrame base24Masks 11 k * pair24_11_12Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 12 k * pair24_11_12Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_11_12_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {11, 12} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 11 k * x k) (∑ k, base24Frame 12 k * x k) := by
  have h := order24_integer_pair_lift 11 12 pair24_11_12Rows pair24_11_12Free
    pair24_11_12Left pair24_11_12Inverse 24 (1) (by norm_num) (by decide +kernel)
    pair24_11_12_certificate pair24_11_12_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
