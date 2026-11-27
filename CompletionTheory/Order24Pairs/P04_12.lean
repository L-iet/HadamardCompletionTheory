/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P04_08
@[expose] public section
namespace CompletionTheory

def pair24_04_12Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15]
def pair24_04_12Free : Fin 10 → Fin 24 := ![13, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_04_12Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![8, -6, 1, 9, 6, 8, -1, -13, -13, 13, 4, 6, -15, 17;
     -4, 6, 3, -5, 2, -8, 1, 5, 9, -5, 0, -6, 7, -5;
     14, -12, -4, 8, 4, 12, 0, -22, -26, 16, 2, 12, -28, 24;
     -10, 12, 2, -4, -8, 0, 6, 14, 10, -14, -4, -6, 14, -12;
     -10, 12, 6, -8, -4, -8, -2, 14, 18, -14, 0, -6, 22, -20;
     2, 0, 4, 0, 0, -4, -4, 2, 2, 4, -2, 0, 0, -4;
     -16, 18, 3, -5, -10, -8, 1, 17, 21, -17, 0, -6, 19, -17;
     8, -6, -3, 1, 2, 4, -5, -13, -9, 13, 0, 6, -11, 13;
     2, 0, -2, 0, 0, -4, 2, 2, 2, -2, 4, -6, 6, -4;
     2, 0, -2, -6, 0, -4, 2, 8, 8, -2, -2, 0, 6, -10;
     14, -12, -6, 4, 8, 4, -2, -10, -18, 10, 0, 6, -14, 16;
     2, 0, -2, 6, 0, 8, 2, -4, -4, -2, -2, 0, -6, 2;
     12, -12, -2, 2, 4, 4, -2, -6, -10, 6, 4, 0, -10, 10;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 2, -2, -4, -4, 2, 6, 10, -6, -4, 0, 10, -10;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def pair24_04_12Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-12, -108, 24, 12, -72, 84, 36, -48, -36, -48;
     12, 60, -24, -12, 24, -36, 12, 24, 36, 24;
     -24, -168, 72, 24, -120, 120, 24, -72, -72, -96;
     0, 96, 0, 24, 96, -60, -24, 36, 36, 60;
     24, 120, -48, -24, 96, -84, -24, 60, 60, 84;
     0, 0, -24, -24, 0, 0, 0, 24, 0, 0;
     36, 132, -24, 12, 120, -84, -12, 72, 60, 96;
     12, -84, 24, -12, -72, 60, 12, -24, -36, -48;
     0, 24, -24, 0, 0, -36, 0, -12, 12, 12;
     0, 48, -24, -24, 24, -48, -24, 24, 0, 0;
     -24, -96, 24, 0, -96, 60, 0, -60, -36, -84;
     -24, -24, 24, 24, 0, 24, 0, -24, -24, 0;
     -24, -72, 0, 0, -72, 24, 0, -48, -24, -48;
     24, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 48, -24, -24, 48, -48, -24, 24, 0, 24;
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
theorem pair24_04_12_certificate :
    pair24_04_12Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_04_12Rows id +
      pair24_04_12Inverse * integerInformationSelector pair24_04_12Free = (24 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_04_12_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_04_12Inverse.mulVec (fun t => if b t then 1 else -1) k = 24 ∨
      pair24_04_12Inverse.mulVec (fun t => if b t then 1 else -1) k = -24) →
    IntegerScaledHalfPattern 24 (1)
      (∑ k, encodedIntFrame base24Masks 4 k * pair24_04_12Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 12 k * pair24_04_12Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_04_12_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {4, 12} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 4 k * x k) (∑ k, base24Frame 12 k * x k) := by
  have h := order24_integer_pair_lift 4 12 pair24_04_12Rows pair24_04_12Free
    pair24_04_12Left pair24_04_12Inverse 24 (1) (by norm_num) (by decide +kernel)
    pair24_04_12_certificate pair24_04_12_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
