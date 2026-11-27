/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P05_08
@[expose] public section
namespace CompletionTheory

def pair24_05_12Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 13, 14, 15]
def pair24_05_12Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_05_12Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![0, 2, 5, 3, 2, 0, 1, 1, 5, 1, 0, 2, 3, -1;
     4, -2, 3, -3, -2, -8, 3, 3, 11, -5, -4, -2, 9, -7;
     -2, 4, 0, 0, 4, 4, 0, -6, -10, 4, 2, 4, -12, 8;
     -10, 12, -2, 0, 0, 8, 2, 2, -10, -2, 4, -6, -6, 8;
     6, -4, 2, 0, -4, 0, -2, -2, 2, -2, 0, 2, 6, -4;
     2, 0, 4, 0, 0, -4, -4, 2, 2, 4, -2, 0, 0, -4;
     8, -6, -5, 9, -6, 8, -1, -13, -13, 7, 4, 6, -15, 17;
     16, -14, -3, 3, -2, 4, -3, -15, -7, 13, -4, 10, -9, 11;
     2, 0, -2, 0, 0, -4, 2, 2, 2, -2, 4, -6, 6, -4;
     2, 0, -2, -6, 0, -4, 2, 8, 8, -2, -2, 0, 6, -10;
     -2, 4, 0, -6, 4, -8, 0, 12, 8, -8, -4, -2, 12, -10;
     -14, 16, 0, 0, 4, 4, 0, 6, 2, -8, 2, -8, 0, -4;
     -4, 4, 2, -6, 4, -4, -2, 10, 6, -6, 4, -8, 6, -6;
     16, -16, -2, 6, -4, 4, 2, -10, -6, 6, -4, 8, -6, 6;
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

def pair24_05_12Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-12, 0, -12, -12, 24, 0, 12, 12, 0, 12;
     -36, 48, -36, -36, 24, -48, -12, 12, 0, 12;
     24, -48, 48, 24, -24, 48, 24, 0, 0, -24;
     48, 0, 48, 72, 0, 36, 24, -12, 36, 12;
     -24, 0, -24, -24, 0, -12, -24, -12, -12, 12;
     0, 0, -24, -24, 0, 0, 0, 24, 0, 0;
     -12, -96, 36, 36, -72, 72, 12, -60, -48, -36;
     -36, -96, 12, -36, -72, 48, -12, -36, -72, -60;
     0, 24, -24, 0, 0, -36, 0, -12, 12, 12;
     0, 48, -24, -24, 24, -48, -24, 24, 0, 0;
     0, 72, -24, -24, 48, -60, -24, 36, 36, 12;
     48, 48, 24, 48, 48, 0, 24, 24, 48, 48;
     24, 48, -24, 0, 24, -48, 0, 24, 48, 24;
     -48, -72, 0, -24, -48, 24, -24, -48, -72, -48;
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
theorem pair24_05_12_certificate :
    pair24_05_12Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_05_12Rows id +
      pair24_05_12Inverse * integerInformationSelector pair24_05_12Free = (24 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_05_12_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_05_12Inverse.mulVec (fun t => if b t then 1 else -1) k = 24 ∨
      pair24_05_12Inverse.mulVec (fun t => if b t then 1 else -1) k = -24) →
    IntegerScaledHalfPattern 24 (1)
      (∑ k, encodedIntFrame base24Masks 5 k * pair24_05_12Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 12 k * pair24_05_12Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_05_12_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {5, 12} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 5 k * x k) (∑ k, base24Frame 12 k * x k) := by
  have h := order24_integer_pair_lift 5 12 pair24_05_12Rows pair24_05_12Free
    pair24_05_12Left pair24_05_12Inverse 24 (1) (by norm_num) (by decide +kernel)
    pair24_05_12_certificate pair24_05_12_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
