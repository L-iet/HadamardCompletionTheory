/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P02_05
@[expose] public section
namespace CompletionTheory

def pair24_02_09Rows : Fin 14 → Fin 16 := ![0, 1, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15]
def pair24_02_09Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_02_09Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![30, -28, 8, -8, 0, 0, -4, -14, 16, 0, 10, 12, -2, 4;
     10, -8, 0, -4, 4, -4, 0, -6, 4, 0, 2, 0, -2, 4;
     13, -11, 0, -1, -5, -1, 0, -6, 4, -3, 5, 9, -2, -2;
     -10, 12, -2, 0, -4, 4, 4, 8, -8, 0, 0, -6, 4, -2;
     18, -16, 2, -8, 0, 0, -4, -8, 4, 0, 4, 6, 4, -2;
     29, -27, 4, -9, -1, -5, -8, -10, 16, -3, 9, 9, -2, -2;
     -10, 12, 4, 0, -4, 4, 4, 2, -8, 0, -6, 0, -2, 4;
     4, -2, 0, 2, -2, 2, 0, -6, 4, -6, -4, 6, -2, 4;
     -16, 18, -2, 6, 2, -2, 4, 8, -8, 6, -6, -12, 4, -2;
     -25, 27, -8, 9, 5, 1, 4, 14, -8, 3, -9, -9, -2, -2;
     -14, 16, -6, 8, 4, -4, 0, 12, -8, 0, -4, -6, 4, -2;
     -17, 19, 0, 5, 1, 5, 0, 6, -8, 3, -1, -9, -2, -2;
     2, -2, -4, 2, 2, -2, -4, 4, 0, 6, 2, -6, 0, 0;
     10, -10, 4, -2, -2, 2, 4, -4, 0, -6, -2, 6, 0, 0;
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

def pair24_02_09Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-72, -120, -72, -72, -96, 0, -48, -48, -120, -48;
     -24, -24, -24, -24, -48, 0, 0, -24, -24, -24;
     -36, -48, -12, -36, -24, -12, -36, 0, -60, -24;
     24, 48, 24, 48, 48, -12, 0, 12, 36, 36;
     -48, -48, -48, -48, -48, -12, -48, -36, -60, -12;
     -60, -96, -84, -84, -96, -12, -60, -24, -108, -48;
     0, 24, 48, 48, 48, 24, 24, 0, 24, 24;
     -24, -24, 24, -24, 0, 24, 0, 0, -24, -24;
     48, 72, 24, 48, 48, -12, 48, 12, 84, 36;
     84, 96, 60, 60, 72, 12, 60, 48, 108, 24;
     48, 72, 24, 24, 48, -12, 24, 36, 84, 12;
     60, 48, 36, 60, 48, 12, 36, 24, 60, 48;
     24, 0, -24, 0, -24, -24, 0, 0, 24, 0;
     -48, -24, 0, -24, 0, 0, -24, -24, -48, -24;
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
theorem pair24_02_09_certificate :
    pair24_02_09Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_02_09Rows id +
      pair24_02_09Inverse * integerInformationSelector pair24_02_09Free = (24 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_02_09_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_02_09Inverse.mulVec (fun t => if b t then 1 else -1) k = 24 ∨
      pair24_02_09Inverse.mulVec (fun t => if b t then 1 else -1) k = -24) →
    IntegerScaledHalfPattern 24 (1)
      (∑ k, encodedIntFrame base24Masks 2 k * pair24_02_09Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 9 k * pair24_02_09Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_02_09_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {2, 9} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 2 k * x k) (∑ k, base24Frame 9 k * x k) := by
  have h := order24_integer_pair_lift 2 9 pair24_02_09Rows pair24_02_09Free
    pair24_02_09Left pair24_02_09Inverse 24 (1) (by norm_num) (by decide +kernel)
    pair24_02_09_certificate pair24_02_09_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
