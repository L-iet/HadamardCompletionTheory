/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P03_05
@[expose] public section
namespace CompletionTheory

def pair24_03_09Rows : Fin 14 → Fin 16 := ![0, 1, 2, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15]
def pair24_03_09Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_03_09Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![-30, 32, 8, 12, 4, 4, 4, 10, -8, 4, -10, -8, -2, 4;
     10, -8, 0, -4, 4, -4, 0, -6, 4, 0, 2, 0, -2, 4;
     13, -11, 0, -1, -5, -1, 0, -6, 4, -3, 5, 9, -2, -2;
     5, -3, -2, -5, -5, 3, 2, 2, -2, -1, 5, -1, 4, -2;
     3, -1, 2, -3, 1, 1, -2, -2, -2, 1, -1, 1, 4, -2;
     -1, 3, 4, 1, 1, -3, -4, 2, 4, -1, -1, -1, -2, -2;
     -40, 42, 4, 10, -2, 6, 8, 14, -20, 2, -16, -10, -2, 4;
     4, -2, 0, 2, -2, 2, 0, -6, 4, -6, -4, 6, -2, 4;
     -1, 3, -2, 1, 1, -3, 2, 2, -2, 5, -1, -7, 4, -2;
     35, -33, -8, -11, 1, -3, -4, -10, 16, -1, 11, 11, -2, -2;
     31, -29, -6, -7, 1, -7, -6, -6, 10, -3, 11, 9, 4, -2;
     -17, 19, 0, 5, 1, 5, 0, 6, -8, 3, -1, -9, -2, -2;
     32, -32, -4, -8, 0, -4, -8, -8, 12, 4, 12, 4, 0, 0;
     -20, 20, 4, 8, 0, 4, 8, 8, -12, -4, -12, -4, 0, 0;
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

def pair24_03_09Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![72, 72, 72, 72, 96, 48, 96, 48, 120, 48;
     -24, -24, -24, -24, -48, 0, 0, -24, -24, -24;
     -36, -48, -12, -36, -24, -12, -36, 0, -60, -24;
     -12, 0, -12, 12, 0, -24, -36, -12, -24, 12;
     -12, 0, -12, -12, 0, 0, -12, -12, 0, 12;
     12, 0, -12, -12, 0, 12, 12, 24, 12, 0;
     72, 120, 120, 120, 144, 48, 96, 48, 144, 72;
     -24, -24, 24, -24, 0, 24, 0, 0, -24, -24;
     12, 24, -12, 12, 0, -24, 12, -12, 24, 12;
     -60, -96, -84, -84, -120, -36, -84, -48, -132, -72;
     -60, -72, -84, -84, -96, -48, -84, -36, -96, -60;
     60, 48, 36, 60, 48, 12, 36, 24, 60, 48;
     -48, -96, -96, -72, -120, -48, -72, -48, -96, -48;
     24, 72, 72, 48, 96, 24, 48, 24, 72, 24;
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
theorem pair24_03_09_certificate :
    pair24_03_09Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_03_09Rows id +
      pair24_03_09Inverse * integerInformationSelector pair24_03_09Free = (24 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_03_09_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_03_09Inverse.mulVec (fun t => if b t then 1 else -1) k = 24 ∨
      pair24_03_09Inverse.mulVec (fun t => if b t then 1 else -1) k = -24) →
    IntegerScaledHalfPattern 24 (1)
      (∑ k, encodedIntFrame base24Masks 3 k * pair24_03_09Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 9 k * pair24_03_09Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_03_09_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {3, 9} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 3 k * x k) (∑ k, base24Frame 9 k * x k) := by
  have h := order24_integer_pair_lift 3 9 pair24_03_09Rows pair24_03_09Free
    pair24_03_09Left pair24_03_09Inverse 24 (1) (by norm_num) (by decide +kernel)
    pair24_03_09_certificate pair24_03_09_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
