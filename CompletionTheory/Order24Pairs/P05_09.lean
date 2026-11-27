/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P04_15
@[expose] public section
namespace CompletionTheory

def pair24_05_09Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 6, 7, 8, 10, 11, 12, 13, 14, 15]
def pair24_05_09Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_05_09Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![15, -14, 0, 4, -4, 0, -2, -7, 8, 0, 5, 6, -1, 2;
     35, -34, -4, 4, -12, -4, -4, -15, 14, -2, 11, 10, -1, 2;
     -31, 32, 5, -5, 12, 2, 5, 12, -13, 1, -10, -8, -1, -1;
     -35, 36, 4, -5, 10, 4, 6, 16, -16, 2, -10, -13, 2, -1;
     9, -8, 0, 1, -4, 0, -2, -4, 2, 0, 2, 3, 2, -1;
     7, -6, 1, 1, -2, -2, -3, -2, 5, -1, 2, 2, -1, -1;
     -35, 36, 4, -2, 10, 4, 6, 13, -16, 2, -13, -10, -1, 2;
     -13, 14, 2, -2, 6, 2, 2, 3, -4, -2, -7, -2, -1, 2;
     7, -6, -2, 1, -2, -2, 0, -2, 2, 2, 2, -1, 2, -1;
     25, -24, -5, 1, -8, -2, -3, -8, 11, -1, 8, 8, -1, -1;
     23, -22, -4, 1, -6, -4, -4, -6, 8, -2, 8, 7, 2, -1;
     -1, 2, -1, 1, 0, 2, -1, 0, -1, 1, 2, -2, -1, -1;
     16, -16, -2, 0, -4, -2, -4, -4, 6, 2, 6, 2, 0, 0;
     -10, 10, 2, 0, 4, 2, 4, 4, -6, -2, -6, -2, 0, 0;
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

def pair24_05_09Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-36, -60, -36, -36, -48, 0, -24, -24, -60, -24;
     -84, -108, -84, -84, -120, -24, -72, -60, -132, -60;
     72, 96, 84, 72, 108, 24, 72, 60, 120, 48;
     84, 120, 84, 96, 120, 18, 72, 54, 138, 66;
     -24, -24, -24, -24, -24, -6, -24, -18, -30, -6;
     -12, -24, -24, -24, -24, 0, -12, 0, -24, -12;
     72, 108, 96, 96, 120, 36, 84, 48, 132, 60;
     24, 36, 48, 24, 48, 24, 36, 24, 48, 12;
     -12, -12, -24, -12, -24, -18, -12, -18, -18, -6;
     -48, -72, -60, -60, -84, -24, -60, -36, -96, -48;
     -48, -60, -60, -60, -72, -30, -60, -30, -78, -42;
     12, 0, 0, 12, 0, 0, 0, 0, 0, 12;
     -24, -48, -48, -36, -60, -24, -36, -24, -48, -24;
     12, 36, 36, 24, 48, 12, 24, 12, 36, 12;
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
theorem pair24_05_09_certificate :
    pair24_05_09Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_05_09Rows id +
      pair24_05_09Inverse * integerInformationSelector pair24_05_09Free = (12 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_05_09_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_05_09Inverse.mulVec (fun t => if b t then 1 else -1) k = 12 ∨
      pair24_05_09Inverse.mulVec (fun t => if b t then 1 else -1) k = -12) →
    IntegerScaledHalfPattern 12 (1)
      (∑ k, encodedIntFrame base24Masks 5 k * pair24_05_09Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 9 k * pair24_05_09Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_05_09_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {5, 9} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 5 k * x k) (∑ k, base24Frame 9 k * x k) := by
  have h := order24_integer_pair_lift 5 9 pair24_05_09Rows pair24_05_09Free
    pair24_05_09Left pair24_05_09Inverse 12 (1) (by norm_num) (by decide +kernel)
    pair24_05_09_certificate pair24_05_09_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
