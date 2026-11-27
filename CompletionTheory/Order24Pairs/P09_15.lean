/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P09_11
@[expose] public section
namespace CompletionTheory

def pair24_09_15Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14]
def pair24_09_15Free : Fin 10 → Fin 24 := ![11, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_09_15Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![24, -15, -4, 16, -7, 1, 13, -10, -15, 12, 7, 22, 1, -9;
     24, -15, -8, 8, -11, 5, 5, -8, -15, 6, 5, 20, -7, -9;
     -15, 15, 8, -8, 11, -5, -5, 8, 6, -6, -5, -11, 7, 0;
     -12, 12, 3, -6, 0, -6, 0, 9, 12, -9, -3, -6, -3, 9;
     -15, 15, 9, -6, 3, 3, -3, 3, 6, -9, 0, -15, 0, 9;
     -6, 6, 10, -4, 4, 2, -10, -2, 6, 6, -4, -10, 2, 0;
     9, 0, -10, 16, -10, -8, 16, -4, -9, -6, 4, 13, -2, -9;
     15, -6, -8, 8, -2, -4, 14, -8, -15, 6, -4, 11, 2, -9;
     -6, 6, 1, -4, 4, 2, -10, 7, 6, -3, 5, -10, -7, 9;
     3, -3, -2, -10, 1, 5, -7, 4, 6, 6, -1, -7, 5, 0;
     -3, 3, 1, -10, 7, 5, -13, 1, 12, -3, -4, -7, 2, 9;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     18, -18, -2, -4, -2, 2, -4, -8, 0, 6, 8, 8, -4, 0;
     -15, 15, 4, 2, 7, -1, 5, 10, 6, -12, -7, -13, -1, 0;
     15, -15, -2, 2, -5, -1, -1, -2, -6, 6, -1, 5, 5, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def pair24_09_15Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-72, -132, -72, 0, -96, 12, -36, -48, -120, 24;
     -72, -84, -72, 0, -120, -12, -36, -60, -96, 12;
     36, 48, 72, 0, 84, 12, 36, 60, 60, -12;
     36, 72, 36, 36, 72, -18, 0, 18, 54, 18;
     36, 72, 36, 0, 72, 18, 36, 18, 90, 18;
     36, 24, 0, -36, 24, 24, 36, 48, 48, -24;
     -72, -60, 0, 72, -24, 12, -36, -48, -84, 60;
     -72, -84, 0, 0, -48, 24, -36, -24, -96, 12;
     36, 60, 0, 0, 24, -30, 36, -6, 66, -6;
     36, 24, 0, -36, -12, -12, 0, 12, 12, -60;
     36, 60, 0, -36, 24, -30, 0, 30, 66, -42;
     36, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, -48, -72, -36, -84, -48, -36, -24, -24, -24;
     0, 60, 72, 36, 96, 24, 36, 12, 48, 12;
     0, -48, -36, -36, -48, -12, -36, -24, -60, -24;
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
theorem pair24_09_15_certificate :
    pair24_09_15Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_09_15Rows id +
      pair24_09_15Inverse * integerInformationSelector pair24_09_15Free = (36 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_09_15_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_09_15Inverse.mulVec (fun t => if b t then 1 else -1) k = 36 ∨
      pair24_09_15Inverse.mulVec (fun t => if b t then 1 else -1) k = -36) →
    IntegerScaledHalfPattern 36 (1)
      (∑ k, encodedIntFrame base24Masks 9 k * pair24_09_15Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 15 k * pair24_09_15Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_09_15_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {9, 15} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 9 k * x k) (∑ k, base24Frame 15 k * x k) := by
  have h := order24_integer_pair_lift 9 15 pair24_09_15Rows pair24_09_15Free
    pair24_09_15Left pair24_09_15Inverse 36 (1) (by norm_num) (by decide +kernel)
    pair24_09_15_certificate pair24_09_15_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
