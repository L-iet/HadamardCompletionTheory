/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P09_10
@[expose] public section
namespace CompletionTheory

def pair24_09_14Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 15]
def pair24_09_14Free : Fin 10 → Fin 24 := ![11, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_09_14Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![-12, 12, 11, 1, 8, 4, -2, 5, 3, 3, 1, -11, 4, 9;
     -12, 12, 7, -7, 4, 8, -10, 7, 3, -3, -1, -13, -4, 9;
     -15, 15, 8, -8, 11, -5, -5, 8, 6, -6, -5, -11, 7, 0;
     24, -15, -12, 9, -15, -9, 15, -6, -6, 0, 3, 27, -6, -9;
     21, -12, -6, 9, -12, 0, 12, -12, -12, 0, 6, 18, -3, -9;
     -6, 6, 10, -4, 4, 2, -10, -2, 6, 6, -4, -10, 2, 0;
     -27, 27, 5, 1, 5, -5, 1, 11, 9, -15, -2, -20, 1, 9;
     -21, 21, 7, -7, 13, -1, -1, 7, 3, -3, -10, -22, 5, 9;
     30, -21, -14, 11, -11, -1, 5, -8, -12, 6, 11, 23, -10, -9;
     3, -3, -2, -10, 1, 5, -7, 4, 6, 6, -1, -7, 5, 0;
     33, -24, -14, 5, -8, 2, 2, -14, -6, 6, 2, 26, -1, -9;
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

def pair24_09_14Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![36, 12, 36, 0, 48, 48, 72, 24, 60, -12;
     36, 60, 36, 0, 24, 24, 72, 12, 84, -24;
     36, 48, 72, 0, 84, 12, 36, 60, 60, -12;
     -72, -72, -72, 36, -72, -54, -108, -54, -126, 54;
     -72, -72, -72, 0, -72, -18, -72, -54, -90, 54;
     36, 24, 0, -36, 24, 24, 36, 48, 48, -24;
     36, 84, 108, 72, 120, 48, 72, 24, 96, 24;
     36, 60, 108, 0, 96, 60, 72, 48, 84, -24;
     -72, -84, -108, 0, -120, -66, -72, -78, -114, 30;
     36, 24, 0, -36, -12, -12, 0, 12, 12, -60;
     -72, -84, -108, -36, -120, -66, -108, -42, -114, -6;
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
theorem pair24_09_14_certificate :
    pair24_09_14Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_09_14Rows id +
      pair24_09_14Inverse * integerInformationSelector pair24_09_14Free = (36 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_09_14_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_09_14Inverse.mulVec (fun t => if b t then 1 else -1) k = 36 ∨
      pair24_09_14Inverse.mulVec (fun t => if b t then 1 else -1) k = -36) →
    IntegerScaledHalfPattern 36 (1)
      (∑ k, encodedIntFrame base24Masks 9 k * pair24_09_14Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 14 k * pair24_09_14Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_09_14_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {9, 14} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 9 k * x k) (∑ k, base24Frame 14 k * x k) := by
  have h := order24_integer_pair_lift 9 14 pair24_09_14Rows pair24_09_14Free
    pair24_09_14Left pair24_09_14Inverse 36 (1) (by norm_num) (by decide +kernel)
    pair24_09_14_certificate pair24_09_14_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
