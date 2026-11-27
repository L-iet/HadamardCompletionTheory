/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P05_10
@[expose] public section
namespace CompletionTheory

def pair24_05_14Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 15]
def pair24_05_14Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_05_14Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![9, -8, 1, 3, -2, 0, -1, -4, 1, 5, 0, 3, 4, 1;
     29, -28, -3, 3, -10, -4, -3, -12, 1, 11, -2, 9, 8, 1;
     -37, 38, 6, -6, 14, 2, 6, 15, 1, -16, 1, -12, -10, -2;
     -23, 24, 2, -3, 6, 4, 4, 10, -2, -10, 2, -6, -9, 1;
     21, -20, -2, 3, -8, 0, -4, -10, -2, 8, 0, 6, 7, 1;
     1, 0, 2, 0, 0, -2, -2, 1, 1, 2, -1, 0, 0, -2;
     -41, 42, 5, -3, 12, 4, 7, 16, 1, -19, 2, -15, -12, 1;
     -19, 20, 3, -3, 8, 2, 3, 6, 1, -7, -2, -9, -4, 1;
     19, -18, -4, 3, -6, -2, -2, -8, -2, 8, 2, 6, 3, 1;
     19, -18, -4, 0, -6, -2, -2, -5, 1, 8, -1, 6, 6, -2;
     35, -34, -6, 3, -10, -4, -6, -12, -2, 14, -2, 12, 11, 1;
     -7, 8, 0, 0, 2, 2, 0, 3, 1, -4, 1, 0, -4, -2;
     16, -16, -2, 0, -4, -2, -4, -4, 0, 6, 2, 6, 2, 0;
     -10, 10, 2, 0, 4, 2, 4, 4, 0, -6, -2, -6, -2, 0;
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

def pair24_05_14Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-24, -36, -24, -24, -24, 0, -12, -12, -36, -12;
     -72, -84, -72, -72, -96, -24, -60, -48, -108, -48;
     84, 120, 96, 84, 132, 24, 84, 72, 144, 60;
     60, 72, 60, 72, 72, 18, 48, 30, 90, 42;
     -48, -72, -48, -48, -72, -6, -48, -42, -78, -30;
     0, 0, -12, -12, 0, 0, 0, 12, 0, 0;
     84, 132, 108, 108, 144, 36, 96, 60, 156, 72;
     36, 60, 60, 36, 72, 24, 48, 36, 72, 24;
     -36, -60, -48, -36, -72, -18, -36, -42, -66, -30;
     -36, -48, -48, -48, -60, -24, -48, -24, -72, -36;
     -72, -108, -84, -84, -120, -30, -84, -54, -126, -66;
     24, 24, 12, 24, 24, 0, 12, 12, 24, 24;
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
theorem pair24_05_14_certificate :
    pair24_05_14Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_05_14Rows id +
      pair24_05_14Inverse * integerInformationSelector pair24_05_14Free = (12 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_05_14_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_05_14Inverse.mulVec (fun t => if b t then 1 else -1) k = 12 ∨
      pair24_05_14Inverse.mulVec (fun t => if b t then 1 else -1) k = -12) →
    IntegerScaledHalfPattern 12 (1)
      (∑ k, encodedIntFrame base24Masks 5 k * pair24_05_14Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 14 k * pair24_05_14Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_05_14_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {5, 14} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 5 k * x k) (∑ k, base24Frame 14 k * x k) := by
  have h := order24_integer_pair_lift 5 14 pair24_05_14Rows pair24_05_14Free
    pair24_05_14Left pair24_05_14Inverse 12 (1) (by norm_num) (by decide +kernel)
    pair24_05_14_certificate pair24_05_14_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
