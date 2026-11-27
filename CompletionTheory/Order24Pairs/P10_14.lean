/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P09_15
@[expose] public section
namespace CompletionTheory

def pair24_10_14Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 15]
def pair24_10_14Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_10_14Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![-21, 27, 16, 8, 13, 5, 5, 4, 6, 6, 5, -7, -1, 6;
     9, -3, 4, -4, -5, 11, -13, 4, -6, 6, -1, -1, -7, 6;
     18, -12, 4, -4, 4, -16, -4, 4, -6, 6, -10, 8, 20, -12;
     12, -6, -8, 2, -14, -10, 14, 4, 0, -12, 2, 14, -4, 6;
     6, 0, 4, 2, -8, 8, 8, -8, -12, -12, 8, -4, 2, 6;
     -24, 30, 16, -4, 10, 2, -10, -8, 18, 6, -4, -10, -10, -12;
     39, -33, -8, 20, -23, -19, 5, 4, -18, 6, -7, 5, 23, 6;
     -9, 15, 4, -4, 13, -7, 5, 4, -6, 6, -19, -19, 11, 6;
     -6, 12, -8, 2, 4, 8, -4, 4, 0, -12, 20, -4, -22, 6;
     -6, 12, -8, -16, 4, 8, -4, 4, 18, 6, 2, -4, -4, -12;
     0, 6, -8, -10, 10, 14, -10, -8, 12, -12, 2, 2, -4, 6;
     18, -12, -8, 8, -8, -4, 8, -8, -6, 6, 2, 20, -4, -12;
     6, -6, 0, -12, 6, 6, -6, -12, 12, 0, 18, 6, -18, 0;
     30, -30, 0, 12, -6, -6, 6, 12, -12, 0, -18, -6, 18, 0;
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

def pair24_10_14Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![36, 24, 36, 36, 96, 60, 108, 48, 84, 48;
     -36, 24, -36, -36, -48, -12, 36, -24, 12, -24;
     -72, -48, 0, -72, 24, -48, -72, 48, -96, -24;
     0, -48, 0, 72, -48, -12, -72, -60, -60, 12;
     0, -48, 0, 0, -48, 60, 0, -60, 12, 12;
     72, 96, 0, 0, 96, 24, 72, 120, 120, 48;
     -180, -120, -36, -36, -48, -12, -108, -96, -204, -24;
     -36, 24, 108, -36, 96, 60, 36, 48, 12, -24;
     72, 24, 0, 72, -48, -12, 72, -60, 84, 12;
     72, 96, 0, 0, 24, -48, 0, 48, 48, -24;
     72, 24, 0, 0, -48, -12, 0, 12, 84, -60;
     0, -48, -72, 0, -48, -48, -72, -24, -96, 48;
     72, 0, -72, 0, -72, -72, 0, 0, 72, 0;
     -144, -72, 0, -72, 0, 0, -72, -72, -144, -72;
     72, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 72, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 72, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 72, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 72, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 72, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 72, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 72, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 72, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 72]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_10_14_certificate :
    pair24_10_14Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_10_14Rows id +
      pair24_10_14Inverse * integerInformationSelector pair24_10_14Free = (72 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_10_14_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_10_14Inverse.mulVec (fun t => if b t then 1 else -1) k = 72 ∨
      pair24_10_14Inverse.mulVec (fun t => if b t then 1 else -1) k = -72) →
    IntegerScaledHalfPattern 72 (1)
      (∑ k, encodedIntFrame base24Masks 10 k * pair24_10_14Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 14 k * pair24_10_14Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_10_14_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {10, 14} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 10 k * x k) (∑ k, base24Frame 14 k * x k) := by
  have h := order24_integer_pair_lift 10 14 pair24_10_14Rows pair24_10_14Free
    pair24_10_14Left pair24_10_14Inverse 72 (1) (by norm_num) (by decide +kernel)
    pair24_10_14_certificate pair24_10_14_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
