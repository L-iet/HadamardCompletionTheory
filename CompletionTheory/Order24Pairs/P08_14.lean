/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P08_10
@[expose] public section
namespace CompletionTheory

def pair24_08_14Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 15]
def pair24_08_14Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_08_14Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![-6, 12, 14, 10, 8, 4, 4, 2, 6, 6, 4, -2, 4, 6;
     -6, 12, 6, -6, 0, 12, -12, 6, 6, -6, 0, -6, -12, 6;
     3, 3, 6, -6, 9, -15, -3, 6, 6, -6, -9, 3, 15, -12;
     12, -6, -8, 2, -14, -10, 14, 4, -12, 0, 2, 14, -4, 6;
     -24, 30, 8, -2, 2, 10, 10, -4, -12, -12, 10, -14, -8, 6;
     21, -15, 10, 2, -5, -1, -13, -14, 6, 18, -7, 5, 5, -12;
     -6, 12, -2, 14, -8, -16, 8, 10, 6, -18, -4, -10, 8, 6;
     -24, 30, 6, -6, 18, -6, 6, 6, 6, -6, -18, -24, 6, 6;
     -6, 12, -8, 2, 4, 8, -4, 4, -12, 0, 20, -4, -22, 6;
     39, -33, -14, -10, -11, 5, -7, -2, 6, 18, -1, 11, 11, -12;
     30, -24, -12, -6, 0, 12, -12, -12, -12, 12, 0, 12, 6, 6;
     3, 3, -6, 6, -3, -3, 9, -6, 6, -6, 3, 15, -9, -12;
     36, -36, -4, -8, -4, 4, -8, -16, 0, 12, 16, 16, -8, 0;
     0, 0, 4, 8, 4, -4, 8, 16, 0, -12, -16, -16, 8, 0;
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

def pair24_08_14Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![0, -24, 0, 0, 48, 48, 72, 24, 24, 24;
     0, 72, 0, 0, 0, 0, 72, 0, 72, 0;
     -36, 0, 36, -36, 72, -36, -36, 72, -36, 0;
     0, -48, 0, 72, -48, -12, -72, -60, -60, 12;
     72, 48, 72, 72, 48, 84, 72, -12, 132, 60;
     -36, -48, -108, -108, -48, -12, -36, 48, -60, -24;
     -72, 24, 72, 72, 96, 24, 0, -24, -24, 48;
     0, 72, 144, 0, 144, 72, 72, 72, 72, 0;
     72, 24, 0, 72, -48, -12, 72, -60, 84, 12;
     -36, -48, -108, -108, -120, -84, -108, -24, -132, -96;
     0, -72, -72, -72, -144, -36, -72, -36, -36, -108;
     36, 0, -36, 36, 0, -36, -36, 0, -36, 72;
     0, -96, -144, -72, -168, -96, -72, -48, -48, -48;
     -72, 24, 72, 0, 96, 24, 0, -24, -24, -24;
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
theorem pair24_08_14_certificate :
    pair24_08_14Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_08_14Rows id +
      pair24_08_14Inverse * integerInformationSelector pair24_08_14Free = (72 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_08_14_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_08_14Inverse.mulVec (fun t => if b t then 1 else -1) k = 72 ∨
      pair24_08_14Inverse.mulVec (fun t => if b t then 1 else -1) k = -72) →
    IntegerScaledHalfPattern 72 (1)
      (∑ k, encodedIntFrame base24Masks 8 k * pair24_08_14Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 14 k * pair24_08_14Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_08_14_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {8, 14} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 8 k * x k) (∑ k, base24Frame 14 k * x k) := by
  have h := order24_integer_pair_lift 8 14 pair24_08_14Rows pair24_08_14Free
    pair24_08_14Left pair24_08_14Inverse 72 (1) (by norm_num) (by decide +kernel)
    pair24_08_14_certificate pair24_08_14_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
