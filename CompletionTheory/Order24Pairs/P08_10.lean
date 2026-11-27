/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P07_13
@[expose] public section
namespace CompletionTheory

def pair24_08_10Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 12, 13, 14, 15]
def pair24_08_10Free : Fin 10 → Fin 24 := ![13, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_08_10Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![-15, 21, 16, 14, 13, 5, 11, 10, 0, -1, -13, 5, -6, 12;
     3, 3, 4, -10, -5, 11, -19, -2, 12, 5, 5, -13, 6, 0;
     3, 3, 4, -10, 7, -13, -7, -2, 6, -1, 11, 11, 0, -12;
     12, -6, -8, 2, -14, -10, 14, 4, -12, 2, 14, -4, 0, 6;
     12, -6, 4, -10, -14, 2, -10, -20, 12, 14, 14, -4, 24, -18;
     -15, 21, 16, 14, 13, 5, 11, 10, -18, -19, -31, 5, -24, 12;
     3, 3, -8, 2, -17, -13, -7, -14, 12, 17, 17, -1, 6, 0;
     -15, 21, 4, -10, 13, -7, -1, -2, 12, -13, -13, 5, 6, 0;
     12, -6, -8, 2, -2, 2, -10, 4, 0, 14, 2, -16, 12, -6;
     3, 3, -8, 2, 7, 11, 17, 22, -18, -13, -25, 11, -24, 12;
     12, -6, -8, 2, 10, 14, 2, 4, -24, -10, -10, 8, -12, 18;
     21, -15, -8, 2, -11, -7, -1, -14, 18, 5, 29, -7, 12, -24;
     18, -18, 0, 0, 6, 6, 6, 0, -12, 6, -6, -6, -12, 12;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     18, -18, 0, 0, -6, -6, -6, 0, 12, -6, 6, 6, 12, -12;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def pair24_08_10Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-36, -12, 72, 36, 96, 96, 108, 12, 48, 12;
     36, 60, -72, -36, -48, -48, 36, 12, 48, 12;
     36, -12, 0, -36, 24, -48, -36, 84, -24, 12;
     0, -48, 0, 72, -48, -12, -72, -60, -60, 12;
     72, 24, -144, -72, -48, -84, -72, 12, 12, 84;
     -108, -12, 144, 36, 96, 168, 108, 12, 48, -60;
     108, -12, -72, 36, -48, -48, -36, 12, -24, 84;
     36, 60, 72, -36, 96, 24, 36, 84, 48, 12;
     0, 24, -72, 0, -48, -84, 0, -60, 12, 12;
     -108, -12, 144, 36, 24, 96, 36, -60, -24, -132;
     -72, -48, 72, 0, -48, 60, 0, -60, 12, -132;
     36, -12, -144, -36, -48, -120, -108, 12, -96, 84;
     -72, -72, 0, 0, -72, 0, 0, -72, 0, -72;
     72, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, -72, -72, 0, -72, -72, 0, -72, 0;
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
theorem pair24_08_10_certificate :
    pair24_08_10Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_08_10Rows id +
      pair24_08_10Inverse * integerInformationSelector pair24_08_10Free = (72 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_08_10_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_08_10Inverse.mulVec (fun t => if b t then 1 else -1) k = 72 ∨
      pair24_08_10Inverse.mulVec (fun t => if b t then 1 else -1) k = -72) →
    IntegerScaledHalfPattern 72 (1)
      (∑ k, encodedIntFrame base24Masks 8 k * pair24_08_10Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 10 k * pair24_08_10Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_08_10_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {8, 10} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 8 k * x k) (∑ k, base24Frame 10 k * x k) := by
  have h := order24_integer_pair_lift 8 10 pair24_08_10Rows pair24_08_10Free
    pair24_08_10Left pair24_08_10Inverse 72 (1) (by norm_num) (by decide +kernel)
    pair24_08_10_certificate pair24_08_10_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
