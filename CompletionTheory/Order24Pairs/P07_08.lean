/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P06_12
@[expose] public section
namespace CompletionTheory

def pair24_07_08Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 9, 10, 11, 12, 13, 14, 15]
def pair24_07_08Free : Fin 10 → Fin 24 := ![13, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_07_08Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![-5, 13, 18, 12, 9, 5, 3, 10, 10, 7, 1, 5, 2, 6;
     1, 7, 6, -12, -5, 15, -23, 14, -2, 5, 3, -17, 6, 2;
     1, 7, 6, -12, 11, -17, -7, 6, -2, -3, 11, 15, -2, -14;
     22, -14, -12, 0, -22, -14, 14, -12, 4, 6, 26, -6, 4, 4;
     -14, 22, 12, 0, -2, 6, 10, -4, -20, 2, -18, -2, 12, -4;
     -5, 13, 18, 12, 9, 5, 3, -14, 10, -17, -23, 5, -22, 6;
     -17, 25, -6, 12, -11, -15, 7, 2, -14, 11, -3, 1, -6, 14;
     -23, 31, 6, -12, 19, -9, 1, 14, -2, -19, -21, 7, 6, 2;
     22, -14, -12, 0, -6, 2, -18, 4, 4, 22, 10, -22, 20, -12;
     37, -29, -18, -12, -9, 11, -3, -2, 22, 1, 7, 11, -10, -6;
     22, -14, -12, 0, 10, 18, -2, -28, 4, -10, -6, 10, -12, 20;
     7, 1, -6, 12, -3, -7, 15, 10, -14, -5, 13, -7, 2, -18;
     24, -24, 0, 0, 8, 8, 8, -16, 0, 8, -8, -8, -16, 16;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     24, -24, 0, 0, -8, -8, -8, 16, 0, -8, 8, 8, 16, -16;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def pair24_07_08Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![12, -36, -24, -12, 48, 48, 84, 36, 24, 36;
     36, 84, -72, -36, -48, -48, 60, 12, 72, 12;
     36, -12, 24, -36, 48, -48, -36, 108, -24, 12;
     24, -72, -48, 72, -96, -48, -120, -72, -96, 24;
     -24, 72, 48, 24, 96, 48, 24, -24, 96, 72;
     -84, -36, 72, -12, 48, 144, 84, 36, 24, -60;
     60, 12, 72, 132, 48, 48, 36, -12, 24, 84;
     36, 84, 120, -36, 144, 48, 60, 108, 72, 12;
     24, 24, -144, -24, -96, -144, -24, -72, 0, 24;
     -12, -60, -72, -84, -144, -48, -84, -36, -120, -132;
     -72, -72, 48, -24, -96, 48, -24, -72, 0, -168;
     -36, 12, -24, 36, 48, -48, -60, -12, -72, 84;
     -96, -96, 0, 0, -96, 0, 0, -96, 0, -96;
     96, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, -96, -96, 0, -96, -96, 0, -96, 0;
     0, 96, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 96, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 96, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 96, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 96, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 96, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 96, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 96, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 96]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_07_08_certificate :
    pair24_07_08Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_07_08Rows id +
      pair24_07_08Inverse * integerInformationSelector pair24_07_08Free = (96 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_07_08_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_07_08Inverse.mulVec (fun t => if b t then 1 else -1) k = 96 ∨
      pair24_07_08Inverse.mulVec (fun t => if b t then 1 else -1) k = -96) →
    IntegerScaledHalfPattern 96 (1)
      (∑ k, encodedIntFrame base24Masks 7 k * pair24_07_08Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 8 k * pair24_07_08Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_07_08_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {7, 8} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 7 k * x k) (∑ k, base24Frame 8 k * x k) := by
  have h := order24_integer_pair_lift 7 8 pair24_07_08Rows pair24_07_08Free
    pair24_07_08Left pair24_07_08Inverse 96 (1) (by norm_num) (by decide +kernel)
    pair24_07_08_certificate pair24_07_08_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
