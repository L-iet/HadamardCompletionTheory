/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P02_15
@[expose] public section
namespace CompletionTheory

def pair24_03_07Rows : Fin 14 → Fin 16 := ![0, 1, 2, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15]
def pair24_03_07Free : Fin 10 → Fin 24 := ![13, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_03_07Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![-10, 14, 12, 6, -2, -6, 12, 20, -4, 2, 2, -2, 16, -12;
     8, -4, 0, -4, 12, -4, -12, -8, 8, 4, 0, -4, -12, 16;
     8, -4, 0, 4, -4, 4, -12, -12, 8, 0, 4, 12, -16, 8;
     11, -7, -6, -11, -7, 7, 0, -6, 2, 3, 13, -3, 2, 2;
     -7, 11, 6, -1, 3, 5, 0, -2, -10, 1, -9, -1, 6, -2;
     -10, 14, 12, 6, -2, -6, 12, 8, -4, -10, -10, -2, 4, -12;
     -16, 20, 0, -4, -12, -4, 12, 16, -16, 4, 0, -4, 12, -8;
     -4, 8, 0, 8, 0, 8, -12, -8, 8, -8, -12, 8, -12, 16;
     11, -7, -6, -3, 1, -9, 0, 2, 2, 11, 5, -11, 10, -6;
     26, -22, -12, -6, 10, 6, -12, -16, 20, 2, 2, 10, -20, 12;
     11, -7, -6, 5, 9, -1, 0, -14, 2, -5, -3, 5, -6, 10;
     -4, 8, 0, 0, -8, 0, 12, 20, -16, -4, 8, -8, 16, -24;
     12, -12, 0, 4, 4, 4, 0, -8, 0, 4, -4, -4, -8, 8;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     12, -12, 0, -4, -4, -4, 0, 8, 0, -4, 4, 4, 8, -8;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def pair24_03_07Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![24, 72, -48, -24, 96, -48, 24, 72, 48, 72;
     0, -48, 0, 0, -96, 48, 48, -48, 0, -48;
     0, -96, 48, 0, -48, 48, 0, 0, -48, -48;
     12, -36, -24, 36, -48, -24, -60, -36, -48, 12;
     -12, 36, 24, 12, 48, 24, 12, -12, 48, 36;
     -24, 72, 0, -24, 96, 0, 24, 72, 48, 24;
     48, 96, 0, 48, 96, -48, 0, 48, 48, 96;
     0, -48, 96, 0, 0, 96, 48, 0, 0, -48;
     12, 12, -72, -12, -48, -72, -12, -36, 0, 12;
     -24, -120, 0, -24, -144, 48, -24, -72, -96, -120;
     -36, -36, 24, -12, -48, 24, -12, -36, 0, -84;
     0, 96, -48, 0, 96, -96, -48, 48, 0, 96;
     -48, -48, 0, 0, -48, 0, 0, -48, 0, -48;
     48, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, -48, -48, 0, -48, -48, 0, -48, 0;
     0, 48, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 48, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 48, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 48, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 48, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 48, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 48, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 48, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 48]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_03_07_certificate :
    pair24_03_07Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_03_07Rows id +
      pair24_03_07Inverse * integerInformationSelector pair24_03_07Free = (48 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_03_07_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_03_07Inverse.mulVec (fun t => if b t then 1 else -1) k = 48 ∨
      pair24_03_07Inverse.mulVec (fun t => if b t then 1 else -1) k = -48) →
    IntegerScaledHalfPattern 48 (1)
      (∑ k, encodedIntFrame base24Masks 3 k * pair24_03_07Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 7 k * pair24_03_07Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_03_07_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {3, 7} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 3 k * x k) (∑ k, base24Frame 7 k * x k) := by
  have h := order24_integer_pair_lift 3 7 pair24_03_07Rows pair24_03_07Free
    pair24_03_07Left pair24_03_07Inverse 48 (1) (by norm_num) (by decide +kernel)
    pair24_03_07_certificate pair24_03_07_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
