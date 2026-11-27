/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P07_12
@[expose] public section
namespace CompletionTheory

def pair24_08_09Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13, 14, 15]
def pair24_08_09Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_08_09Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![-15, 21, 14, 10, 11, 7, 7, 2, 6, 7, -5, 1, -6, 12;
     -15, 21, 6, -6, 3, 15, -9, 6, -6, 3, -9, -15, -6, 12;
     -6, 12, 6, -6, 12, -12, 0, 6, -6, -6, 0, 12, -6, -6;
     30, -24, -8, 2, -20, -16, 8, 4, 0, -4, 20, 2, 12, -6;
     -6, 12, 8, -2, -4, 4, 4, -4, -12, 4, -8, -2, 12, -6;
     12, -6, 10, 2, -2, 2, -10, -14, 18, -4, 2, 2, -6, -6;
     -15, 21, -2, 14, -5, -13, 11, 10, -18, -1, -13, 5, -6, 12;
     -33, 39, 6, -6, 21, -3, 9, 6, -6, -15, -27, 3, -6, 12;
     12, -6, -8, 2, -2, 2, -10, 4, 0, 14, 2, -16, 12, -6;
     30, -24, -14, -10, -8, 8, -4, -2, 18, 2, 8, 8, -6, -6;
     48, -42, -12, -6, -6, 6, -18, -12, 12, -6, 18, 12, 12, -6;
     -6, 12, -6, 6, 0, 0, 12, -6, -6, 6, 12, -12, -6, -6;
     36, -36, -4, -8, -4, 4, -8, -16, 12, 16, 16, -8, 0, 0;
     0, 0, 4, 8, 4, -4, 8, 16, -12, -16, -16, 8, 0, 0;
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

def pair24_08_09Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![36, -24, 36, 36, 48, 84, 108, 24, 60, 24;
     36, 72, 36, 36, 0, 36, 108, 0, 108, 0;
     0, 0, 72, 0, 72, 0, 0, 72, 0, 0;
     -72, -48, -72, 0, -48, -84, -144, -60, -132, 12;
     0, 48, 0, 0, 48, 12, 0, -12, 60, 60;
     0, -48, -72, -72, -48, 24, 0, 48, -24, -24;
     -36, 24, 108, 108, 96, 60, 36, -24, 12, 48;
     36, 72, 180, 36, 144, 108, 108, 72, 108, 0;
     0, 24, -72, 0, -48, -84, 0, -60, 12, 12;
     0, -48, -72, -72, -120, -48, -72, -24, -96, -96;
     -72, -72, -144, -144, -144, -108, -144, -36, -108, -108;
     72, 0, 0, 72, 0, 0, 0, 0, 0, 72;
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
theorem pair24_08_09_certificate :
    pair24_08_09Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_08_09Rows id +
      pair24_08_09Inverse * integerInformationSelector pair24_08_09Free = (72 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_08_09_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_08_09Inverse.mulVec (fun t => if b t then 1 else -1) k = 72 ∨
      pair24_08_09Inverse.mulVec (fun t => if b t then 1 else -1) k = -72) →
    IntegerScaledHalfPattern 72 (1)
      (∑ k, encodedIntFrame base24Masks 8 k * pair24_08_09Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 9 k * pair24_08_09Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_08_09_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {8, 9} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 8 k * x k) (∑ k, base24Frame 9 k * x k) := by
  have h := order24_integer_pair_lift 8 9 pair24_08_09Rows pair24_08_09Free
    pair24_08_09Left pair24_08_09Inverse 72 (1) (by norm_num) (by decide +kernel)
    pair24_08_09_certificate pair24_08_09_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
