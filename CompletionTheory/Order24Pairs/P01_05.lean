/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P00_15
@[expose] public section
namespace CompletionTheory

def pair24_01_05Rows : Fin 14 → Fin 16 := ![0, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def pair24_01_05Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_01_05Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![3, 7, 5, 2, 0, 1, 0, 7, 3, 0, 1, 4, 4, -1;
     3, 5, -5, -2, -12, 5, 6, 17, -9, -6, -1, -4, 14, -11;
     3, -1, 1, 4, 6, -1, -12, -16, 9, 3, 2, 8, -19, 13;
     3, -6, 3, -6, 12, 0, -6, -18, 6, 6, 6, -3, -12, 15;
     3, 4, -1, -4, 0, -2, 0, 4, -6, 0, -2, 1, 10, -7;
     3, 6, 0, 0, -6, -6, 3, 3, 6, -3, 0, 0, 0, -6;
     3, -6, 12, -6, 12, 0, -15, -18, 6, 6, -3, 6, -21, 24;
     3, -1, 1, 4, 6, -1, -12, -7, 9, -6, -7, 8, -10, 13;
     3, -3, 0, 0, -6, 3, 3, 3, -3, 6, 0, -9, 9, -6;
     3, -3, -9, 0, -6, 3, 12, 12, -3, -3, 0, 0, 9, -15;
     3, -1, -8, 4, -12, -1, 15, 11, -9, -6, 2, -1, 17, -14;
     3, -4, 4, -2, 6, -4, -3, -1, 0, 3, 8, -4, -4, -2;
     0, 2, -8, 4, -6, -4, 12, 8, -6, 6, 2, -10, 8, -8;
     0, 1, 5, 2, 6, 7, -3, -5, -3, -6, -8, 4, -5, 5;
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

def pair24_01_05Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-24, -12, -24, -24, 24, 0, 12, 12, -12, 12;
     -48, 84, -48, -48, 48, -72, -12, 24, 12, 24;
     24, -96, 60, 24, -60, 72, 24, -12, -24, -48;
     36, -72, 36, 72, -72, 54, 0, -54, -18, -18;
     -24, 24, -24, -24, 24, -18, -24, -6, 6, 30;
     0, 0, -36, -36, 0, 0, 0, 36, 0, 0;
     0, -108, 72, 72, -72, 108, 36, -72, -36, -36;
     -12, -60, 60, -12, -24, 72, 24, -12, -24, -48;
     0, 36, -36, 0, 0, -54, 0, -18, 18, 18;
     0, 72, -36, -36, 36, -72, -36, 36, 0, 0;
     -12, 84, -48, -48, 48, -90, -48, 42, 30, 6;
     24, -24, -12, 24, -24, 0, -12, -12, -24, 24;
     24, 48, -48, -12, 12, -72, -12, 24, 48, 24;
     -24, -12, 48, 12, 24, 36, 12, -24, -12, -24;
     36, 0, 0, 0, 0, 0, 0, 0, 0, 0;
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
theorem pair24_01_05_certificate :
    pair24_01_05Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_01_05Rows id +
      pair24_01_05Inverse * integerInformationSelector pair24_01_05Free = (36 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_01_05_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_01_05Inverse.mulVec (fun t => if b t then 1 else -1) k = 36 ∨
      pair24_01_05Inverse.mulVec (fun t => if b t then 1 else -1) k = -36) →
    IntegerScaledHalfPattern 36 (1)
      (∑ k, encodedIntFrame base24Masks 1 k * pair24_01_05Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 5 k * pair24_01_05Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_01_05_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {1, 5} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 1 k * x k) (∑ k, base24Frame 5 k * x k) := by
  have h := order24_integer_pair_lift 1 5 pair24_01_05Rows pair24_01_05Free
    pair24_01_05Left pair24_01_05Inverse 36 (1) (by norm_num) (by decide +kernel)
    pair24_01_05_certificate pair24_01_05_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
