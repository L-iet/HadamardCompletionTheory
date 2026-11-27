/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P01_04
@[expose] public section
namespace CompletionTheory

def pair24_01_08Rows : Fin 14 → Fin 16 := ![0, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15]
def pair24_01_08Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_01_08Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![3, 7, 5, 2, 0, 0, 1, 7, 3, 0, 1, 4, 4, -1;
     3, 3, -3, -2, 4, -8, 3, 7, -3, -2, -1, -4, 4, -1;
     3, 3, -3, 4, -8, -2, 3, 4, -3, -5, 2, 8, 1, -7;
     3, -4, 1, -6, -4, 8, 2, -8, 0, 2, 6, -3, -2, 5;
     3, 4, -1, -4, 0, 0, -2, 4, -6, 0, -2, 1, 10, -7;
     3, 5, 1, 0, 2, -4, -7, -2, 9, -1, 0, 0, -5, -1;
     3, -1, 7, -6, -10, 2, 5, 7, -9, -4, -3, 6, 4, -1;
     3, 3, -3, 4, -8, -2, 3, 13, -3, -14, -7, 8, 10, -7;
     3, -4, 1, 0, 2, -4, 2, -2, 0, 8, 0, -9, 4, -1;
     3, -7, -5, 0, 8, 2, -1, -8, 9, 5, 0, 0, -11, 5;
     3, -6, -3, 4, 10, -2, -6, -14, 6, 4, 2, -1, -8, 11;
     3, -3, 3, -2, -2, 4, -3, 4, -3, 1, 8, -4, 1, -7;
     0, -2, -4, 4, 8, 2, -8, -12, 6, 14, 2, -10, -12, 12;
     0, 2, 4, 2, -2, 4, 8, 0, -6, -8, -8, 4, 0, 0;
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

def pair24_01_08Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-24, -12, -24, -24, 24, 0, 12, 12, -12, 12;
     -24, 36, -24, -24, 0, -24, 12, 0, 12, 0;
     -24, 0, 12, -24, 36, -24, -24, 36, -24, 0;
     12, -24, 12, 48, -24, 6, -24, -30, -18, 6;
     -24, 24, -24, -24, 24, -18, -24, -6, 6, 30;
     12, -24, -24, -24, -24, 24, 12, 24, 0, -12;
     -60, 12, 12, 12, 48, -12, -24, -12, -36, 24;
     -60, 36, 12, -60, 72, -24, -24, 36, -24, 0;
     12, 12, -24, 12, -24, -30, 12, -30, 18, 6;
     48, -24, 12, 12, -60, 24, 12, -12, 0, -48;
     48, -36, 12, 12, -72, 30, 12, -18, 30, -54;
     12, 0, -24, 12, 0, -24, -24, 0, -24, 36;
     72, -48, 0, 36, -84, 24, 36, -24, 48, -24;
     -36, 12, 36, 0, 48, 12, 0, -12, -12, -12;
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
theorem pair24_01_08_certificate :
    pair24_01_08Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_01_08Rows id +
      pair24_01_08Inverse * integerInformationSelector pair24_01_08Free = (36 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_01_08_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_01_08Inverse.mulVec (fun t => if b t then 1 else -1) k = 36 ∨
      pair24_01_08Inverse.mulVec (fun t => if b t then 1 else -1) k = -36) →
    IntegerScaledHalfPattern 36 (1)
      (∑ k, encodedIntFrame base24Masks 1 k * pair24_01_08Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 8 k * pair24_01_08Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_01_08_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {1, 8} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 1 k * x k) (∑ k, base24Frame 8 k * x k) := by
  have h := order24_integer_pair_lift 1 8 pair24_01_08Rows pair24_01_08Free
    pair24_01_08Left pair24_01_08Inverse 36 (1) (by norm_num) (by decide +kernel)
    pair24_01_08_certificate pair24_01_08_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
