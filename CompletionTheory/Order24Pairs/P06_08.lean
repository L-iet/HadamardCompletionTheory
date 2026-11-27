/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P05_13
@[expose] public section
namespace CompletionTheory

def pair24_06_08Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 7, 9, 10, 11, 12, 13, 14, 15]
def pair24_06_08Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_06_08Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![3, 0, 7, 5, 2, 0, 1, 7, 3, 0, 1, 4, 4, -1;
     -21, 24, 3, -3, 6, 12, 3, -9, -3, 6, -9, -12, -12, 15;
     -3, 6, 3, -3, 6, -6, 3, 0, -3, -3, 0, 6, -3, -3;
     27, -24, -4, 1, -14, -12, 2, 8, 0, -6, 14, 5, 14, -11;
     3, 0, 4, -1, -4, 0, -2, 4, -6, 0, -2, 1, 10, -7;
     -9, 12, 5, 1, 4, 6, -7, -10, 9, 3, -4, -4, -13, 7;
     9, -6, -1, 7, -8, -12, 5, 11, -9, -6, -1, 8, 8, -5;
     -3, 6, 3, -3, 6, -6, 3, 9, -3, -12, -9, 6, 6, -3;
     -9, 12, -4, 1, 4, 6, 2, -10, 0, 12, -4, -13, -4, 7;
     9, -6, -7, -5, -2, 6, -1, -4, 9, 3, 2, 2, -7, 1;
     -3, 6, -6, -3, 6, 12, -6, -18, 6, 6, 0, -3, -12, 15;
     15, -12, -3, 3, -6, -6, -3, 12, -3, -3, 12, 0, 9, -15;
     6, -6, -2, -4, 2, 6, -8, -8, 6, 12, 4, -8, -8, 8;
     12, -12, 2, 4, -2, -6, 8, 8, -6, -12, -4, 8, 8, -8;
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

def pair24_06_08Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-24, -12, -24, -24, 24, 0, 12, 12, -12, 12;
     72, 36, 72, 72, 0, 72, 108, 0, 108, 0;
     0, 0, 36, 0, 36, 0, 0, 36, 0, 0;
     -84, -24, -84, -48, -24, -90, -120, -30, -114, 6;
     -24, 24, -24, -24, 24, -18, -24, -6, 6, 30;
     60, -24, 24, 24, -24, 72, 60, 24, 48, -12;
     -84, 12, -12, -12, 48, -36, -48, -12, -60, 24;
     -36, 36, 36, -36, 72, 0, 0, 36, 0, 0;
     60, 12, 24, 60, -24, 18, 60, -30, 66, 6;
     24, -24, -12, -12, -60, 0, -12, -12, -24, -48;
     72, -36, 36, 36, -72, 54, 36, -18, 54, -54;
     -36, 0, -72, -36, 0, -72, -72, 0, -72, 36;
     48, -48, -24, 12, -84, 0, 12, -24, 24, -24;
     -84, 12, -12, -48, 48, -36, -48, -12, -60, -12;
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
theorem pair24_06_08_certificate :
    pair24_06_08Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_06_08Rows id +
      pair24_06_08Inverse * integerInformationSelector pair24_06_08Free = (36 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_06_08_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_06_08Inverse.mulVec (fun t => if b t then 1 else -1) k = 36 ∨
      pair24_06_08Inverse.mulVec (fun t => if b t then 1 else -1) k = -36) →
    IntegerScaledHalfPattern 36 (1)
      (∑ k, encodedIntFrame base24Masks 6 k * pair24_06_08Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 8 k * pair24_06_08Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_06_08_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {6, 8} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 6 k * x k) (∑ k, base24Frame 8 k * x k) := by
  have h := order24_integer_pair_lift 6 8 pair24_06_08Rows pair24_06_08Free
    pair24_06_08Left pair24_06_08Inverse 36 (1) (by norm_num) (by decide +kernel)
    pair24_06_08_certificate pair24_06_08_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
