/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P04_14
@[expose] public section
namespace CompletionTheory

def pair24_05_08Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 6, 7, 9, 10, 11, 12, 13, 14, 15]
def pair24_05_08Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_05_08Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![3, 0, 7, 5, 2, 0, 1, 7, 3, 0, 1, 4, 4, -1;
     15, -12, 3, -3, -6, -12, 3, 15, -3, -6, 3, 0, 12, -9;
     -21, 24, 3, -3, 12, 6, 3, -12, -3, 3, -6, 0, -15, 9;
     -9, 12, -4, 1, -2, 12, 2, -16, 0, 6, 2, -7, -10, 13;
     3, 0, 4, -1, -4, 0, -2, 4, -6, 0, -2, 1, 10, -7;
     9, -6, 5, 1, -2, -6, -7, 2, 9, -3, 2, 2, -1, -5;
     -27, 30, -1, 7, 4, 12, 5, -13, -9, 6, -13, -4, -16, 19;
     -21, 24, 3, -3, 12, 6, 3, -3, -3, -6, -15, 0, -6, 9;
     9, -6, -4, 1, -2, -6, 2, 2, 0, 6, 2, -7, 8, -5;
     27, -24, -7, -5, -8, -6, -1, 8, 9, -3, 8, 8, 5, -11;
     33, -30, -6, -3, -6, -12, -6, 6, 6, -6, 12, 9, 12, -9;
     -3, 6, -3, 3, 0, 6, -3, 0, -3, 3, 6, -6, -3, -3;
     24, -24, -2, -4, -4, -6, -8, 4, 6, 6, 10, -2, 4, -4;
     -6, 6, 2, 4, 4, 6, 8, -4, -6, -6, -10, 2, -4, 4;
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

def pair24_05_08Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-24, -12, -24, -24, 24, 0, 12, 12, -12, 12;
     -72, 36, -72, -72, 0, -72, -36, 0, -36, 0;
     72, 0, 108, 72, 36, 72, 72, 36, 72, 0;
     60, -24, 60, 96, -24, 54, 24, -30, 30, 6;
     -24, 24, -24, -24, 24, -18, -24, -6, 6, 30;
     -12, -24, -48, -48, -24, 0, -12, 24, -24, -12;
     60, 12, 132, 132, 48, 108, 96, -12, 84, 24;
     36, 36, 108, 36, 72, 72, 72, 36, 72, 0;
     -12, 12, -48, -12, -24, -54, -12, -30, -6, 6;
     -48, -24, -84, -84, -60, -72, -84, -12, -96, -48;
     -72, -36, -108, -108, -72, -90, -108, -18, -90, -54;
     36, 0, 0, 36, 0, 0, 0, 0, 0, 36;
     -24, -48, -96, -60, -84, -72, -60, -24, -48, -24;
     -12, 12, 60, 24, 48, 36, 24, -12, 12, -12;
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
theorem pair24_05_08_certificate :
    pair24_05_08Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_05_08Rows id +
      pair24_05_08Inverse * integerInformationSelector pair24_05_08Free = (36 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_05_08_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_05_08Inverse.mulVec (fun t => if b t then 1 else -1) k = 36 ∨
      pair24_05_08Inverse.mulVec (fun t => if b t then 1 else -1) k = -36) →
    IntegerScaledHalfPattern 36 (1)
      (∑ k, encodedIntFrame base24Masks 5 k * pair24_05_08Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 8 k * pair24_05_08Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_05_08_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {5, 8} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 5 k * x k) (∑ k, base24Frame 8 k * x k) := by
  have h := order24_integer_pair_lift 5 8 pair24_05_08Rows pair24_05_08Free
    pair24_05_08Left pair24_05_08Inverse 36 (1) (by norm_num) (by decide +kernel)
    pair24_05_08_certificate pair24_05_08_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
