/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P05_06
@[expose] public section
namespace CompletionTheory

def pair24_05_10Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 6, 7, 8, 9, 11, 12, 13, 14, 15]
def pair24_05_10Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_05_10Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![-3, 6, 8, 4, 4, 0, 2, 3, 8, 0, -1, 2, 5, -2;
     21, -18, 2, -2, -8, -12, 2, -3, 14, -6, 5, 2, 11, -8;
     -15, 18, 2, -2, 10, 6, 2, -3, -13, 3, -4, 2, -16, 10;
     -9, 12, -4, 1, -2, 12, 2, 0, -16, 6, 2, -7, -10, 13;
     15, -12, 2, 1, -8, 0, -4, -6, 2, 0, 2, 5, 8, -5;
     -9, 12, 8, -2, 4, -6, -4, 9, 5, -3, -4, -4, 2, -8;
     -9, 12, -4, 10, -2, 12, 2, -9, -16, 6, -7, 2, -19, 22;
     -15, 18, 2, -2, 10, 6, 2, -3, -4, -6, -13, 2, -7, 10;
     9, -6, -4, 1, -2, -6, 2, 0, 2, 6, 2, -7, 8, -5;
     9, -6, -4, -8, -2, -6, 2, 9, 11, -3, 2, 2, 8, -14;
     21, -18, -4, -5, -2, -12, -4, 6, 8, -6, 8, 5, 14, -11;
     3, 0, -4, 4, -2, 6, -4, -3, -1, 3, 8, -4, -4, -2;
     12, -12, 0, -6, 0, -6, -6, 6, 6, 6, 6, -6, 6, -6;
     6, -6, 0, 6, 0, 6, 6, -6, -6, -6, -6, 6, -6, 6;
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

def pair24_05_10Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-12, 12, -12, -12, 48, 0, 24, 24, 12, 24;
     -84, 12, -84, -84, -24, -72, -48, -12, -60, -12;
     60, -24, 96, 60, 12, 72, 60, 24, 48, -12;
     60, -24, 60, 96, -24, 54, 24, -30, 30, 6;
     -48, -24, -48, -48, -24, -18, -48, -30, -42, 6;
     24, 48, -12, -12, 48, 0, 24, 60, 48, 24;
     24, -60, 96, 96, -24, 108, 60, -48, 12, -12;
     24, 12, 96, 24, 48, 72, 60, 24, 48, -12;
     -12, 12, -48, -12, -24, -54, -12, -30, -6, 6;
     -12, 48, -48, -48, 12, -72, -48, 24, -24, -12;
     -48, 12, -84, -84, -24, -90, -84, 6, -42, -30;
     24, -24, -12, 24, -24, 0, -12, -12, -24, 24;
     0, 0, -72, -36, -36, -72, -36, 0, 0, 0;
     -36, -36, 36, 0, 0, 36, 0, -36, -36, -36;
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
theorem pair24_05_10_certificate :
    pair24_05_10Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_05_10Rows id +
      pair24_05_10Inverse * integerInformationSelector pair24_05_10Free = (36 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_05_10_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_05_10Inverse.mulVec (fun t => if b t then 1 else -1) k = 36 ∨
      pair24_05_10Inverse.mulVec (fun t => if b t then 1 else -1) k = -36) →
    IntegerScaledHalfPattern 36 (1)
      (∑ k, encodedIntFrame base24Masks 5 k * pair24_05_10Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 10 k * pair24_05_10Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_05_10_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {5, 10} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 5 k * x k) (∑ k, base24Frame 10 k * x k) := by
  have h := order24_integer_pair_lift 5 10 pair24_05_10Rows pair24_05_10Free
    pair24_05_10Left pair24_05_10Inverse 36 (1) (by norm_num) (by decide +kernel)
    pair24_05_10_certificate pair24_05_10_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
