/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P09_12
@[expose] public section
namespace CompletionTheory

def pair24_10_11Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15]
def pair24_10_11Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_10_11Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![-3, 6, 8, 4, 4, 0, 0, 2, 3, 8, -1, 2, 5, -2;
     3, 0, 2, -2, -2, 6, -6, 2, -3, 2, -1, -4, -1, 4;
     -6, 9, 2, -2, 7, -3, 3, 2, -3, -7, -1, 5, -10, 4;
     9, -6, -4, 1, -8, -6, 6, 2, 0, -4, 8, -1, 2, 1;
     15, -12, 2, 1, -8, 0, 0, -4, -6, 2, 2, 5, 8, -5;
     -18, 21, 8, -2, 7, 3, -3, -4, 9, -1, -7, -7, -4, -2;
     9, -6, -4, 10, -8, -6, 6, 2, -9, -4, -1, 8, -7, 10;
     -33, 36, 2, -2, 16, 6, 12, 2, -3, -16, -19, -4, -19, 22;
     27, -24, -4, 1, -8, -6, -12, 2, 0, 14, 8, -1, 20, -17;
     0, 3, -4, -8, 1, 3, -3, 2, 9, 5, -1, -1, 2, -8;
     3, 0, -4, -5, 4, 6, -6, -4, 6, -4, 2, -1, 2, 1;
     12, -9, -4, 4, -5, -3, 3, -4, -3, 5, 11, -1, 2, -8;
     30, -30, 0, -6, -6, -6, -12, -6, 6, 18, 12, 0, 18, -18;
     -12, 12, 0, 6, 6, 6, 12, 6, -6, -18, -12, 0, -18, 18;
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

def pair24_10_11Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-12, 12, -12, -12, 48, 0, 24, 24, 12, 24;
     -12, 12, -12, -12, -24, 0, 24, -12, 12, -12;
     24, -24, 60, 24, 12, 36, 24, 24, 12, -12;
     -12, -24, -12, 24, -24, -18, -48, -30, -42, 6;
     -48, -24, -48, -48, -24, -18, -48, -30, -42, 6;
     60, 48, 24, 24, 48, 36, 60, 60, 84, 24;
     -48, -60, 24, 24, -24, 36, -12, -48, -60, -12;
     96, 12, 168, 96, 48, 144, 132, 24, 120, -12;
     -84, 12, -120, -84, -24, -126, -84, -30, -78, 6;
     24, 48, -12, -12, 12, -36, -12, 24, 12, -12;
     24, 12, -12, -12, -24, -18, -12, 6, 30, -30;
     -12, -24, -48, -12, -24, -36, -48, -12, -60, 24;
     -72, 0, -144, -108, -36, -144, -108, 0, -72, 0;
     36, -36, 108, 72, 0, 108, 72, -36, 36, -36;
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
theorem pair24_10_11_certificate :
    pair24_10_11Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_10_11Rows id +
      pair24_10_11Inverse * integerInformationSelector pair24_10_11Free = (36 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_10_11_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_10_11Inverse.mulVec (fun t => if b t then 1 else -1) k = 36 ∨
      pair24_10_11Inverse.mulVec (fun t => if b t then 1 else -1) k = -36) →
    IntegerScaledHalfPattern 36 (1)
      (∑ k, encodedIntFrame base24Masks 10 k * pair24_10_11Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 11 k * pair24_10_11Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_10_11_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {10, 11} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 10 k * x k) (∑ k, base24Frame 11 k * x k) := by
  have h := order24_integer_pair_lift 10 11 pair24_10_11Rows pair24_10_11Free
    pair24_10_11Left pair24_10_11Inverse 36 (1) (by norm_num) (by decide +kernel)
    pair24_10_11_certificate pair24_10_11_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
