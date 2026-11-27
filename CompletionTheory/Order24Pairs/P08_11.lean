/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P07_14
@[expose] public section
namespace CompletionTheory

def pair24_08_11Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 12, 13, 14, 15]
def pair24_08_11Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_08_11Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![3, 0, 7, 5, 2, 0, 0, 1, 7, 3, 1, 4, 4, -1;
     -3, 6, 3, -3, 0, 6, -6, 3, 3, -3, -3, -6, 0, 3;
     -12, 15, 3, -3, 9, -3, 3, 3, -6, -3, -3, 3, -9, 3;
     9, -6, -4, 1, -8, -6, 6, 2, -4, 0, 8, -1, 2, 1;
     3, 0, 4, -1, -4, 0, 0, -2, 4, -6, -2, 1, 10, -7;
     0, 3, 5, 1, 1, 3, -3, -7, -4, 9, -1, -1, -7, 1;
     -9, 12, -1, 7, -2, -6, 6, 5, -1, -9, -7, 2, -4, 7;
     -39, 42, 3, -3, 18, 6, 12, 3, -15, -3, -21, -6, -18, 21;
     27, -24, -4, 1, -8, -6, -12, 2, 14, 0, 8, -1, 20, -17;
     18, -15, -7, -5, -5, 3, -3, -1, 2, 9, 5, 5, -1, -5;
     15, -12, -6, -3, 0, 6, -6, -6, -6, 6, 6, 3, 0, 3;
     6, -3, -3, 3, -3, -3, 3, -3, 6, -3, 9, -3, 3, -9;
     42, -42, -2, -4, -10, -6, -12, -8, 16, 6, 16, 4, 16, -16;
     -24, 24, 2, 4, 10, 6, 12, 8, -16, -6, -16, -4, -16, 16;
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

def pair24_08_11Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-24, -12, -24, -24, 24, 0, 12, 12, -12, 12;
     0, 36, 0, 0, 0, 0, 36, 0, 36, 0;
     36, 0, 72, 36, 36, 36, 36, 36, 36, 0;
     -12, -24, -12, 24, -24, -18, -48, -30, -42, 6;
     -24, 24, -24, -24, 24, -18, -24, -6, 6, 30;
     24, -24, -12, -12, -24, 36, 24, 24, 12, -12;
     -12, 12, 60, 60, 48, 36, 24, -12, 12, 24;
     108, 36, 180, 108, 72, 144, 144, 36, 144, 0;
     -84, 12, -120, -84, -24, -126, -84, -30, -78, 6;
     -12, -24, -48, -48, -60, -36, -48, -12, -60, -48;
     0, -36, -36, -36, -72, -18, -36, -18, -18, -54;
     0, 0, -36, 0, 0, -36, -36, 0, -36, 36;
     -96, -48, -168, -132, -84, -144, -132, -24, -120, -24;
     60, 12, 132, 96, 48, 108, 96, -12, 84, -12;
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
theorem pair24_08_11_certificate :
    pair24_08_11Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_08_11Rows id +
      pair24_08_11Inverse * integerInformationSelector pair24_08_11Free = (36 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_08_11_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_08_11Inverse.mulVec (fun t => if b t then 1 else -1) k = 36 ∨
      pair24_08_11Inverse.mulVec (fun t => if b t then 1 else -1) k = -36) →
    IntegerScaledHalfPattern 36 (1)
      (∑ k, encodedIntFrame base24Masks 8 k * pair24_08_11Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 11 k * pair24_08_11Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_08_11_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {8, 11} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 8 k * x k) (∑ k, base24Frame 11 k * x k) := by
  have h := order24_integer_pair_lift 8 11 pair24_08_11Rows pair24_08_11Free
    pair24_08_11Left pair24_08_11Inverse 36 (1) (by norm_num) (by decide +kernel)
    pair24_08_11_certificate pair24_08_11_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
