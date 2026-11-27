/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P05_07
@[expose] public section
namespace CompletionTheory

def pair24_05_11Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 12, 13, 14, 15]
def pair24_05_11Free : Fin 10 → Fin 24 := ![13, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_05_11Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![-6, 8, 6, 2, 4, 0, 2, 4, 6, -2, -2, 0, 4, -2;
     -6, 8, 4, -8, 0, -12, 0, 10, 16, -8, 2, -8, 14, -12;
     6, -4, -1, 3, 2, 6, 1, -11, -13, 7, 0, 8, -15, 11;
     6, -4, -4, 6, -4, 12, 4, -8, -16, 4, 0, 2, -12, 14;
     -6, 8, 4, -2, 0, 0, 0, 4, 4, -8, -4, -2, 8, -6;
     6, -4, 3, -1, -2, -6, -7, 1, 3, 7, 4, 0, 1, -5;
     -6, 8, -2, 10, 0, 12, 6, -8, -14, -2, -10, 4, -16, 18;
     6, -4, -2, -2, 0, 0, -6, -8, -2, 10, 2, 4, -4, 6;
     -6, 8, 0, 2, 4, 0, 8, 4, 0, -8, -8, -6, 4, -2;
     6, -4, -3, -7, -2, -6, -1, 7, 9, 1, 4, 0, 7, -11;
     6, -4, -2, -8, 0, -12, -6, 10, 10, -2, 8, -2, 14, -12;
     6, -4, -3, 5, -2, 6, -1, -5, -3, 1, 4, 0, -5, 1;
     0, 0, 2, -2, 4, 0, 2, 6, 2, -6, -4, -4, 2, -2;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     12, -12, -2, 2, -4, 0, -2, -6, -2, 6, 4, 4, -2, 2;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def pair24_05_11Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![0, 24, 0, 0, 48, 0, 24, 24, 24, 24;
     24, 96, -48, -24, 48, -72, 0, 48, 48, 48;
     -12, -84, 48, 12, -48, 60, 12, -24, -36, -48;
     -24, -72, 48, 48, -48, 60, 0, -60, -36, -36;
     0, 48, 0, 0, 48, -12, 0, 12, 36, 36;
     12, -12, -48, -36, -24, -12, -12, 24, -12, 0;
     -24, -48, 96, 72, 0, 96, 48, -48, 0, -24;
     24, -48, 0, -24, -48, 24, 0, 0, -24, -24;
     -24, 48, 24, 24, 48, -12, 24, -12, 36, 12;
     12, 36, -48, -36, 0, -60, -36, 24, -12, 0;
     24, 48, -72, -48, 0, -84, -48, 36, 12, 12;
     -12, -36, 0, 12, -24, 12, -12, -24, -36, 0;
     -24, 24, 0, 0, 24, -24, 0, 0, 24, 0;
     24, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, -48, -24, -24, -48, 0, -24, -24, -48, -24;
     0, 24, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 24, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 24, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 24, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 24, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 24, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 24, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 24, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 24]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_05_11_certificate :
    pair24_05_11Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_05_11Rows id +
      pair24_05_11Inverse * integerInformationSelector pair24_05_11Free = (24 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_05_11_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_05_11Inverse.mulVec (fun t => if b t then 1 else -1) k = 24 ∨
      pair24_05_11Inverse.mulVec (fun t => if b t then 1 else -1) k = -24) →
    IntegerScaledHalfPattern 24 (1)
      (∑ k, encodedIntFrame base24Masks 5 k * pair24_05_11Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 11 k * pair24_05_11Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_05_11_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {5, 11} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 5 k * x k) (∑ k, base24Frame 11 k * x k) := by
  have h := order24_integer_pair_lift 5 11 pair24_05_11Rows pair24_05_11Free
    pair24_05_11Left pair24_05_11Inverse 24 (1) (by norm_num) (by decide +kernel)
    pair24_05_11_certificate pair24_05_11_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
