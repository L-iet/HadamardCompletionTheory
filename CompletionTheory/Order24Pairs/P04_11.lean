/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P04_07
@[expose] public section
namespace CompletionTheory

def pair24_04_11Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15]
def pair24_04_11Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_04_11Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![6, -4, 4, 4, 0, 0, 0, -2, 4, 4, 2, 4, 2, 0;
     -2, 4, 2, -2, 4, -4, 2, 0, 2, -2, -2, -4, 0, 2;
     10, -8, -1, 1, -2, 2, -1, -9, -7, 7, 4, 8, -9, 5;
     -10, 12, 0, -2, -4, 4, 4, 8, 0, -8, 0, -6, 4, -2;
     -6, 8, 4, -2, 0, 0, 0, 4, 4, -8, -4, -2, 8, -6;
     2, 0, 3, 1, 2, -2, -5, -1, -3, 7, 0, 0, -5, 1;
     -10, 12, 0, 4, -4, 4, 4, 2, 0, -8, -6, 0, -2, 4;
     10, -8, -4, 4, 4, 8, -4, -18, -16, 16, -2, 8, -18, 20;
     2, 0, 0, -2, -4, -8, 4, 8, 12, -8, 0, -6, 16, -14;
     2, 0, -3, -5, 2, -2, 1, 5, 3, 1, 0, 0, 1, -5;
     10, -8, -4, -2, 4, -4, -4, 0, -4, 4, 4, 2, 0, 2;
     -2, 4, -1, 1, -2, 2, -1, 3, 5, -5, 4, -4, 3, -7;
     8, -8, 2, -6, -4, -8, -2, 10, 14, -6, 4, -4, 14, -14;
     4, -4, -2, 6, 4, 8, 2, -10, -14, 6, -4, 4, -14, 14;
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

def pair24_04_11Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-24, -24, -24, -24, 0, 0, 0, 0, -24, 0;
     0, 24, 0, 0, 0, 0, 24, 0, 24, 0;
     -12, -72, 12, -12, -48, 24, -12, -12, -48, -36;
     24, 48, 24, 48, 48, -12, 0, 12, 36, 36;
     0, 48, 0, 0, 48, -12, 0, 12, 36, 36;
     12, -24, -12, -12, -24, 24, 12, 12, 0, -12;
     0, 24, 48, 48, 48, 24, 24, 0, 24, 24;
     0, -120, 48, 0, -96, 96, 24, -48, -48, -72;
     -24, 72, -48, -24, 48, -84, -24, 12, 12, 36;
     12, 24, -12, -12, 0, -24, -12, 12, 0, -12;
     0, -24, -24, -24, -48, -12, -24, -12, -12, -36;
     12, 24, -12, 12, 24, -24, -12, 12, 0, 36;
     -24, 48, -72, -48, 24, -96, -48, 24, 0, 24;
     0, -72, 48, 24, -48, 72, 24, -48, -24, -48;
     24, 0, 0, 0, 0, 0, 0, 0, 0, 0;
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
theorem pair24_04_11_certificate :
    pair24_04_11Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_04_11Rows id +
      pair24_04_11Inverse * integerInformationSelector pair24_04_11Free = (24 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_04_11_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_04_11Inverse.mulVec (fun t => if b t then 1 else -1) k = 24 ∨
      pair24_04_11Inverse.mulVec (fun t => if b t then 1 else -1) k = -24) →
    IntegerScaledHalfPattern 24 (1)
      (∑ k, encodedIntFrame base24Masks 4 k * pair24_04_11Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 11 k * pair24_04_11Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_04_11_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {4, 11} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 4 k * x k) (∑ k, base24Frame 11 k * x k) := by
  have h := order24_integer_pair_lift 4 11 pair24_04_11Rows pair24_04_11Free
    pair24_04_11Left pair24_04_11Inverse 24 (1) (by norm_num) (by decide +kernel)
    pair24_04_11_certificate pair24_04_11_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
