/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P02_06
@[expose] public section
namespace CompletionTheory

def pair24_02_10Rows : Fin 14 → Fin 16 := ![0, 1, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15]
def pair24_02_10Free : Fin 10 → Fin 24 := ![11, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_02_10Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![8, -2, 8, -2, -2, 6, -4, -2, 8, 2, 12, -2, 2, -8;
     3, 0, 0, -2, 4, -2, 0, -3, 1, 1, 2, -4, -2, 2;
     3, 0, 0, 2, -4, 2, 0, -3, -1, -1, 4, 4, -4, -2;
     -2, 2, -2, -2, -2, 2, 4, 2, -6, 0, -2, 0, 0, 6;
     5, -2, 2, -4, 2, 4, -4, -5, -3, 3, 2, 0, 0, 0;
     10, -4, 4, -4, -4, 0, -8, 2, 10, -2, 12, -4, 4, -16;
     -8, 8, 4, 0, 0, 4, 4, -4, -10, 2, -10, 4, -10, 16;
     -3, 6, 0, 4, -2, 4, 0, -3, 1, -5, -4, 2, -2, 2;
     -2, 2, -2, 2, 2, -6, 4, 2, -2, 4, -6, -4, 4, 2;
     -2, 2, -8, 2, 2, -6, 4, 8, 4, -2, -6, 2, 4, -4;
     0, 0, -6, 4, 4, -8, 0, 6, -2, -2, -4, 2, 4, 2;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     8, -8, -4, 0, 0, -4, -4, 4, 4, 4, 4, -4, 4, -4;
     -2, 2, 4, 2, 2, 6, 4, -4, -8, -2, -6, 2, -8, 8;
     6, -6, 0, -2, -2, -2, 0, 0, 4, -2, 2, 2, 4, -4;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def pair24_02_10Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-48, -24, -48, 0, 0, -24, -24, 0, -48, 48;
     -12, 0, -12, 0, -24, 0, 12, -12, 0, 0;
     -12, -24, 12, 0, 0, 0, -12, 12, -24, 0;
     24, 0, 24, 24, 0, 12, 0, -12, 12, -12;
     -12, -24, -12, 0, -24, 12, -12, -24, -12, 12;
     -48, 0, -72, -24, 0, -48, -48, 24, -48, 48;
     24, -24, 72, 48, 0, 72, 48, -24, 24, -24;
     -12, 0, 36, 0, 24, 24, 12, 12, 0, 0;
     24, 24, 0, 0, 0, -12, 24, -12, 36, -12;
     24, 48, 0, -24, 24, -24, 0, 24, 24, -24;
     24, 24, 0, -24, 0, -12, 0, 12, 36, -36;
     24, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, -48, -24, -24, -48, -24, 0, 0, 0;
     0, -24, 48, 24, 0, 48, 24, -24, 0, -24;
     0, 0, -24, -24, 0, -24, -24, 0, -24, 0;
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
theorem pair24_02_10_certificate :
    pair24_02_10Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_02_10Rows id +
      pair24_02_10Inverse * integerInformationSelector pair24_02_10Free = (24 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_02_10_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_02_10Inverse.mulVec (fun t => if b t then 1 else -1) k = 24 ∨
      pair24_02_10Inverse.mulVec (fun t => if b t then 1 else -1) k = -24) →
    IntegerScaledHalfPattern 24 (1)
      (∑ k, encodedIntFrame base24Masks 2 k * pair24_02_10Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 10 k * pair24_02_10Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_02_10_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {2, 10} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 2 k * x k) (∑ k, base24Frame 10 k * x k) := by
  have h := order24_integer_pair_lift 2 10 pair24_02_10Rows pair24_02_10Free
    pair24_02_10Left pair24_02_10Inverse 24 (1) (by norm_num) (by decide +kernel)
    pair24_02_10_certificate pair24_02_10_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
