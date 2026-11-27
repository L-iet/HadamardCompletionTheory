/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P01_12
@[expose] public section
namespace CompletionTheory

def pair24_02_03Rows : Fin 14 → Fin 16 := ![0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def pair24_02_03Free : Fin 10 → Fin 24 := ![13, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_02_03Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![16, -14, -6, 2, -6, -12, -6, 4, 16, 10, 16, 2, 2, 0;
     4, -2, -2, 6, -2, 0, -6, -4, 4, 2, 0, -2, -6, 8;
     4, -2, 2, -2, 2, 0, -6, -6, 4, 0, 2, 6, -8, 4;
     -5, 7, -1, -5, 5, 6, 6, 0, -8, -3, -1, -3, 4, -2;
     7, -5, -5, 3, 1, -6, -6, -4, 4, 5, 3, 1, 0, 2;
     16, -14, -6, 2, -6, -12, -6, -2, 16, 4, 10, 2, -4, 0;
     -8, 10, -2, -6, -2, 0, 6, 8, -8, 2, 0, -2, 6, -4;
     -2, 4, 4, 0, 4, 0, -6, -4, 4, -4, -6, 4, -6, 8;
     -5, 7, 3, -1, -3, 6, 6, 4, -8, 1, -5, -7, 8, -6;
     -8, 10, 6, 2, 6, 12, 6, -2, -8, -8, -14, 2, -4, 0;
     -5, 7, 7, 3, 1, 6, 6, -4, -8, -7, -9, 1, 0, 2;
     -2, 4, 0, -4, 0, 0, 6, 10, -8, -2, 4, -4, 8, -12;
     6, -6, 2, 2, 2, 0, 0, -4, 0, 2, -2, -2, -4, 4;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     6, -6, -2, -2, -2, 0, 0, 4, 0, -2, 2, 2, 4, -4;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def pair24_02_03Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![48, -72, -96, -48, -96, -24, -24, 0, -48, 0;
     0, -24, 0, 0, -48, 24, 24, -24, 0, -24;
     0, -48, 24, 0, -24, 24, 0, 0, -24, -24;
     -12, 36, 24, 36, 48, -12, -12, 0, 12, 24;
     12, -36, -24, -12, -48, 12, -12, -24, -12, 0;
     24, -72, -72, -48, -96, 0, -24, 0, -48, -24;
     24, 48, 0, 24, 48, -24, 0, 24, 24, 48;
     0, -24, 48, 0, 0, 48, 24, 0, 0, -24;
     -12, 60, 0, 12, 48, -36, 12, 0, 36, 24;
     -48, 48, 72, 24, 72, 24, 24, 0, 24, -24;
     -36, 36, 48, 12, 48, 12, 12, 0, 36, -24;
     0, 48, -24, 0, 48, -48, -24, 24, 0, 48;
     -24, -24, 0, 0, -24, 0, 0, -24, 0, -24;
     24, 0, 0, 0, 0, 0, 0, 0, 0, 0;
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
theorem pair24_02_03_certificate :
    pair24_02_03Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_02_03Rows id +
      pair24_02_03Inverse * integerInformationSelector pair24_02_03Free = (24 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_02_03_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_02_03Inverse.mulVec (fun t => if b t then 1 else -1) k = 24 ∨
      pair24_02_03Inverse.mulVec (fun t => if b t then 1 else -1) k = -24) →
    IntegerScaledHalfPattern 24 (1)
      (∑ k, encodedIntFrame base24Masks 2 k * pair24_02_03Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 3 k * pair24_02_03Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_02_03_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {2, 3} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 2 k * x k) (∑ k, base24Frame 3 k * x k) := by
  have h := order24_integer_pair_lift 2 3 pair24_02_03Rows pair24_02_03Free
    pair24_02_03Left pair24_02_03Inverse 24 (1) (by norm_num) (by decide +kernel)
    pair24_02_03_certificate pair24_02_03_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
