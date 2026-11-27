/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P01_14
@[expose] public section
namespace CompletionTheory

def pair24_02_05Rows : Fin 14 → Fin 16 := ![0, 1, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def pair24_02_05Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_02_05Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![15, -14, 4, -4, 0, -2, -7, 0, 8, 0, 5, 6, -1, 2;
     11, -10, 0, -4, -4, 0, -3, 4, 2, -2, 3, 2, 3, -2;
     -1, 2, 0, 2, 2, 0, -3, -5, 2, 1, 0, 2, -6, 4;
     -11, 12, -1, 2, 4, 2, 4, -4, -4, 2, -2, -5, -2, 3;
     9, -8, 1, -4, 0, -2, -4, 0, 2, 0, 2, 3, 2, -1;
     13, -12, 2, -4, -2, -4, -5, -1, 8, -1, 4, 4, -2, 0;
     -11, 12, 2, 2, 4, 2, 1, -4, -4, 2, -5, -2, -5, 6;
     -1, 2, 0, 2, 2, 0, -3, -2, 2, -2, -3, 2, -3, 4;
     -5, 6, -1, 2, -2, 2, 4, 2, -4, 2, -2, -5, 4, -3;
     -5, 6, -4, 2, -2, 2, 7, 5, -4, -1, -2, -2, 4, -6;
     -1, 2, -3, 2, -4, 0, 6, 4, -4, -2, 0, -1, 6, -5;
     -7, 8, 0, 2, 2, 0, 3, 1, -4, 1, 0, -4, 0, -2;
     4, -4, -2, 0, -2, -2, 2, 2, 0, 2, 2, -2, 2, -2;
     2, -2, 2, 0, 2, 2, -2, -2, 0, -2, -2, 2, -2, 2;
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

def pair24_02_05Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-36, -60, -36, -36, -48, 0, -24, -24, -60, -24;
     -36, -12, -36, -36, -24, -24, -24, -12, -36, -12;
     12, -24, 24, 12, -12, 24, 12, 0, 0, -12;
     36, 24, 36, 48, 24, 18, 24, 6, 42, 18;
     -24, -24, -24, -24, -24, -6, -24, -18, -30, -6;
     -24, -48, -36, -36, -48, 0, -24, -12, -48, -24;
     24, 12, 48, 48, 24, 36, 36, 0, 36, 12;
     0, -12, 24, 0, 0, 24, 12, 0, 0, -12;
     12, 36, 0, 12, 24, -18, 12, 6, 30, 18;
     12, 48, 0, 0, 36, -24, 0, 24, 24, 12;
     0, 36, -12, -12, 24, -30, -12, 18, 18, 6;
     24, 24, 12, 24, 24, 0, 12, 12, 24, 24;
     0, 0, -24, -12, -12, -24, -12, 0, 0, 0;
     -12, -12, 12, 0, 0, 12, 0, -12, -12, -12;
     12, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 12, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 12, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 12, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 12, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 12, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 12, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 12, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 12, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 12]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_02_05_certificate :
    pair24_02_05Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_02_05Rows id +
      pair24_02_05Inverse * integerInformationSelector pair24_02_05Free = (12 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_02_05_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_02_05Inverse.mulVec (fun t => if b t then 1 else -1) k = 12 ∨
      pair24_02_05Inverse.mulVec (fun t => if b t then 1 else -1) k = -12) →
    IntegerScaledHalfPattern 12 (1)
      (∑ k, encodedIntFrame base24Masks 2 k * pair24_02_05Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 5 k * pair24_02_05Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_02_05_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {2, 5} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 2 k * x k) (∑ k, base24Frame 5 k * x k) := by
  have h := order24_integer_pair_lift 2 5 pair24_02_05Rows pair24_02_05Free
    pair24_02_05Left pair24_02_05Inverse 12 (1) (by norm_num) (by decide +kernel)
    pair24_02_05_certificate pair24_02_05_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
