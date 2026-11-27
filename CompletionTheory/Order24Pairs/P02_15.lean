/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P02_11
@[expose] public section
namespace CompletionTheory

def pair24_02_15Rows : Fin 14 → Fin 16 := ![0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
def pair24_02_15Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_02_15Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![36, -34, 8, -10, -2, -2, -4, -14, 4, 16, -2, 12, 14, 2;
     16, -14, 0, -6, 2, -6, 0, -6, 4, 4, -2, 4, 2, 2;
     10, -8, 0, 0, -4, 0, 0, -6, -2, 4, -2, 4, 8, -4;
     -13, 15, -2, 1, -3, 5, 4, 8, -2, -8, 1, -1, -7, 2;
     15, -13, 2, -7, 1, 1, -4, -8, -2, 4, 1, 3, 5, 2;
     26, -24, 4, -8, 0, -4, -8, -10, -2, 16, -2, 8, 8, -4;
     -4, 6, 4, -2, -6, 2, 4, 2, 4, -8, -2, -4, 2, 2;
     10, -8, 0, 0, -4, 0, 0, -6, 4, 4, -8, -2, 8, 2;
     -19, 21, -2, 7, 3, -1, 4, 8, -2, -8, 7, -7, -13, 2;
     -28, 30, -8, 10, 6, 2, 4, 14, -2, -8, 4, -10, -10, -4;
     -17, 19, -6, 9, 5, -3, 0, 12, -2, -8, 1, -5, -7, 2;
     -20, 22, 0, 6, 2, 6, 0, 6, -2, -8, 4, -2, -10, -4;
     2, -2, -4, 2, 2, -2, -4, 4, 0, 0, 6, 2, -6, 0;
     10, -10, 4, -2, -2, 2, 4, -4, 0, 0, -6, -2, 6, 0;
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

def pair24_02_15Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-96, -120, -96, -96, -96, -24, -72, -48, -144, -48;
     -48, -24, -48, -48, -48, -24, -24, -24, -48, -24;
     -24, -48, 0, -24, -24, 0, -24, 0, -48, -24;
     36, 48, 36, 60, 48, 0, 12, 12, 48, 36;
     -36, -48, -36, -36, -48, 0, -36, -36, -48, -12;
     -48, -96, -72, -72, -96, 0, -48, -24, -96, -48;
     -24, 24, 24, 24, 48, 0, 0, 0, 0, 24;
     -48, -24, 0, -48, 0, 0, -24, 0, -48, -24;
     60, 72, 36, 60, 48, 0, 60, 12, 96, 36;
     96, 96, 72, 72, 72, 24, 72, 48, 120, 24;
     60, 72, 36, 36, 48, 0, 36, 36, 96, 12;
     72, 48, 48, 72, 48, 24, 48, 24, 72, 48;
     24, 0, -24, 0, -24, -24, 0, 0, 24, 0;
     -48, -24, 0, -24, 0, 0, -24, -24, -48, -24;
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
theorem pair24_02_15_certificate :
    pair24_02_15Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_02_15Rows id +
      pair24_02_15Inverse * integerInformationSelector pair24_02_15Free = (24 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_02_15_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_02_15Inverse.mulVec (fun t => if b t then 1 else -1) k = 24 ∨
      pair24_02_15Inverse.mulVec (fun t => if b t then 1 else -1) k = -24) →
    IntegerScaledHalfPattern 24 (-1)
      (∑ k, encodedIntFrame base24Masks 2 k * pair24_02_15Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 15 k * pair24_02_15Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_02_15_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {2, 15} x →
    HalfCorrelationPattern 24 (rationalRealCast (-1))
      (∑ k, base24Frame 2 k * x k) (∑ k, base24Frame 15 k * x k) := by
  have h := order24_integer_pair_lift 2 15 pair24_02_15Rows pair24_02_15Free
    pair24_02_15Left pair24_02_15Inverse 24 (-1) (by norm_num) (by decide +kernel)
    pair24_02_15_certificate pair24_02_15_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
