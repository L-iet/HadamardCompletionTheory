/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P01_02
@[expose] public section
namespace CompletionTheory

def pair24_01_06Rows : Fin 14 → Fin 16 := ![0, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def pair24_01_06Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_01_06Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![3, 7, 5, 2, 0, 1, 0, 7, 3, 0, 1, 4, 4, -1;
     3, -1, 1, -2, 12, -1, -12, -13, 9, 6, -1, -4, -16, 19;
     3, 2, -2, 4, -6, 2, -3, -1, 0, -3, 2, 8, -4, -2;
     3, 0, -3, -6, -12, 6, 12, 12, -12, -6, 6, -3, 18, -15;
     3, 4, -1, -4, 0, -2, 0, 4, -6, 0, -2, 1, 10, -7;
     3, 3, 3, 0, 6, -9, -6, -12, 15, 3, 0, 0, -15, 9;
     3, 0, 6, -6, -12, 6, 3, 12, -12, -6, -3, 6, 9, -6;
     3, 2, -2, 4, -6, 2, -3, 8, 0, -12, -7, 8, 5, -2;
     3, -6, 3, 0, 6, 0, -6, -12, 6, 12, 0, -9, -6, 9;
     3, -6, -6, 0, 6, 0, 3, -3, 6, 3, 0, 0, -6, 0;
     3, -7, -2, 4, 12, -7, -3, -19, 9, 6, 2, -1, -13, 16;
     3, -1, 1, -2, -6, -1, 6, 14, -9, -3, 8, -4, 11, -17;
     0, -1, -5, 4, 6, -7, 3, -7, 3, 12, 2, -10, -7, 7;
     0, 4, 2, 2, -6, 10, 6, 10, -12, -12, -8, 4, 10, -10;
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

def pair24_01_06Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-24, -12, -24, -24, 24, 0, 12, 12, -12, 12;
     24, -60, 24, 24, -96, 72, 60, -48, 12, -48;
     -12, -24, 24, -12, 12, 0, -12, 24, -24, -12;
     -36, 72, -36, 0, 72, -90, -72, 18, -18, 54;
     -24, 24, -24, -24, 24, -18, -24, -6, 6, 30;
     36, -72, 0, 0, -72, 72, 36, 0, 0, -36;
     -72, 36, 0, 0, 72, -36, -36, 0, -36, 36;
     -48, 12, 24, -48, 48, 0, -12, 24, -24, -12;
     36, -36, 0, 36, -72, 18, 36, -54, 18, -18;
     36, 0, 0, 0, -36, 0, 0, 0, 0, -36;
     60, -60, 24, 24, -96, 54, 24, -30, 30, -66;
     -12, 48, -48, -12, 48, -72, -48, 24, -24, 60;
     60, -24, -12, 24, -60, 0, 24, -12, 48, -12;
     -60, 60, 12, -24, 96, -36, -24, 12, -12, 12;
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
theorem pair24_01_06_certificate :
    pair24_01_06Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_01_06Rows id +
      pair24_01_06Inverse * integerInformationSelector pair24_01_06Free = (36 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_01_06_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_01_06Inverse.mulVec (fun t => if b t then 1 else -1) k = 36 ∨
      pair24_01_06Inverse.mulVec (fun t => if b t then 1 else -1) k = -36) →
    IntegerScaledHalfPattern 36 (1)
      (∑ k, encodedIntFrame base24Masks 1 k * pair24_01_06Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 6 k * pair24_01_06Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_01_06_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {1, 6} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 1 k * x k) (∑ k, base24Frame 6 k * x k) := by
  have h := order24_integer_pair_lift 1 6 pair24_01_06Rows pair24_01_06Free
    pair24_01_06Left pair24_01_06Inverse 36 (1) (by norm_num) (by decide +kernel)
    pair24_01_06_certificate pair24_01_06_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
