/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P00_05
@[expose] public section
namespace CompletionTheory

def pair24_00_06Rows : Fin 14 → Fin 16 := ![1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def pair24_00_06Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_00_06Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![6, 15, 9, 6, 0, 3, 3, 15, 3, 0, 0, 6, 9, -3;
     6, -1, 1, -2, 24, -1, -21, -25, 15, 12, -4, -10, -31, 37;
     6, 5, -5, 10, -12, 5, -3, -1, -3, -6, 2, 14, -7, -5;
     6, 1, -7, -10, -24, 13, 27, 25, -27, -12, 10, -8, 37, -31;
     6, 9, -3, -6, 0, -3, 3, 9, -15, 0, -6, 0, 21, -15;
     6, 7, 5, 2, 12, -17, -9, -23, 27, 6, -2, -2, -29, 17;
     6, 1, 11, -10, -24, 13, 9, 25, -27, -12, -8, 10, 19, -13;
     6, 5, -5, 10, -12, 5, -3, 17, -3, -24, -16, 14, 11, -5;
     6, -11, 5, 2, 12, 1, -9, -23, 9, 24, -2, -20, -11, 17;
     6, -11, -13, 2, 12, 1, 9, -5, 9, 6, -2, -2, -11, -1;
     6, -13, -5, 10, 24, -13, -3, -37, 15, 12, 2, -4, -25, 31;
     6, -1, 1, -2, -12, -1, 15, 29, -21, -6, 14, -10, 23, -35;
     0, -2, -10, 8, 12, -14, 6, -14, 6, 24, 4, -20, -14, 14;
     0, 8, 4, 4, -12, 20, 12, 20, -24, -24, -16, 8, 20, -20;
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

def pair24_00_06Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-36, 0, -36, -36, 72, 0, 36, 36, 0, 36;
     60, -96, 60, 60, -168, 144, 132, -84, 48, -84;
     -12, -24, 60, -12, 48, 0, -12, 60, -24, -12;
     -60, 168, -60, 12, 168, -180, -132, 48, -12, 120;
     -36, 72, -36, -36, 72, -36, -36, 0, 36, 72;
     84, -120, 12, 12, -120, 144, 84, 12, 24, -60;
     -132, 96, 12, 12, 168, -72, -60, 12, -48, 84;
     -84, 48, 60, -84, 120, 0, -12, 60, -24, -12;
     84, -48, 12, 84, -120, 36, 84, -96, 60, -24;
     84, 24, 12, 12, -48, 0, 12, 12, 24, -60;
     132, -96, 60, 60, -168, 108, 60, -48, 84, -120;
     -12, 120, -84, -12, 120, -144, -84, 60, -24, 132;
     120, -48, -24, 48, -120, 0, 48, -24, 96, -24;
     -120, 120, 24, -48, 192, -72, -48, 24, -24, 24;
     72, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 72, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 72, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 72, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 72, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 72, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 72, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 72, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 72, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 72]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_00_06_certificate :
    pair24_00_06Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_00_06Rows id +
      pair24_00_06Inverse * integerInformationSelector pair24_00_06Free = (72 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_00_06_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_00_06Inverse.mulVec (fun t => if b t then 1 else -1) k = 72 ∨
      pair24_00_06Inverse.mulVec (fun t => if b t then 1 else -1) k = -72) →
    IntegerScaledHalfPattern 72 (1)
      (∑ k, encodedIntFrame base24Masks 0 k * pair24_00_06Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 6 k * pair24_00_06Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_00_06_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {0, 6} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 0 k * x k) (∑ k, base24Frame 6 k * x k) := by
  have h := order24_integer_pair_lift 0 6 pair24_00_06Rows pair24_00_06Free
    pair24_00_06Left pair24_00_06Inverse 72 (1) (by norm_num) (by decide +kernel)
    pair24_00_06_certificate pair24_00_06_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
