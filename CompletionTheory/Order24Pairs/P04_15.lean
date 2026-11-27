/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P04_11
@[expose] public section
namespace CompletionTheory

def pair24_04_15Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
def pair24_04_15Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_04_15Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![15, -10, 10, 10, 0, 0, 0, -5, 10, 10, 0, 5, 10, 5;
     -5, 10, 6, -6, 8, -12, 6, 3, 10, -8, -2, -5, -10, 5;
     25, -20, 0, 0, -10, 0, 0, -15, -5, 10, -5, 10, 20, -10;
     -25, 30, -1, -4, -8, 12, 9, 17, -5, -17, 2, 0, -15, 5;
     -15, 20, 7, -2, 6, 6, -3, 1, -5, -11, 6, -10, -5, 5;
     5, 0, 8, 2, 4, -6, -12, -1, -5, 16, -1, 0, 0, -10;
     -25, 30, 2, 8, -14, 6, 12, 11, 10, -26, -4, -15, 0, 5;
     25, -20, 0, 0, -10, 0, 0, -15, 10, 10, -20, -5, 20, 5;
     5, 0, -7, 2, 4, -6, 3, -1, -5, 1, 14, 0, -15, 5;
     5, 0, -10, -10, 10, 0, 0, 5, -5, 10, 5, 0, 0, -10;
     25, -20, -9, -6, 8, -12, -9, 3, -5, 7, -2, 10, 5, 5;
     -5, 10, -6, 6, 2, 12, -6, -3, -5, -2, 7, 10, -10, -10;
     20, -20, -2, -8, 4, -6, -12, 4, 0, 6, 14, 10, -10, 0;
     10, -10, 2, 8, -4, 6, 12, -4, 0, -6, -14, -10, 10, 0;
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

def pair24_04_15Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-60, -60, -60, -60, 0, 0, 0, 0, -60, 0;
     -12, 84, -12, -12, 24, -24, 48, 12, 60, 12;
     -60, -120, 0, -60, -60, 0, -60, 0, -120, -60;
     72, 96, 72, 132, 96, -6, 12, 18, 90, 78;
     36, 48, 36, 36, 48, 42, 36, -6, 90, 54;
     24, -48, -36, -36, -48, 48, 24, 36, 0, -24;
     -24, 108, 96, 96, 168, 12, 36, 24, 60, 84;
     -120, -60, 0, -120, 0, 0, -60, 0, -120, -60;
     24, 12, -36, 24, -48, -42, 24, -54, 30, 6;
     60, 0, 0, 0, -60, 0, 0, 0, 0, -60;
     -12, -36, -72, -72, -96, -54, -72, -18, -30, -78;
     72, -24, 12, 72, -24, 24, 12, -12, 0, 48;
     24, -48, -96, -36, -108, -72, -36, -24, 0, -24;
     -84, -12, 36, -24, 48, 12, -24, -36, -60, -36;
     60, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 60, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 60, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 60, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 60, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 60, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 60, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 60, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 60, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 60]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_04_15_certificate :
    pair24_04_15Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_04_15Rows id +
      pair24_04_15Inverse * integerInformationSelector pair24_04_15Free = (60 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_04_15_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_04_15Inverse.mulVec (fun t => if b t then 1 else -1) k = 60 ∨
      pair24_04_15Inverse.mulVec (fun t => if b t then 1 else -1) k = -60) →
    IntegerScaledHalfPattern 60 (1)
      (∑ k, encodedIntFrame base24Masks 4 k * pair24_04_15Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 15 k * pair24_04_15Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_04_15_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {4, 15} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 4 k * x k) (∑ k, base24Frame 15 k * x k) := by
  have h := order24_integer_pair_lift 4 15 pair24_04_15Rows pair24_04_15Free
    pair24_04_15Left pair24_04_15Inverse 60 (1) (by norm_num) (by decide +kernel)
    pair24_04_15_certificate pair24_04_15_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
