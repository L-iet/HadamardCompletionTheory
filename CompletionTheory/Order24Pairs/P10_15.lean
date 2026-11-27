/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P10_11
@[expose] public section
namespace CompletionTheory

def pair24_10_15Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14]
def pair24_10_15Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_10_15Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![-12, 18, 16, 8, 10, 2, 2, 4, 6, 12, 2, -4, 2, 6;
     18, -12, 4, -4, -8, 8, -16, 4, -6, 12, -4, 2, -4, 6;
     0, 6, 4, -4, 10, -10, 2, 4, -6, -6, -4, 2, 14, -12;
     21, -15, -8, 2, -17, -13, 11, 4, 0, -6, -1, 17, -1, 6;
     15, -9, 4, 2, -11, 5, 5, -8, -12, -6, 5, -1, 5, 6;
     -42, 48, 16, -4, 16, 8, -4, -8, 18, -6, 2, -16, -16, -12;
     48, -42, -8, 20, -26, -22, 2, 4, -18, 12, -10, 8, 26, 6;
     0, 6, 4, -4, 10, -10, 2, 4, -6, 12, -22, -16, 14, 6;
     3, 3, -8, 2, 1, 5, -7, 4, 0, -6, 17, -1, -19, 6;
     -24, 30, -8, -16, 10, 14, 2, 4, 18, -6, 8, -10, -10, -12;
     9, -3, -8, -10, 7, 11, -13, -8, 12, -6, -1, 5, -1, 6;
     0, 6, -8, 8, -2, 2, 14, -8, -6, -6, 8, 14, -10, -12;
     6, -6, 0, -12, 6, 6, -6, -12, 12, 0, 18, 6, -18, 0;
     30, -30, 0, 12, -6, -6, 6, 12, -12, 0, -18, -6, 18, 0;
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

def pair24_10_15Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![0, 24, 0, 0, 96, 24, 72, 48, 48, 48;
     -72, 24, -72, -72, -48, -48, 0, -24, -24, -24;
     0, -48, 72, 0, 24, 24, 0, 48, -24, -24;
     -36, -48, -36, 36, -48, -48, -108, -60, -96, 12;
     -36, -48, -36, -36, -48, 24, -36, -60, -24, 12;
     144, 96, 72, 72, 96, 96, 144, 120, 192, 48;
     -216, -120, -72, -72, -48, -48, -144, -96, -240, -24;
     -72, 24, 72, -72, 96, 24, 0, 48, -24, -24;
     36, 24, -36, 36, -48, -48, 36, -60, 48, 12;
     144, 96, 72, 72, 24, 24, 72, 48, 120, -24;
     36, 24, -36, -36, -48, -48, -36, 12, 48, -60;
     72, -48, 0, 72, -48, 24, 0, -24, -24, 48;
     72, 0, -72, 0, -72, -72, 0, 0, 72, 0;
     -144, -72, 0, -72, 0, 0, -72, -72, -144, -72;
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
theorem pair24_10_15_certificate :
    pair24_10_15Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_10_15Rows id +
      pair24_10_15Inverse * integerInformationSelector pair24_10_15Free = (72 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_10_15_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_10_15Inverse.mulVec (fun t => if b t then 1 else -1) k = 72 ∨
      pair24_10_15Inverse.mulVec (fun t => if b t then 1 else -1) k = -72) →
    IntegerScaledHalfPattern 72 (-1)
      (∑ k, encodedIntFrame base24Masks 10 k * pair24_10_15Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 15 k * pair24_10_15Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_10_15_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {10, 15} x →
    HalfCorrelationPattern 24 (rationalRealCast (-1))
      (∑ k, base24Frame 10 k * x k) (∑ k, base24Frame 15 k * x k) := by
  have h := order24_integer_pair_lift 10 15 pair24_10_15Rows pair24_10_15Free
    pair24_10_15Left pair24_10_15Inverse 72 (-1) (by norm_num) (by decide +kernel)
    pair24_10_15_certificate pair24_10_15_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
