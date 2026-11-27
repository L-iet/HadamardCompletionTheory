/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P00_04
@[expose] public section
namespace CompletionTheory

def pair24_00_05Rows : Fin 14 → Fin 16 := ![1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def pair24_00_05Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_00_05Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![6, 15, 9, 6, 0, 3, 3, 15, 3, 0, 0, 6, 9, -3;
     6, 11, -11, -2, -24, 11, 15, 35, -21, -12, -4, -10, 29, -23;
     6, -1, 1, 10, 12, -1, -21, -31, 15, 6, 2, 14, -37, 25;
     6, -11, 5, -10, 24, 1, -9, -35, 9, 12, 10, -8, -23, 29;
     6, 9, -3, -6, 0, -3, 3, 9, -15, 0, -6, 0, 21, -15;
     6, 13, -1, 2, -12, -11, 9, 7, 9, -6, -2, -2, 1, -13;
     6, -11, 23, -10, 24, 1, -27, -35, 9, 12, -8, 10, -41, 47;
     6, -1, 1, 10, 12, -1, -21, -13, 15, -12, -16, 14, -19, 25;
     6, -5, -1, 2, -12, 7, 9, 7, -9, 12, -2, -20, 19, -13;
     6, -5, -19, 2, -12, 7, 27, 25, -9, -6, -2, -2, 19, -31;
     6, -1, -17, 10, -24, -1, 33, 23, -21, -12, 2, -4, 35, -29;
     6, -7, 7, -2, 12, -7, -3, -1, -3, 6, 14, -10, -7, -5;
     0, 4, -16, 8, -12, -8, 24, 16, -12, 12, 4, -20, 16, -16;
     0, 2, 10, 4, 12, 14, -6, -10, -6, -12, -16, 8, -10, 10;
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

def pair24_00_05Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-36, 0, -36, -36, 72, 0, 36, 36, 0, 36;
     -84, 192, -84, -84, 120, -144, -12, 60, 48, 60;
     60, -168, 132, 60, -96, 144, 60, -12, -24, -84;
     84, -120, 84, 156, -120, 108, 12, -96, -12, -24;
     -36, 72, -36, -36, 72, -36, -36, 0, 36, 72;
     12, 24, -60, -60, 24, 0, 12, 84, 24, 12;
     12, -192, 156, 156, -120, 216, 84, -132, -48, -60;
     -12, -96, 132, -12, -24, 144, 60, -12, -24, -84;
     12, 96, -60, 12, 24, -108, 12, -24, 60, 48;
     12, 168, -60, -60, 96, -144, -60, 84, 24, 12;
     -12, 192, -84, -84, 120, -180, -84, 96, 84, 24;
     60, -24, -12, 60, -24, 0, -12, -12, -24, 60;
     48, 96, -96, -24, 24, -144, -24, 48, 96, 48;
     -48, -24, 96, 24, 48, 72, 24, -48, -24, -48;
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
theorem pair24_00_05_certificate :
    pair24_00_05Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_00_05Rows id +
      pair24_00_05Inverse * integerInformationSelector pair24_00_05Free = (72 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_00_05_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_00_05Inverse.mulVec (fun t => if b t then 1 else -1) k = 72 ∨
      pair24_00_05Inverse.mulVec (fun t => if b t then 1 else -1) k = -72) →
    IntegerScaledHalfPattern 72 (1)
      (∑ k, encodedIntFrame base24Masks 0 k * pair24_00_05Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 5 k * pair24_00_05Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_00_05_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {0, 5} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 0 k * x k) (∑ k, base24Frame 5 k * x k) := by
  have h := order24_integer_pair_lift 0 5 pair24_00_05Rows pair24_00_05Free
    pair24_00_05Left pair24_00_05Inverse 72 (1) (by norm_num) (by decide +kernel)
    pair24_00_05_certificate pair24_00_05_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
