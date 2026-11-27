/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P00_10
@[expose] public section
namespace CompletionTheory

def pair24_00_11Rows : Fin 14 → Fin 16 := ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15]
def pair24_00_11Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_00_11Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![6, 15, 9, 6, 0, 0, 3, 3, 15, 3, 0, 6, 9, -3;
     6, 5, -5, -2, 12, -12, 5, -3, 5, -3, -4, -10, -1, 7;
     6, 2, -2, 10, -6, 6, 2, -12, -16, 6, 2, 14, -22, 10;
     6, -5, -1, -10, -12, 12, 7, 9, -5, -9, 10, -8, 7, -1;
     6, 9, -3, -6, 0, 0, -3, 3, 9, -15, -6, 0, 21, -15;
     6, 10, 2, 2, 6, -6, -14, 0, -8, 18, -2, -2, -14, 2;
     6, -5, 17, -10, -12, 12, 7, -9, -5, -9, -8, 10, -11, 17;
     6, -7, 7, 10, 12, 24, -7, -39, -43, 33, -16, 14, -49, 55;
     6, 1, -7, 2, -12, -24, 13, 27, 37, -27, -2, -20, 49, -43;
     6, -8, -16, 2, 6, -6, 4, 18, 10, 0, -2, -2, 4, -16;
     6, -7, -11, 10, 12, -12, -7, 15, -7, -3, 2, -4, 5, 1;
     6, -4, 4, -2, -6, 6, -4, 6, 14, -12, 14, -10, 8, -20;
     0, 10, -22, 8, -12, -24, -2, 42, 46, -30, 4, -20, 46, -46;
     0, -4, 16, 4, 12, 24, 8, -24, -40, 12, -16, 8, -40, 40;
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

def pair24_00_11Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-36, 0, -36, -36, 72, 0, 36, 36, 0, 36;
     -12, 48, -12, -12, -24, 0, 60, -12, 48, -12;
     24, -96, 96, 24, -24, 72, 24, 24, -24, -48;
     12, 24, 12, 84, 24, -36, -60, -24, -12, 48;
     -36, 72, -36, -36, 72, -36, -36, 0, 36, 72;
     48, -48, -24, -24, -48, 72, 48, 48, 24, -24;
     -60, -48, 84, 84, 24, 72, 12, -60, -48, 12;
     60, -240, 204, 60, -168, 288, 132, -84, -24, -156;
     -60, 240, -132, -60, 168, -252, -60, 48, 60, 120;
     48, 96, -24, -24, 24, -72, -24, 48, 24, -24;
     60, 48, -12, -12, -24, -36, -12, 24, 84, -48;
     24, 48, -48, 24, 48, -72, -48, 24, -24, 96;
     -24, 240, -168, -96, 168, -288, -96, 120, 96, 120;
     24, -168, 168, 96, -96, 216, 96, -120, -24, -120;
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
theorem pair24_00_11_certificate :
    pair24_00_11Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_00_11Rows id +
      pair24_00_11Inverse * integerInformationSelector pair24_00_11Free = (72 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_00_11_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_00_11Inverse.mulVec (fun t => if b t then 1 else -1) k = 72 ∨
      pair24_00_11Inverse.mulVec (fun t => if b t then 1 else -1) k = -72) →
    IntegerScaledHalfPattern 72 (1)
      (∑ k, encodedIntFrame base24Masks 0 k * pair24_00_11Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 11 k * pair24_00_11Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_00_11_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {0, 11} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 0 k * x k) (∑ k, base24Frame 11 k * x k) := by
  have h := order24_integer_pair_lift 0 11 pair24_00_11Rows pair24_00_11Free
    pair24_00_11Left pair24_00_11Inverse 72 (1) (by norm_num) (by decide +kernel)
    pair24_00_11_certificate pair24_00_11_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
