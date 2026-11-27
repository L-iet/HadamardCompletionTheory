/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P10_14
@[expose] public section
namespace CompletionTheory

def pair24_11_14Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 15]
def pair24_11_14Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_11_14Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![9, -8, 1, 3, -2, 0, 0, -1, -4, 1, 5, 3, 4, 1;
     -1, 2, 1, -1, 0, 2, -2, 1, 0, 1, -1, -1, -2, 1;
     -22, 23, 4, -4, 9, -1, 1, 4, 9, 1, -10, -7, -5, -2;
     7, -6, -2, 1, -4, -2, 2, 0, -2, -2, 2, 4, 1, 1;
     21, -20, -2, 3, -8, 0, 0, -4, -10, -2, 8, 6, 7, 1;
     -14, 15, 4, -2, 5, 1, -1, 0, 7, 1, -4, -5, -5, -2;
     -11, 12, 1, 1, 2, -2, 2, 3, 4, 1, -7, -5, -2, 1;
     -49, 50, 7, -7, 18, 2, 4, 7, 18, 1, -19, -19, -14, 1;
     49, -48, -8, 7, -16, -2, -4, -6, -20, -2, 20, 16, 13, 1;
     4, -3, -2, -2, -1, 1, -1, 0, 1, 1, 2, 1, 1, -2;
     5, -4, -2, -1, 0, 2, -2, -2, 0, -2, 2, 2, 1, 1;
     8, -7, -2, 2, -3, -1, 1, -2, -3, 1, 2, 5, 1, -2;
     46, -46, -6, 4, -14, -2, -4, -8, -16, 0, 18, 16, 12, 0;
     -40, 40, 6, -4, 14, 2, 4, 8, 16, 0, -18, -16, -12, 0;
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

def pair24_11_14Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-24, -36, -24, -24, -24, 0, -12, -12, -36, -12;
     0, 12, 0, 0, 0, 0, 12, 0, 12, 0;
     48, 72, 60, 48, 84, 12, 48, 48, 84, 36;
     -12, -24, -12, 0, -24, -6, -24, -18, -30, -6;
     -48, -72, -48, -48, -72, -6, -48, -42, -78, -30;
     36, 48, 24, 24, 48, 12, 36, 36, 60, 24;
     12, 36, 36, 36, 48, 12, 24, 12, 36, 24;
     108, 156, 132, 108, 168, 48, 120, 84, 192, 72;
     -108, -156, -120, -108, -168, -42, -108, -90, -186, -78;
     0, 0, -12, -12, -12, -12, -12, 0, -12, -12;
     0, -12, -12, -12, -24, -6, -12, -6, -6, -18;
     -12, -24, -24, -12, -24, -12, -24, -12, -36, 0;
     -96, -144, -120, -108, -156, -48, -108, -72, -168, -72;
     84, 132, 108, 96, 144, 36, 96, 60, 156, 60;
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
theorem pair24_11_14_certificate :
    pair24_11_14Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_11_14Rows id +
      pair24_11_14Inverse * integerInformationSelector pair24_11_14Free = (12 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_11_14_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_11_14Inverse.mulVec (fun t => if b t then 1 else -1) k = 12 ∨
      pair24_11_14Inverse.mulVec (fun t => if b t then 1 else -1) k = -12) →
    IntegerScaledHalfPattern 12 (1)
      (∑ k, encodedIntFrame base24Masks 11 k * pair24_11_14Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 14 k * pair24_11_14Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_11_14_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {11, 14} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 11 k * x k) (∑ k, base24Frame 14 k * x k) := by
  have h := order24_integer_pair_lift 11 14 pair24_11_14Rows pair24_11_14Free
    pair24_11_14Left pair24_11_14Inverse 12 (1) (by norm_num) (by decide +kernel)
    pair24_11_14_certificate pair24_11_14_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
