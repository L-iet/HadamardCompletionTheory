/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P03_10
@[expose] public section
namespace CompletionTheory

def pair24_03_14Rows : Fin 14 → Fin 16 := ![0, 1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15]
def pair24_03_14Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_03_14Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![-27, 29, 8, 11, 3, 3, 4, 10, 2, -8, 3, -9, -7, 2;
     13, -11, 0, -5, 3, -5, 0, -6, 2, 4, -1, 3, 1, 2;
     16, -14, 0, -2, -6, -2, 0, -6, 2, 4, -4, 6, 10, -4;
     -1, 3, -2, -3, -3, 5, 2, 2, -4, -2, 1, 3, -3, 2;
     -3, 5, 2, -1, 3, 3, -2, -2, -4, -2, 3, -3, -1, 2;
     2, 0, 4, 0, 0, -4, -4, 2, 2, 4, -2, 0, 0, -4;
     -37, 39, 4, 9, -3, 5, 8, 14, 2, -20, 1, -15, -9, 2;
     7, -5, 0, 1, -3, 1, 0, -6, 2, 4, -7, -3, 7, 2;
     -7, 9, -2, 3, 3, -1, 2, 2, -4, -2, 7, -3, -9, 2;
     38, -36, -8, -12, 0, -4, -4, -10, 2, 16, -2, 12, 12, -4;
     25, -23, -6, -5, 3, -5, -6, -6, -4, 10, -1, 9, 7, 2;
     -14, 16, 0, 4, 0, 4, 0, 6, 2, -8, 2, 0, -8, -4;
     32, -32, -4, -8, 0, -4, -8, -8, 0, 12, 4, 12, 4, 0;
     -20, 20, 4, 8, 0, 4, 8, 8, 0, -12, -4, -12, -4, 0;
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

def pair24_03_14Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![60, 72, 60, 60, 96, 36, 84, 48, 108, 48;
     -36, -24, -36, -36, -48, -12, -12, -24, -36, -24;
     -48, -48, -24, -48, -24, -24, -48, 0, -72, -24;
     12, 0, 12, 36, 0, 0, -12, -12, 0, 12;
     12, 0, 12, 12, 0, 24, 12, -12, 24, 12;
     0, 0, -24, -24, 0, 0, 0, 24, 0, 0;
     60, 120, 108, 108, 144, 36, 84, 48, 132, 72;
     -36, -24, 12, -36, 0, 12, -12, 0, -36, -24;
     36, 24, 12, 36, 0, 0, 36, -12, 48, 12;
     -72, -96, -96, -96, -120, -48, -96, -48, -144, -72;
     -36, -72, -60, -60, -96, -24, -60, -36, -72, -60;
     48, 48, 24, 48, 48, 0, 24, 24, 48, 48;
     -48, -96, -96, -72, -120, -48, -72, -48, -96, -48;
     24, 72, 72, 48, 96, 24, 48, 24, 72, 24;
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
theorem pair24_03_14_certificate :
    pair24_03_14Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_03_14Rows id +
      pair24_03_14Inverse * integerInformationSelector pair24_03_14Free = (24 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_03_14_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_03_14Inverse.mulVec (fun t => if b t then 1 else -1) k = 24 ∨
      pair24_03_14Inverse.mulVec (fun t => if b t then 1 else -1) k = -24) →
    IntegerScaledHalfPattern 24 (1)
      (∑ k, encodedIntFrame base24Masks 3 k * pair24_03_14Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 14 k * pair24_03_14Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_03_14_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {3, 14} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 3 k * x k) (∑ k, base24Frame 14 k * x k) := by
  have h := order24_integer_pair_lift 3 14 pair24_03_14Rows pair24_03_14Free
    pair24_03_14Left pair24_03_14Inverse 24 (1) (by norm_num) (by decide +kernel)
    pair24_03_14_certificate pair24_03_14_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
