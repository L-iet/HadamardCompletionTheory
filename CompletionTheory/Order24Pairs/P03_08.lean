/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P03_04
@[expose] public section
namespace CompletionTheory

def pair24_03_08Rows : Fin 14 → Fin 16 := ![0, 1, 2, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15]
def pair24_03_08Free : Fin 10 → Fin 24 := ![13, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_03_08Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![11, -7, 6, -3, 1, -9, -12, 14, 14, 11, 17, 1, 10, -6;
     -13, 17, 6, 5, 9, -1, 12, -2, -10, -5, -15, -7, -6, 10;
     -13, 17, 6, 13, -7, 7, 12, -6, -10, -9, -11, 9, -10, 2;
     11, -7, -6, -11, -7, 7, 0, -6, 2, 3, 13, -3, 2, 2;
     -7, 11, 6, -1, 3, 5, 0, -2, -10, 1, -9, -1, 6, -2;
     11, -7, 6, -3, 1, -9, -12, 2, 14, -1, 5, 1, -2, -6;
     5, -1, -6, -13, -9, -7, -12, 10, 2, 13, 15, -1, 6, -2;
     -25, 29, 6, 17, -3, 11, 12, -2, -10, -17, -27, 5, -6, 10;
     11, -7, -6, -3, 1, -9, 0, 2, 2, 11, 5, -11, 10, -6;
     5, -1, -6, 3, 7, 9, 12, -10, 2, -7, -13, 7, -14, 6;
     11, -7, -6, 5, 9, -1, 0, -14, 2, -5, -3, 5, -6, 10;
     17, -13, -6, -9, -5, -3, -12, 14, 2, 5, 23, -5, 10, -18;
     12, -12, 0, 4, 4, 4, 0, -8, 0, 4, -4, -4, -8, 8;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     12, -12, 0, -4, -4, -4, 0, 8, 0, -4, 4, 4, 8, -8;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def pair24_03_08Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![60, -36, -120, -60, -48, -48, -12, 36, -24, 36;
     -36, 60, 72, 36, 48, 48, 84, -12, 72, -12;
     -36, 12, 120, 36, 96, 48, 36, 36, 24, -12;
     12, -36, -24, 36, -48, -24, -60, -36, -48, 12;
     -12, 36, 24, 12, 48, 24, 12, -12, 48, 36;
     12, -36, -72, -60, -48, 0, -12, 36, -24, -12;
     84, -12, -72, 12, -48, -48, -36, 12, -24, 60;
     -36, 60, 168, 36, 144, 96, 84, 36, 72, -12;
     12, 12, -72, -12, -48, -72, -12, -36, 0, 12;
     -60, -12, 72, 12, 0, 48, 12, -36, -24, -84;
     -36, -36, 24, -12, -48, 24, -12, -36, 0, -84;
     36, -12, -120, -36, -48, -96, -84, 12, -72, 60;
     -48, -48, 0, 0, -48, 0, 0, -48, 0, -48;
     48, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, -48, -48, 0, -48, -48, 0, -48, 0;
     0, 48, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 48, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 48, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 48, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 48, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 48, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 48, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 48, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 48]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_03_08_certificate :
    pair24_03_08Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_03_08Rows id +
      pair24_03_08Inverse * integerInformationSelector pair24_03_08Free = (48 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_03_08_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_03_08Inverse.mulVec (fun t => if b t then 1 else -1) k = 48 ∨
      pair24_03_08Inverse.mulVec (fun t => if b t then 1 else -1) k = -48) →
    IntegerScaledHalfPattern 48 (1)
      (∑ k, encodedIntFrame base24Masks 3 k * pair24_03_08Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 8 k * pair24_03_08Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_03_08_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {3, 8} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 3 k * x k) (∑ k, base24Frame 8 k * x k) := by
  have h := order24_integer_pair_lift 3 8 pair24_03_08Rows pair24_03_08Free
    pair24_03_08Left pair24_03_08Inverse 48 (1) (by norm_num) (by decide +kernel)
    pair24_03_08_certificate pair24_03_08_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
