/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P02_04
@[expose] public section
namespace CompletionTheory

def pair24_02_08Rows : Fin 14 → Fin 16 := ![0, 1, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15]
def pair24_02_08Free : Fin 10 → Fin 24 := ![13, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_02_08Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![19, -17, -6, -9, -1, -15, -18, 16, 16, 13, 25, -1, 14, -12;
     7, -5, -6, -5, 3, -11, -6, 8, 4, 5, 9, -5, 6, -4;
     7, -5, -6, -1, -5, -7, -6, 6, 4, 3, 11, 3, 4, -8;
     -8, 10, 6, 2, -2, 14, 12, -12, -8, -6, -10, 0, -8, 10;
     10, -8, -6, -8, 0, -8, -12, 8, 4, 8, 12, -2, 12, -10;
     19, -17, -6, -9, -1, -15, -18, 10, 16, 7, 19, -1, 8, -12;
     -11, 13, 6, 1, -3, 7, 6, -4, -8, -1, -9, 1, -6, 8;
     1, 1, -6, 1, -3, -5, -6, 8, 4, -1, 3, 1, 6, -4;
     -8, 10, 6, 6, 2, 6, 12, -8, -8, -2, -14, -4, -4, 6;
     -11, 13, 6, 9, 5, 15, 18, -14, -8, -11, -23, 5, -16, 12;
     -8, 10, 6, 10, 6, 10, 12, -16, -8, -10, -18, 4, -12, 14;
     -5, 7, 6, 3, -1, 9, 6, -2, -8, -5, -5, -1, -4, 0;
     6, -6, 0, 2, 2, 2, 0, -4, 0, 2, -2, -2, -4, 4;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     6, -6, 0, -2, -2, -2, 0, 4, 0, -2, 2, 2, 4, -4;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def pair24_02_08Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![84, -36, -168, -84, -96, -96, -60, 36, -48, 36;
     36, 12, -72, -36, -48, -48, -12, 12, 0, 12;
     36, -12, -48, -36, -24, -48, -36, 36, -24, 12;
     -48, 0, 96, 72, 48, 60, 24, -36, 12, -12;
     48, 0, -96, -48, -48, -60, -48, 12, -12, 36;
     60, -36, -144, -84, -96, -72, -60, 36, -48, 12;
     -12, 12, 72, 60, 48, 48, 36, -12, 24, 12;
     36, 12, -24, -36, 0, -24, -12, 36, 0, 12;
     -48, 24, 72, 48, 48, 36, 48, -36, 36, -12;
     -84, 12, 144, 60, 72, 96, 60, -36, 24, -60;
     -72, 0, 120, 48, 48, 84, 48, -36, 36, -60;
     -36, 12, 48, 36, 48, 24, 12, -12, 0, 12;
     -24, -24, 0, 0, -24, 0, 0, -24, 0, -24;
     24, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, -24, -24, 0, -24, -24, 0, -24, 0;
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
theorem pair24_02_08_certificate :
    pair24_02_08Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_02_08Rows id +
      pair24_02_08Inverse * integerInformationSelector pair24_02_08Free = (24 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_02_08_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_02_08Inverse.mulVec (fun t => if b t then 1 else -1) k = 24 ∨
      pair24_02_08Inverse.mulVec (fun t => if b t then 1 else -1) k = -24) →
    IntegerScaledHalfPattern 24 (1)
      (∑ k, encodedIntFrame base24Masks 2 k * pair24_02_08Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 8 k * pair24_02_08Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_02_08_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {2, 8} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 2 k * x k) (∑ k, base24Frame 8 k * x k) := by
  have h := order24_integer_pair_lift 2 8 pair24_02_08Rows pair24_02_08Free
    pair24_02_08Left pair24_02_08Inverse 24 (1) (by norm_num) (by decide +kernel)
    pair24_02_08_certificate pair24_02_08_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
