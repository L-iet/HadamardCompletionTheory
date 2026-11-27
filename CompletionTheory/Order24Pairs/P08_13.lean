/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P08_09
@[expose] public section
namespace CompletionTheory

def pair24_08_13Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 14, 15]
def pair24_08_13Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_08_13Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![-9, 12, 7, 5, 6, 4, 4, 1, -1, 3, 4, -3, -4, 7;
     15, -12, 3, -3, -6, 0, -12, 3, 15, -3, -6, 3, 12, -9;
     -21, 24, 3, -3, 12, 0, 6, 3, -12, -3, 3, -6, -15, 9;
     12, -9, -4, 1, -9, -7, 5, 2, -2, 0, -1, 9, 4, -1;
     0, 3, 4, -1, -3, 1, 1, -2, 2, -6, 1, -3, 8, -5;
     3, 0, 5, 1, 0, 2, -4, -7, -2, 9, -1, 0, -5, -1;
     -15, 18, -1, 7, 0, -4, 8, 5, -5, -9, 2, -9, -8, 11;
     -21, 24, 3, -3, 12, 0, 6, 3, -3, -3, -6, -15, -6, 9;
     30, -27, -4, 1, -9, -7, -13, 2, 16, 0, -1, 9, 22, -19;
     3, 0, -7, -5, 0, 8, 2, -1, -8, 9, 5, 0, -11, 5;
     6, -3, -6, -3, 3, 9, -3, -6, -12, 6, 3, 3, -6, 9;
     15, -12, -3, 3, -6, -6, 0, -3, 12, -3, -3, 12, 9, -15;
     30, -30, -2, -4, -6, -2, -8, -8, 8, 6, 4, 12, 8, -8;
     -12, 12, 2, 4, 6, 2, 8, 8, -8, -6, -4, -12, -8, 8;
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

def pair24_08_13Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![24, -12, 24, 24, 24, 48, 60, 12, 36, 12;
     -72, 36, -72, -72, 0, -72, -36, 0, -36, 0;
     72, 0, 108, 72, 36, 72, 72, 36, 72, 0;
     -24, -24, -24, 12, -24, -30, -60, -30, -54, 6;
     -12, 24, -12, -12, 24, -6, -12, -6, 18, 30;
     12, -24, -24, -24, -24, 24, 12, 24, 0, -12;
     12, 12, 84, 84, 48, 60, 48, -12, 36, 24;
     36, 36, 108, 36, 72, 72, 72, 36, 72, 0;
     -96, 12, -132, -96, -24, -138, -96, -30, -90, 6;
     48, -24, 12, 12, -60, 24, 12, -12, 0, -48;
     36, -36, 0, 0, -72, 18, 0, -18, 18, -54;
     -36, 0, -72, -36, 0, -72, -72, 0, -72, 36;
     -48, -48, -120, -84, -84, -96, -84, -24, -72, -24;
     12, 12, 84, 48, 48, 60, 48, -12, 36, -12;
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
theorem pair24_08_13_certificate :
    pair24_08_13Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_08_13Rows id +
      pair24_08_13Inverse * integerInformationSelector pair24_08_13Free = (36 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_08_13_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_08_13Inverse.mulVec (fun t => if b t then 1 else -1) k = 36 ∨
      pair24_08_13Inverse.mulVec (fun t => if b t then 1 else -1) k = -36) →
    IntegerScaledHalfPattern 36 (1)
      (∑ k, encodedIntFrame base24Masks 8 k * pair24_08_13Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 13 k * pair24_08_13Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_08_13_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {8, 13} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 8 k * x k) (∑ k, base24Frame 13 k * x k) := by
  have h := order24_integer_pair_lift 8 13 pair24_08_13Rows pair24_08_13Free
    pair24_08_13Left pair24_08_13Inverse 36 (1) (by norm_num) (by decide +kernel)
    pair24_08_13_certificate pair24_08_13_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
