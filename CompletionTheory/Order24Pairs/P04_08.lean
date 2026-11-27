/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P03_15
@[expose] public section
namespace CompletionTheory

def pair24_04_08Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15]
def pair24_04_08Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_04_08Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![9, -6, 7, 5, -2, -2, 1, 11, 3, -2, 3, 6, 8, -5;
     -3, 6, 3, -3, 6, -6, 3, 3, -3, 0, -3, -6, 0, 3;
     15, -12, 3, -3, -12, -6, 3, 12, -3, -9, 6, 12, 9, -15;
     -15, 18, -4, 1, 2, 14, 2, -20, 0, 8, 0, -9, -14, 17;
     -9, 12, 4, -1, 4, 4, -2, -4, -6, 4, -6, -3, 2, 1;
     3, 0, 5, 1, 2, -4, -7, -2, 9, -1, 0, 0, -5, -1;
     -15, 18, -1, 7, -4, 8, 5, -5, -9, 2, -9, 0, -8, 11;
     15, -12, 3, -3, -12, -6, 3, 21, -3, -18, -3, 12, 18, -15;
     3, 0, -4, 1, 2, -4, 2, -2, 0, 8, 0, -9, 4, -1;
     3, 0, -7, -5, 8, 2, -1, -8, 9, 5, 0, 0, -11, 5;
     15, -12, -6, -3, 6, -6, -6, -6, 6, 0, 6, 3, 0, 3;
     -3, 6, -3, 3, 0, 6, -3, 0, -3, 3, 6, -6, -3, -3;
     12, -12, -2, -4, 4, -2, -8, -4, 6, 10, 6, -6, -4, 4;
     6, -6, 2, 4, -4, 2, 8, 4, -6, -10, -6, 6, 4, -4;
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

def pair24_04_08Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-48, -12, -48, -48, 24, -24, -12, 12, -36, 12;
     0, 36, 0, 0, 0, 0, 36, 0, 36, 0;
     -72, 0, -36, -72, 36, -72, -72, 36, -72, 0;
     84, -24, 84, 120, -24, 78, 48, -30, 54, 6;
     24, 24, 24, 24, 24, 30, 24, -6, 54, 30;
     12, -24, -24, -24, -24, 24, 12, 24, 0, -12;
     12, 12, 84, 84, 48, 60, 48, -12, 36, 24;
     -108, 36, -36, -108, 72, -72, -72, 36, -72, 0;
     12, 12, -24, 12, -24, -30, 12, -30, 18, 6;
     48, -24, 12, 12, -60, 24, 12, -12, 0, -48;
     0, -36, -36, -36, -72, -18, -36, -18, -18, -54;
     36, 0, 0, 36, 0, 0, 0, 0, 0, 36;
     24, -48, -48, -12, -84, -24, -12, -24, 0, -24;
     -60, 12, 12, -24, 48, -12, -24, -12, -36, -12;
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
theorem pair24_04_08_certificate :
    pair24_04_08Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_04_08Rows id +
      pair24_04_08Inverse * integerInformationSelector pair24_04_08Free = (36 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_04_08_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_04_08Inverse.mulVec (fun t => if b t then 1 else -1) k = 36 ∨
      pair24_04_08Inverse.mulVec (fun t => if b t then 1 else -1) k = -36) →
    IntegerScaledHalfPattern 36 (1)
      (∑ k, encodedIntFrame base24Masks 4 k * pair24_04_08Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 8 k * pair24_04_08Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_04_08_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {4, 8} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 4 k * x k) (∑ k, base24Frame 8 k * x k) := by
  have h := order24_integer_pair_lift 4 8 pair24_04_08Rows pair24_04_08Free
    pair24_04_08Left pair24_04_08Inverse 36 (1) (by norm_num) (by decide +kernel)
    pair24_04_08_certificate pair24_04_08_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
