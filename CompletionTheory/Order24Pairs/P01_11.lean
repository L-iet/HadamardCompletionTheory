/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P01_07
@[expose] public section
namespace CompletionTheory

def pair24_01_11Rows : Fin 14 → Fin 16 := ![0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15]
def pair24_01_11Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_01_11Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![6, 14, 10, 4, 0, 0, 2, 0, 14, 6, 2, 8, 8, -2;
     6, 4, -4, -4, 12, -12, 4, -6, 4, 0, -2, -8, -2, 8;
     6, 1, -1, 8, -6, 6, 1, -15, -17, 9, 4, 16, -23, 11;
     6, -6, 0, -12, -12, 12, 6, 6, -6, -6, 12, -6, 6, 0;
     6, 8, -2, -8, 0, 0, -4, 0, 8, -12, -4, 2, 20, -14;
     6, 9, 3, 0, 6, -6, -15, -3, -9, 21, 0, 0, -15, 3;
     6, -6, 18, -12, -12, 12, 6, -12, -6, -6, -6, 12, -12, 18;
     6, -8, 8, 8, 12, 24, -8, -42, -44, 36, -14, 16, -50, 56;
     6, 0, -6, 0, -12, -24, 12, 24, 36, -24, 0, -18, 48, -42;
     6, -9, -15, 0, 6, -6, 3, 15, 9, 3, 0, 0, 3, -15;
     6, -8, -10, 8, 12, -12, -8, 12, -8, 0, 4, -2, 4, 2;
     6, -5, 5, -4, -6, 6, -5, 3, 13, -9, 16, -8, 7, -19;
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

def pair24_01_11Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-48, -24, -48, -48, 48, 0, 24, 24, -24, 24;
     -24, 24, -24, -24, -48, 0, 48, -24, 24, -24;
     12, -120, 84, 12, -48, 72, 12, 12, -48, -60;
     0, 0, 0, 72, 0, -36, -72, -36, -36, 36;
     -48, 48, -48, -48, 48, -36, -48, -12, 12, 60;
     36, -72, -36, -36, -72, 72, 36, 36, 0, -36;
     -72, -72, 72, 72, 0, 72, 0, -72, -72, 0;
     48, -264, 192, 48, -192, 288, 120, -96, -48, -168;
     -72, 216, -144, -72, 144, -252, -72, 36, 36, 108;
     36, 72, -36, -36, 0, -72, -36, 36, 0, -36;
     48, 24, -24, -24, -48, -36, -24, 12, 60, -60;
     12, 24, -60, 12, 24, -72, -60, 12, -48, 84;
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
theorem pair24_01_11_certificate :
    pair24_01_11Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_01_11Rows id +
      pair24_01_11Inverse * integerInformationSelector pair24_01_11Free = (72 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_01_11_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_01_11Inverse.mulVec (fun t => if b t then 1 else -1) k = 72 ∨
      pair24_01_11Inverse.mulVec (fun t => if b t then 1 else -1) k = -72) →
    IntegerScaledHalfPattern 72 (1)
      (∑ k, encodedIntFrame base24Masks 1 k * pair24_01_11Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 11 k * pair24_01_11Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_01_11_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {1, 11} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 1 k * x k) (∑ k, base24Frame 11 k * x k) := by
  have h := order24_integer_pair_lift 1 11 pair24_01_11Rows pair24_01_11Free
    pair24_01_11Left pair24_01_11Inverse 72 (1) (by norm_num) (by decide +kernel)
    pair24_01_11_certificate pair24_01_11_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
