/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.IntegerPairCertificates
@[expose] public section
namespace CompletionTheory

def pair24_00_01Rows : Fin 14 → Fin 16 := ![2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def pair24_00_01Free : Fin 10 → Fin 24 := ![11, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_00_01Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![7, 5, 4, 8, 2, 1, -9, -12, 15, 5, -7, 8, -12, 21;
     3, -3, 0, 12, -6, 3, -9, -12, 9, 3, -9, 0, -12, 21;
     3, -3, 6, 0, 0, 3, -9, -15, 9, 0, -6, 12, -15, 15;
     -1, -2, -4, -2, 4, 5, 0, -12, 3, 1, -2, 1, -3, 12;
     4, -1, -2, 8, 2, -2, -9, -15, 6, 5, -10, 5, -6, 15;
     8, -2, 2, 4, -8, -4, 0, -6, 12, -2, -8, 4, -6, 6;
     -4, 10, -4, 4, 10, 2, -18, -27, 12, 7, -11, 10, -27, 36;
     0, 0, 6, 6, 6, 0, -18, -21, 18, -3, -15, 12, -21, 30;
     -1, -2, 2, 4, -8, 5, 0, -6, 3, 7, -8, -5, 3, 6;
     -1, -11, 2, 4, -8, 5, 9, 3, 3, -2, -8, 4, 3, -3;
     0, -9, 6, 6, -12, 0, 9, -3, 0, -3, -6, 3, 6, 3;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     4, -10, 4, -4, -10, -2, 18, 18, -12, 2, 2, -10, 18, -18;
     -1, 7, 2, 4, 10, 5, -9, -15, 3, -2, -8, 4, -15, 15;
     3, -3, 0, -6, -6, 3, 9, 15, -9, -6, 0, 0, 15, -15;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def pair24_00_01Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![36, -84, 36, 0, -48, 96, 72, -24, 12, -60;
     36, -36, 36, 0, -72, 72, 72, -36, 36, -72;
     36, -72, 72, 0, -36, 72, 36, 0, 0, -72;
     36, -24, 36, 36, -24, 30, 0, -30, 6, -30;
     36, -48, 36, 0, -48, 78, 36, -42, 30, -42;
     36, -24, 0, -36, -24, 48, 36, 24, 24, -48;
     36, -132, 108, 72, -96, 156, 72, -84, -12, -84;
     36, -108, 108, 0, -72, 144, 72, -36, 0, -108;
     36, 12, 0, 0, -24, -6, 36, -30, 42, -30;
     36, 48, 0, -36, 12, -24, 0, 24, 24, -48;
     36, 36, 0, -36, 0, -18, 0, 18, 54, -54;
     36, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 96, -72, -36, 60, -120, -36, 48, 48, 48;
     0, -60, 72, 36, -24, 84, 36, -48, -12, -48;
     0, 72, -36, -36, 72, -72, -36, 36, 0, 36;
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
theorem pair24_00_01_certificate :
    pair24_00_01Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_00_01Rows id +
      pair24_00_01Inverse * integerInformationSelector pair24_00_01Free = (36 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_00_01_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_00_01Inverse.mulVec (fun t => if b t then 1 else -1) k = 36 ∨
      pair24_00_01Inverse.mulVec (fun t => if b t then 1 else -1) k = -36) →
    IntegerScaledHalfPattern 36 (1)
      (∑ k, encodedIntFrame base24Masks 0 k * pair24_00_01Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 1 k * pair24_00_01Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_00_01_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {0, 1} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 0 k * x k) (∑ k, base24Frame 1 k * x k) := by
  have h := order24_integer_pair_lift 0 1 pair24_00_01Rows pair24_00_01Free
    pair24_00_01Left pair24_00_01Inverse 36 (1) (by norm_num) (by decide +kernel)
    pair24_00_01_certificate pair24_00_01_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
