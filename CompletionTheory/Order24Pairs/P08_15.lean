/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24Pairs.P08_11
@[expose] public section
namespace CompletionTheory

def pair24_08_15Rows : Fin 14 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14]
def pair24_08_15Free : Fin 10 → Fin 24 := ![14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def pair24_08_15Left : Matrix (Fin 24) (Fin 14) ℤ :=
  !![3, 3, 14, 10, 5, 1, 1, 2, 12, 6, 1, 1, 7, 6;
     3, 3, 6, -6, -3, 9, -15, 6, 12, -6, -3, -3, -9, 6;
     -15, 21, 6, -6, 15, -9, 3, 6, -6, -6, -3, -3, 9, -12;
     21, -15, -8, 2, -17, -13, 11, 4, -6, 0, -1, 17, -1, 6;
     -15, 21, 8, -2, -1, 7, 7, -4, -6, -12, 7, -11, -5, 6;
     3, 3, 10, 2, 1, 5, -7, -14, -6, 18, -1, -1, -1, -12;
     3, 3, -2, 14, -11, -19, 5, 10, 12, -18, -7, -7, 11, 6;
     -15, 21, 6, -6, 15, -9, 3, 6, 12, -6, -21, -21, 9, 6;
     3, 3, -8, 2, 1, 5, -7, 4, -6, 0, 17, -1, -19, 6;
     21, -15, -14, -10, -5, 11, -1, -2, -6, 18, 5, 5, 5, -12;
     39, -33, -12, -6, -3, 9, -15, -12, -6, 12, -3, 15, 9, 6;
     -15, 21, -6, 6, 3, 3, 15, -6, -6, -6, 9, 9, -15, -12;
     36, -36, -4, -8, -4, 4, -8, -16, 0, 12, 16, 16, -8, 0;
     0, 0, 4, 8, 4, -4, 8, 16, 0, -12, -16, -16, 8, 0;
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

def pair24_08_15Inverse : Matrix (Fin 24) (Fin 10) ℤ :=
  !![-36, -24, -36, -36, 48, 12, 36, 24, -12, 24;
     -36, 72, -36, -36, 0, -36, 36, 0, 36, 0;
     36, 0, 108, 36, 72, 36, 36, 72, 36, 0;
     -36, -48, -36, 36, -48, -48, -108, -60, -96, 12;
     36, 48, 36, 36, 48, 48, 36, -12, 96, 60;
     36, -48, -36, -36, -48, 60, 36, 48, 12, -24;
     -108, 24, 36, 36, 96, -12, -36, -24, -60, 48;
     -36, 72, 108, -36, 144, 36, 36, 72, 36, 0;
     36, 24, -36, 36, -48, -48, 36, -60, 48, 12;
     36, -48, -36, -36, -120, -12, -36, -24, -60, -96;
     -36, -72, -108, -108, -144, -72, -108, -36, -72, -108;
     108, 0, 36, 108, 0, 36, 36, 0, 36, 72;
     0, -96, -144, -72, -168, -96, -72, -48, -48, -48;
     -72, 24, 72, 0, 96, 24, 0, -24, -24, -24;
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
theorem pair24_08_15_certificate :
    pair24_08_15Left * (encodedIntFrame (n := 24) base24Masks).submatrix pair24_08_15Rows id +
      pair24_08_15Inverse * integerInformationSelector pair24_08_15Free = (72 : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair24_08_15_finite : ∀ b : Fin 10 → Bool,
    (∀ k, pair24_08_15Inverse.mulVec (fun t => if b t then 1 else -1) k = 72 ∨
      pair24_08_15Inverse.mulVec (fun t => if b t then 1 else -1) k = -72) →
    IntegerScaledHalfPattern 72 (1)
      (∑ k, encodedIntFrame base24Masks 8 k * pair24_08_15Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks 15 k * pair24_08_15Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem pair24_08_15_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {8, 15} x →
    HalfCorrelationPattern 24 (rationalRealCast (1))
      (∑ k, base24Frame 8 k * x k) (∑ k, base24Frame 15 k * x k) := by
  have h := order24_integer_pair_lift 8 15 pair24_08_15Rows pair24_08_15Free
    pair24_08_15Left pair24_08_15Inverse 72 (1) (by norm_num) (by decide +kernel)
    pair24_08_15_certificate pair24_08_15_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
