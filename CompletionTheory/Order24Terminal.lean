/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.RationalSignCertificates
public import CompletionTheory.Order24Exchange
/-! # Kernel-checked terminality of the explicit sixteen-row frame
Generated exact coefficients are proof data, not an external proof oracle.
The exclusion of one- and two-row exchanges remains a separate obligation. -/
@[expose] public section
namespace CompletionTheory

def base24RationalFrame : Matrix (Fin 16) (Fin 24) ℚ :=
  (encodedIntFrame base24Masks).map (Int.castRingHom ℚ)

def base24FreeCoordinates : Fin 8 → Fin 24 := ![16, 17, 18, 19, 20, 21, 22, 23]

def base24TerminalLeft : Matrix (Fin 24) (Fin 16) ℚ :=
  !![(-1 / 8), (5 / 24), (5 / 24), (1 / 8), (1 / 8), (1 / 24), (1 / 24), (1 / 24), (1 / 24), (1 / 8), (1 / 24), (1 / 24), (-1 / 24), (1 / 24), (1 / 24), (1 / 24);
     (1 / 24), (1 / 24), (1 / 24), (-1 / 24), (-1 / 24), (5 / 24), (-1 / 8), (1 / 24), (-1 / 8), (-1 / 24), (1 / 24), (1 / 24), (-1 / 24), (-1 / 8), (-1 / 8), (5 / 24);
     (-1 / 12), (1 / 6), (1 / 12), (-1 / 12), (1 / 6), (-1 / 6), 0, (1 / 12), 0, 0, (-1 / 12), (-1 / 12), 0, (1 / 6), (-1 / 12), (-1 / 12);
     (1 / 12), 0, (-1 / 12), 0, (-1 / 6), (-1 / 6), (1 / 6), (1 / 12), (1 / 12), (-1 / 12), (-1 / 12), 0, (1 / 6), (-1 / 12), (1 / 12), 0;
     0, (1 / 12), (1 / 12), 0, (-1 / 12), (1 / 12), (1 / 12), (-1 / 12), (-1 / 12), (-1 / 12), (-1 / 12), (1 / 12), (-1 / 12), 0, (1 / 12), 0;
     (1 / 12), 0, (1 / 6), 0, 0, 0, (-1 / 6), (-1 / 6), (1 / 12), (1 / 12), (1 / 6), (-1 / 12), 0, 0, 0, (-1 / 6);
     (-7 / 24), (3 / 8), (-1 / 24), (5 / 24), (-1 / 24), (-1 / 8), (5 / 24), (1 / 8), (-1 / 24), (-1 / 8), (-5 / 24), (1 / 24), (-5 / 24), (1 / 24), (-5 / 24), (7 / 24);
     (-5 / 24), (7 / 24), (1 / 24), (-1 / 24), (5 / 24), (-1 / 24), (1 / 8), (1 / 24), (-1 / 8), (-1 / 24), (1 / 24), (-5 / 24), (-7 / 24), (1 / 8), (-1 / 8), (5 / 24);
     (5 / 24), (-1 / 8), (-1 / 8), (1 / 24), (-1 / 24), (1 / 24), (-1 / 8), (1 / 24), (-1 / 24), (-1 / 24), (1 / 24), (5 / 24), (1 / 24), (-5 / 24), (1 / 8), (-1 / 24);
     (1 / 3), (-1 / 4), (-1 / 6), (-1 / 6), (-1 / 12), (1 / 12), (-1 / 12), 0, (1 / 12), (1 / 12), (1 / 6), 0, (1 / 12), (1 / 12), 0, (-1 / 6);
     (7 / 24), (-5 / 24), (-1 / 8), (-1 / 8), (1 / 24), (1 / 8), (-5 / 24), (-1 / 8), (1 / 8), (-1 / 24), (1 / 24), (-1 / 24), (1 / 8), (1 / 24), (1 / 8), (-1 / 24);
     (1 / 6), (-1 / 12), (-1 / 12), (1 / 12), (-1 / 12), (-1 / 12), (1 / 12), (-1 / 12), 0, (1 / 6), (-1 / 12), 0, (1 / 4), (-1 / 12), (1 / 12), (-1 / 4);
     (1 / 3), (-1 / 3), 0, (-1 / 6), 0, 0, (-1 / 6), (-1 / 6), (1 / 6), (1 / 6), 0, (1 / 6), (1 / 6), (-1 / 6), (1 / 6), (-1 / 6);
     (-5 / 24), (5 / 24), (1 / 24), (1 / 8), (1 / 8), (1 / 24), (5 / 24), (5 / 24), (-1 / 24), (-5 / 24), (-1 / 8), (-1 / 8), (-7 / 24), (1 / 24), (-5 / 24), (5 / 24);
     (1 / 4), (-1 / 4), 0, 0, (-1 / 12), (-1 / 12), (-1 / 12), 0, 0, (1 / 6), 0, (-1 / 12), (1 / 12), (1 / 12), (1 / 6), (-1 / 6);
     (1 / 8), (-1 / 8), (-1 / 24), (1 / 24), (-1 / 24), (1 / 24), (1 / 24), (-1 / 24), (-1 / 8), (-1 / 8), (1 / 8), (1 / 24), (1 / 24), (1 / 24), (-1 / 8), (1 / 8);
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def base24TerminalInverse : Matrix (Fin 24) (Fin 8) ℚ :=
  !![0, 0, 1, (1 / 2), 1, (1 / 2), (1 / 2), (1 / 2);
     0, 0, -1, (1 / 2), 1, (-1 / 2), (1 / 2), (-1 / 2);
     1, 0, 1, 0, 0, 1, 0, 0;
     0, 1, 0, (-1 / 2), -1, (-1 / 2), (-1 / 2), (1 / 2);
     0, 0, 0, (1 / 2), 0, (-1 / 2), (1 / 2), (1 / 2);
     -1, -1, 0, 0, 0, 1, 0, 0;
     2, 2, 1, (3 / 2), 1, (-1 / 2), (1 / 2), (1 / 2);
     2, 0, 1, (3 / 2), 1, (1 / 2), (1 / 2), (-1 / 2);
     -1, 0, -1, -1, 0, -1, 0, 0;
     -1, -1, -1, -1, -1, 0, -1, -1;
     -1, -1, -1, -1, -1, 0, 0, -1;
     -1, 0, 0, -1, -1, 0, -1, 1;
     -2, -1, -1, -2, -1, 0, 0, 0;
     2, 1, 1, (3 / 2), 1, (-1 / 2), (1 / 2), (-1 / 2);
     -1, -1, 0, -1, -1, 0, -1, 0;
     0, 0, -1, (1 / 2), 0, (-1 / 2), (-1 / 2), (-1 / 2);
     1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 1]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem base24_terminal_reconstruction_certificate :
    base24TerminalLeft * base24RationalFrame +
      base24TerminalInverse * informationSelector base24FreeCoordinates =
        (1 : Matrix (Fin 24) (Fin 24) ℚ) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem base24_terminal_no_sign_seed : ∀ b : Fin 8 → Bool,
    ¬ IsCubeVector (base24TerminalInverse.mulVec (fun j => if b j then 1 else -1)) := by
  unfold IsCubeVector
  decide +kernel

theorem base24RationalFrame_cast : base24RationalFrame.map (rationalRealCast) = base24Frame := by
  ext i j
  simp [base24RationalFrame, base24Frame, encodedRealFrame, Matrix.map_apply]

theorem base24Frame_noSignExtension : NoSignExtension base24Frame := by
  rintro ⟨x, hx, horth⟩
  have hzero : (base24RationalFrame.map (rationalRealCast)).mulVec x = 0 := by
    rw [base24RationalFrame_cast]
    funext i
    exact horth i
  have hrec := rational_reconstruction_complete base24RationalFrame base24TerminalLeft
    base24TerminalInverse base24FreeCoordinates base24_terminal_reconstruction_certificate x hzero
  obtain ⟨b, hb⟩ := rational_seed_has_signs base24TerminalInverse base24FreeCoordinates x hx hrec
  exact base24_terminal_no_sign_seed b hb

theorem base24_tensor_partialHadamard {τ : Type*} [Fintype τ] [DecidableEq τ]
    (H : Matrix τ τ ℝ) (hH : IsHadamard H) : IsPartialHadamard (tensorFrame base24Frame H) :=
  tensorFrame_partialHadamard base24Frame H base24Frame_partialHadamard hH

theorem base24_tensor_noSignExtension {τ : Type*} [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (H : Matrix τ τ ℝ) (hH : IsHadamard H) : NoSignExtension (tensorFrame base24Frame H) :=
  tensor_noSignExtension base24Frame H hH base24Frame_noSignExtension

theorem base24_tensor_exchangeCost_le_three {τ : Type*}
    [Fintype τ] [DecidableEq τ] [Nonempty τ] (H : Matrix τ τ ℝ) (hH : IsHadamard H) :
    exchangeCost (tensorFrame base24Frame H) ≤ (3 : WithTop ℕ) :=
  (tensor_exchangeCost_le base24Frame H hH).trans base24_exchangeCost_le_three

end CompletionTheory
