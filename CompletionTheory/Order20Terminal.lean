/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.RationalSignCertificates
public import CompletionTheory.EncodedFrames
@[expose] public section
namespace CompletionTheory

def codeTrap20Masks : Fin 12 → ℕ := ![0, 965904, 1003736, 902980, 730036, 501868, 412530, 210762, 649754, 358790, 694982, 250934]

def codeTrap20RationalFrame : Matrix (Fin 12) (Fin 20) ℚ :=
  (encodedIntFrame codeTrap20Masks).map (Int.castRingHom ℚ)

def codeTrap20Frame : Matrix (Fin 12) (Fin 20) ℝ := encodedRealFrame codeTrap20Masks

def codeTrap20Free : Fin 8 → Fin 20 := ![12, 13, 14, 15, 16, 17, 18, 19]

def codeTrap20Left : Matrix (Fin 20) (Fin 12) ℚ :=
  !![0, (3 / 10), 0, (-3 / 10), (3 / 10), (1 / 5), (-1 / 10), (2 / 5), (-1 / 10), (-1 / 10), (3 / 10), (1 / 10);
     (1 / 20), (11 / 60), (-1 / 60), (1 / 60), (3 / 20), (7 / 60), (-7 / 60), (-1 / 20), (-1 / 20), (-11 / 60), (1 / 20), (-3 / 20);
     (1 / 5), (7 / 30), (-1 / 15), (-13 / 30), (1 / 10), (-1 / 30), (1 / 30), (3 / 10), (-1 / 5), (-7 / 30), (1 / 5), (-1 / 10);
     (3 / 20), (1 / 20), (-1 / 20), (1 / 20), (-1 / 20), (-3 / 20), (3 / 20), (-3 / 20), (-3 / 20), (-1 / 20), (3 / 20), (1 / 20);
     (1 / 5), (1 / 15), (-7 / 30), (-4 / 15), (1 / 10), (2 / 15), (-2 / 15), (3 / 10), (-1 / 5), (-1 / 15), (1 / 5), (-1 / 10);
     (-1 / 20), (-7 / 60), (11 / 60), (5 / 12), (-1 / 4), (-11 / 60), (-1 / 60), (-1 / 4), (1 / 4), (13 / 60), (-3 / 20), (-1 / 20);
     (1 / 10), (1 / 10), (-1 / 5), (-1 / 5), (1 / 5), 0, (-1 / 5), (1 / 10), (1 / 10), 0, 0, 0;
     (1 / 20), (-13 / 60), (-1 / 60), (5 / 12), (-1 / 4), (1 / 60), (11 / 60), (-1 / 4), (1 / 4), (7 / 60), (-7 / 20), (1 / 20);
     (1 / 10), (1 / 15), (-1 / 30), (-1 / 6), 0, (1 / 30), (-2 / 15), 0, 0, (-4 / 15), (3 / 10), (1 / 10);
     0, (-1 / 30), (1 / 6), (1 / 30), (-1 / 5), (1 / 30), (1 / 15), (-1 / 10), (-1 / 10), (7 / 30), (-1 / 5), (1 / 10);
     (1 / 10), (-11 / 30), (2 / 15), (4 / 15), (-1 / 10), (-1 / 30), (7 / 30), (-3 / 10), (1 / 5), (4 / 15), (-3 / 10), (-1 / 10);
     (1 / 10), (-4 / 15), (2 / 15), (1 / 6), 0, (-2 / 15), (1 / 30), 0, 0, (1 / 15), (-1 / 5), (1 / 10);
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def codeTrap20Inverse : Matrix (Fin 20) (Fin 8) ℚ :=
  !![1, 1, -2, 0, 0, 2, -1, 0;
     (-1 / 3), (1 / 3), -1, (1 / 3), (-1 / 3), (1 / 3), 0, (2 / 3);
     (2 / 3), (1 / 3), -2, (-2 / 3), (-4 / 3), (4 / 3), -1, (-1 / 3);
     0, -1, 0, 0, -1, 0, 0, 0;
     (1 / 3), (2 / 3), -2, (-1 / 3), (-2 / 3), (2 / 3), -1, (-2 / 3);
     (-1 / 3), (-2 / 3), 2, (1 / 3), (2 / 3), (-5 / 3), 1, (2 / 3);
     0, 1, -1, 0, 0, 0, -1, 0;
     (-4 / 3), (-2 / 3), 2, (1 / 3), (2 / 3), (-5 / 3), 1, (-1 / 3);
     (1 / 3), (-1 / 3), -1, (2 / 3), (-2 / 3), (2 / 3), -1, (1 / 3);
     (1 / 3), (-1 / 3), 1, (-1 / 3), (1 / 3), (-1 / 3), 1, (-2 / 3);
     (-4 / 3), (-2 / 3), 2, (-2 / 3), (2 / 3), (-5 / 3), 1, (-1 / 3);
     (-1 / 3), (-2 / 3), 1, (-2 / 3), (2 / 3), (-2 / 3), 0, (-1 / 3);
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
theorem codeTrap20_certificate :
    codeTrap20Left * codeTrap20RationalFrame +
      codeTrap20Inverse * informationSelector codeTrap20Free = 1 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem codeTrap20_no_sign_seed : ∀ b : Fin 8 → Bool,
    ¬ IsCubeVector (codeTrap20Inverse.mulVec (fun j => if b j then 1 else -1)) := by
  unfold IsCubeVector
  decide +kernel

set_option maxRecDepth 20000 in
theorem codeTrap20_int_gram :
    encodedIntFrame (n := 20) codeTrap20Masks * (encodedIntFrame codeTrap20Masks).transpose =
      (20 : ℤ) • (1 : Matrix (Fin 12) (Fin 12) ℤ) := by decide +kernel

theorem codeTrap20_partialHadamard : IsPartialHadamard codeTrap20Frame :=
  encodedRealFrame_partialHadamard codeTrap20Masks codeTrap20_int_gram

theorem codeTrap20RationalFrame_cast :
    codeTrap20RationalFrame.map rationalRealCast = codeTrap20Frame := by
  ext i j
  simp [codeTrap20RationalFrame, codeTrap20Frame, encodedRealFrame, Matrix.map_apply]

theorem codeTrap20_noSignExtension : NoSignExtension codeTrap20Frame := by
  rintro ⟨x, hx, horth⟩
  have hzero : (codeTrap20RationalFrame.map rationalRealCast).mulVec x = 0 := by
    rw [codeTrap20RationalFrame_cast]
    funext i
    exact horth i
  have hrec := rational_reconstruction_complete codeTrap20RationalFrame codeTrap20Left
    codeTrap20Inverse codeTrap20Free codeTrap20_certificate x hzero
  obtain ⟨b, hb⟩ := rational_seed_has_signs codeTrap20Inverse codeTrap20Free x hx hrec
  exact codeTrap20_no_sign_seed b hb

theorem codeTrap20_tensor_partialHadamard {τ : Type*} [Fintype τ] [DecidableEq τ]
    (H : Matrix τ τ ℝ) (hH : IsHadamard H) : IsPartialHadamard (tensorFrame codeTrap20Frame H) :=
  tensorFrame_partialHadamard codeTrap20Frame H codeTrap20_partialHadamard hH

theorem codeTrap20_tensor_noSignExtension {τ : Type*} [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (H : Matrix τ τ ℝ) (hH : IsHadamard H) : NoSignExtension (tensorFrame codeTrap20Frame H) :=
  tensor_noSignExtension codeTrap20Frame H hH codeTrap20_noSignExtension

end CompletionTheory
