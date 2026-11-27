/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module

public import CompletionTheory.TensorExchange

/-! # Exact bit-mask encoding and real lifting of integer sign-frame certificates -/

@[expose] public section
namespace CompletionTheory

def encodedSign (m j : ℕ) : ℤ := if m.testBit j then -1 else 1

def encodedIntFrame {r n : ℕ} (masks : Fin r → ℕ) : Matrix (Fin r) (Fin n) ℤ :=
  fun i j => encodedSign (masks i) j.val

def encodedRealFrame {r n : ℕ} (masks : Fin r → ℕ) : Matrix (Fin r) (Fin n) ℝ :=
  (encodedIntFrame masks).map (Int.castRingHom ℝ)

theorem encodedRealFrame_sign {r n : ℕ} (masks : Fin r → ℕ) :
    IsSignMatrix (encodedRealFrame masks : Matrix (Fin r) (Fin n) ℝ) := by
  intro i j
  change (encodedSign (masks i) j.val : ℝ) = 1 ∨ (encodedSign (masks i) j.val : ℝ) = -1
  unfold encodedSign
  split <;> norm_num

theorem encodedRealFrame_partialHadamard {r n : ℕ} (masks : Fin r → ℕ)
    (hgram : (encodedIntFrame masks : Matrix (Fin r) (Fin n) ℤ) *
      (encodedIntFrame masks).transpose = (n : ℤ) • (1 : Matrix (Fin r) (Fin r) ℤ)) :
    IsPartialHadamard (encodedRealFrame masks : Matrix (Fin r) (Fin n) ℝ) := by
  refine ⟨encodedRealFrame_sign masks, ?_⟩
  ext i j
  have hg := congrArg (fun M => M i j) hgram
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul] at hg
  change (∑ k : Fin n, (encodedIntFrame masks i k : ℝ) * (encodedIntFrame masks j k : ℝ)) =
    (Fintype.card (Fin n) : ℝ) * (if i = j then 1 else 0)
  simp only [Fintype.card_fin]
  exact_mod_cast hg

end CompletionTheory
