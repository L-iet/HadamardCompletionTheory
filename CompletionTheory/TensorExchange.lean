/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module

public import CompletionTheory
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! # Augmenting exchanges and their exact cost under Hadamard tensoring -/

@[expose] public section
namespace CompletionTheory
open Matrix

def tensorFrame {ι κ τ : Type*} (P : Matrix ι κ ℝ) (H : Matrix τ τ ℝ) :
    Matrix (ι × τ) (κ × τ) ℝ := fun i j => P i.1 j.1 * H i.2 j.2

def fiberLift {ι κ τ : Type*} (P : Matrix ι κ ℝ) (h : τ → ℝ) : Matrix ι (κ × τ) ℝ :=
  fun i j => P i j.1 * h j.2

def HasAugmentingExchange {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (P : Matrix ι κ ℝ) (k : ℕ) : Prop :=
  ∃ D : Finset ι, D.card = k ∧ ∃ V : Matrix (Fin (k + 1)) κ ℝ,
    IsPartialHadamard V ∧ ∀ i, i ∉ D → ∀ a, ∑ j, P i j * V a j = 0

noncomputable def exchangeCost {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (P : Matrix ι κ ℝ) : WithTop ℕ :=
  ⨅ k : {k : ℕ // HasAugmentingExchange P k}, (k.val : WithTop ℕ)

def exchangeFrame {ι κ : Type*} [DecidableEq ι] (P : Matrix ι κ ℝ)
    (D : Finset ι) {k : ℕ} (V : Matrix (Fin (k + 1)) κ ℝ) :
    Matrix ({i : ι // i ∉ D} ⊕ Fin (k + 1)) κ ℝ :=
  Sum.elim (fun i => P i.val) V

theorem exchangeFrame_partialHadamard {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] (P : Matrix ι κ ℝ)
    (D : Finset ι) {k : ℕ} (V : Matrix (Fin (k + 1)) κ ℝ)
    (hP : IsPartialHadamard P) (hV : IsPartialHadamard V)
    (horth : ∀ i, i ∉ D → ∀ a, ∑ j, P i j * V a j = 0) :
    IsPartialHadamard (exchangeFrame P D V) := by
  constructor
  · intro i j
    cases i with
    | inl i => exact hP.1 i.val j
    | inr i => exact hV.1 i j
  · ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        change (∑ x, P i.val x * P j.val x) = _
        have h := congrArg (fun M => M i.val j.val) hP.2
        simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
          exchangeFrame, Sum.elim_inl, Sum.elim_inr, Subtype.ext_iff] using h
      | inr j =>
        change (∑ x, P i.val x * V j x) = _
        simpa using horth i.val i.property j
    | inr i =>
      cases j with
      | inl j =>
        change (∑ x, V i x * P j.val x) = _
        simpa [mul_comm] using horth j.val j.property i
      | inr j =>
        change (∑ x, V i x * V j x) = _
        have h := congrArg (fun M => M i j) hV.2
        simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
          exchangeFrame, Sum.elim_inl, Sum.elim_inr] using h

theorem tensor_row_dot {κ τ : Type*} [Fintype κ] [Fintype τ]
    (u v : κ → ℝ) (h g : τ → ℝ) :
    (∑ j : κ × τ, (u j.1 * h j.2) * (v j.1 * g j.2)) =
      (∑ j, u j * v j) * ∑ b, h b * g b := by
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ j, ∑ b, (u j * v j) * (h b * g b) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul]

theorem tensorFrame_partialHadamard {ι κ τ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype τ] [DecidableEq τ]
    (P : Matrix ι κ ℝ) (H : Matrix τ τ ℝ)
    (hP : IsPartialHadamard P) (hH : IsHadamard H) :
    IsPartialHadamard (tensorFrame P H) := by
  constructor
  · intro i j
    rcases hP.1 i.1 j.1 with hp | hp <;> rcases hH.1 i.2 j.2 with hh | hh <;>
      simp [tensorFrame, hp, hh, IsSign]
  · ext u v
    rcases u with ⟨i, a⟩
    rcases v with ⟨j, b⟩
    have hp := congrArg (fun M => M i j) hP.2
    have hh := congrArg (fun M => M a b) hH.2
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul] at hp hh ⊢
    change (∑ x : κ × τ, (P i x.1 * H a x.2) * (P j x.1 * H b x.2)) = _
    rw [tensor_row_dot, hp, hh]
    by_cases hij : i = j <;> by_cases hab : a = b <;>
      simp [hij, hab, Fintype.card_prod, Nat.cast_mul]

theorem fiberLift_partialHadamard {ι κ τ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype τ] [DecidableEq τ]
    (P : Matrix ι κ ℝ) (H : Matrix τ τ ℝ)
    (hP : IsPartialHadamard P) (hH : IsHadamard H) (a : τ) :
    IsPartialHadamard (fiberLift P (H a)) := by
  constructor
  · intro i j
    rcases hP.1 i j.1 with hp | hp <;> rcases hH.1 a j.2 with hh | hh <;>
      simp [fiberLift, hp, hh, IsSign]
  · ext i j
    have hp := congrArg (fun M => M i j) hP.2
    have hh := congrArg (fun M => M a a) hH.2
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, ite_true, mul_one] at hp hh ⊢
    change (∑ x : κ × τ, (P i x.1 * H a x.2) * (P j x.1 * H a x.2)) = _
    rw [tensor_row_dot, hp, hh]
    by_cases hij : i = j <;> simp [hij, Fintype.card_prod, Nat.cast_mul]

theorem tensor_augmenting_exchange {ι κ τ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype τ] [DecidableEq τ]
    (P : Matrix ι κ ℝ) (H : Matrix τ τ ℝ) (hH : IsHadamard H) (a : τ)
    (k : ℕ) (hex : HasAugmentingExchange P k) :
    HasAugmentingExchange (tensorFrame P H) k := by
  classical
  obtain ⟨D, hD, V, hV, horth⟩ := hex
  let E := D.image (fun i => (i, a))
  refine ⟨E, ?_, fiberLift V (H a), fiberLift_partialHadamard V H hV hH a, ?_⟩
  · rw [Finset.card_image_of_injective D (fun i j h => Prod.mk.inj h |>.1), hD]
  · intro x hx b
    rcases x with ⟨i, c⟩
    change (∑ j : κ × τ, (P i j.1 * H c j.2) * (V b j.1 * H a j.2)) = 0
    rw [tensor_row_dot]
    by_cases hca : c = a
    · subst c
      have hi : i ∉ D := by
        intro hi
        exact hx (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      rw [horth i hi b, zero_mul]
    · have hh := congrArg (fun M => M c a) hH.2
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul, ite_eq_right hca, mul_zero] at hh
      rw [hh, mul_zero]

theorem exchangeCost_eq_minimum {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (P : Matrix ι κ ℝ) [DecidablePred (HasAugmentingExchange P)]
    (h : ∃ k, HasAugmentingExchange P k) :
    exchangeCost P = (Nat.find h : WithTop ℕ) := by
  classical
  apply le_antisymm
  · exact iInf_le_of_le ⟨Nat.find h, Nat.find_spec h⟩ le_rfl
  · apply le_iInf
    intro k
    exact_mod_cast Nat.find_min' h k.property

theorem exchangeCost_eq_top {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (P : Matrix ι κ ℝ) (h : ¬ ∃ k, HasAugmentingExchange P k) : exchangeCost P = ⊤ := by
  let : IsEmpty {k : ℕ // HasAugmentingExchange P k} := ⟨fun k => h ⟨k.val, k.property⟩⟩
  simp [exchangeCost]

theorem exchangeCost_le_iff {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (P : Matrix ι κ ℝ) (b : ℕ) :
    exchangeCost P ≤ (b : WithTop ℕ) ↔ ∃ k ≤ b, HasAugmentingExchange P k := by
  classical
  constructor
  · intro hb
    by_cases hex : ∃ k, HasAugmentingExchange P k
    · rw [exchangeCost_eq_minimum P hex] at hb
      exact ⟨Nat.find hex, by exact_mod_cast hb, Nat.find_spec hex⟩
    · rw [exchangeCost_eq_top P hex] at hb
      simp at hb
  · rintro ⟨k, hk, h⟩
    exact (iInf_le_of_le ⟨k, h⟩ le_rfl).trans (by exact_mod_cast hk)

theorem tensor_exchangeCost_le {ι κ τ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (P : Matrix ι κ ℝ) (H : Matrix τ τ ℝ) (hH : IsHadamard H) :
    exchangeCost (tensorFrame P H) ≤ exchangeCost P := by
  classical
  apply le_iInf
  intro k
  exact iInf_le_of_le ⟨k.val, tensor_augmenting_exchange P H hH
    (Classical.arbitrary τ) k.val k.property⟩ le_rfl

def NoSignExtension {ι κ : Type*} [Fintype κ] (P : Matrix ι κ ℝ) : Prop :=
  ¬ ∃ f : κ → ℝ, (∀ j, IsSign (f j)) ∧ ∀ i, ∑ j, P i j * f j = 0

theorem tensor_noSignExtension {ι κ τ : Type*}
    [Fintype κ] [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (P : Matrix ι κ ℝ) (H : Matrix τ τ ℝ) (hH : IsHadamard H)
    (hP : NoSignExtension P) : NoSignExtension (tensorFrame P H) := by
  classical
  rintro ⟨f, hf, horth⟩
  have hn : (Fintype.card τ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  let M : Matrix τ τ ℝ := (Fintype.card τ : ℝ)⁻¹ • Hᵀ
  have hHM : H * M = 1 := by
    simp [M, hH.2, smul_smul, hn]
  have hMH : M * H = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hHM
  have hcolumn (i : ι) (b : τ) : (∑ j, P i j * f (j, b)) = 0 := by
    let v : τ → ℝ := fun b => ∑ j, P i j * f (j, b)
    have hv : H.mulVec v = 0 := by
      ext a
      change (∑ b, H a b * ∑ j, P i j * f (j, b)) = 0
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      calc
        _ = ∑ j, ∑ b, (P i j * H a b) * f (j, b) := by
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro b hb
          ring
        _ = 0 := by simpa only [tensorFrame, Fintype.sum_prod_type] using horth (i, a)
    have hv0 : v = 0 := by
      have hh := congrArg (fun y => M.mulVec y) hv
      simpa only [Matrix.mulVec_mulVec, hMH, Matrix.one_mulVec, Matrix.mulVec_zero] using hh
    exact congrFun hv0 b
  let b : τ := Classical.arbitrary τ
  exact hP ⟨fun j => f (j, b), fun j => hf (j, b), fun i => hcolumn i b⟩

end CompletionTheory
