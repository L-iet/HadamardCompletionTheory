/- Copyright (c) 2026 Joshua Mark. Apache-2.0. -/
module
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory.Bloch
open Matrix

/-- Extend any complex scaled orthonormal row family by exactly the missing rows. -/
theorem complex_frame_extension {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (W : Matrix ι (κ ⊕ ι) ℂ)
    (hW : W * W.conjTranspose = (Fintype.card (κ ⊕ ι) : ℂ) • 1) :
    ∃ H : Matrix (κ ⊕ ι) (κ ⊕ ι) ℂ,
      H * H.conjTranspose = (Fintype.card (κ ⊕ ι) : ℂ) • 1 ∧
      H.conjTranspose * H = (Fintype.card (κ ⊕ ι) : ℂ) • 1 ∧
      ∀ i j, H (Sum.inr i) j = W i j := by
  classical
  let N : ℝ := Fintype.card (κ ⊕ ι)
  have hN : 0 < N := by
    change (0 : ℝ) < (Fintype.card (κ ⊕ ι) : ℝ)
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (κ ⊕ ι))
  have hs : Real.sqrt N ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hN)
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (le_of_lt hN)
  have hsC : (Real.sqrt N : ℂ)≠0 := by exact_mod_cast hs
  have hsqC : (Real.sqrt N : ℂ)*(Real.sqrt N : ℂ)=(N : ℂ) := by exact_mod_cast hsq
  have hNc : (Fintype.card (κ ⊕ ι):ℂ)=(N:ℂ) := by simp [N]
  let v : κ ⊕ ι → EuclideanSpace ℂ (κ ⊕ ι) :=
    fun i => WithLp.toLp 2 (fun j => Sum.elim (fun _ => 0) (fun k => W k j / (Real.sqrt N : ℂ)) i)
  let s : Set (κ ⊕ ι) := Set.range Sum.inr
  have hv : Orthonormal ℂ (s.domRestrict v) := by
    dsimp only [s]
    rw [orthonormal_iff_ite]
    intro i j
    rcases i with ⟨i, ⟨a, rfl⟩⟩
    rcases j with ⟨j, ⟨b, rfl⟩⟩
    have hg := congrArg (fun M => M b a) hW
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul] at hg
    change (∑ k,(W b k/(Real.sqrt N:ℂ))*star (W a k/(Real.sqrt N:ℂ)))=_
    have hc : star (Real.sqrt N:ℂ)=(Real.sqrt N:ℂ) := by simp [Complex.star_def]
    have ht (k : κ ⊕ ι) : (W b k/(Real.sqrt N:ℂ))*star (W a k/(Real.sqrt N:ℂ))=
        (W b k*star (W a k))/((Real.sqrt N:ℂ)*(Real.sqrt N:ℂ)) := by
      rw [star_div₀,hc,div_mul_div_comm]
    simp_rw [ht]
    rw [←Finset.sum_div,hsqC,hg]
    split_ifs with hba heq heq2
    · simpa only [mul_one,hNc] using (div_self (show (N : ℂ)≠0 by exact_mod_cast hN.ne'))
    · exfalso
      apply heq
      subst b
      rfl
    · exfalso
      apply hba
      exact (Sum.inr.inj (congrArg Subtype.val heq2)).symm
    · simp
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp [finrank_euclideanSpace])

  let U : Matrix (κ ⊕ ι) (κ ⊕ ι) ℂ := fun i j => b i j
  have hU : U * U.conjTranspose = 1 := by
    ext i j
    change (∑ k, b i k * star (b j k)) = if i = j then 1 else 0
    have h := b.inner_eq_ite j i
    simpa only [PiLp.inner_apply, RCLike.inner_apply, Complex.star_def, eq_comm] using h
  have hUc : U.conjTranspose * U = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hU
  let H : Matrix (κ ⊕ ι) (κ ⊕ ι) ℂ := (Real.sqrt N : ℂ) • U
  have hH : H * H.conjTranspose = (N : ℂ) • 1 := by
    simp [H, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, hU,
      smul_smul, Complex.conj_ofReal, hsqC, hsq]
  have hHc : H.conjTranspose * H = (N : ℂ) • 1 := by
    simp [H, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, hUc,
      smul_smul, Complex.conj_ofReal, hsqC, hsq]
  have hret : ∀ i j, H (Sum.inr i) j = W i j := by
    intro i j
    have he := congrArg (fun x : EuclideanSpace ℂ (κ ⊕ ι) => x j)
      (hb (Sum.inr i) ⟨i, rfl⟩)
    change b (Sum.inr i) j = W i j / (Real.sqrt N : ℂ) at he
    change (Real.sqrt N : ℂ) * b (Sum.inr i) j = W i j
    rw [he]
    field_simp
  exact ⟨H, hH, hHc, hret⟩
end CompletionTheory.Bloch
