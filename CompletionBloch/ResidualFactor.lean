/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionBloch.ComplexExtension
public import CompletionBloch.BlochAlgebra
public import Mathlib.Tactic.LinearCombination
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory.Bloch
noncomputable section
open scoped BigOperators ComplexConjugate

theorem complex_residual_factor {n : ℕ} (hn : 2≤n)
    (V : Matrix (Fin n) (Fin (n-2)) ℂ)
    (hgram : V.conjTranspose*V=(n:ℂ) • (1 : Matrix (Fin (n-2)) (Fin (n-2)) ℂ)) :
    ∃ R : Matrix (Fin n) (Fin 2) ℂ,
      R.conjTranspose*R=(n:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      R*R.conjTranspose=(n:ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)-V*V.conjTranspose := by
  classical
  have hcard : Fintype.card (Fin 2 ⊕ Fin (n-2))=n := by simp; omega
  let e : (Fin 2 ⊕ Fin (n-2)) ≃ Fin n := Fintype.equivOfCardEq (by simp; omega)
  let W : Matrix (Fin (n-2)) (Fin 2 ⊕ Fin (n-2)) ℂ := fun i j => star (V (e j) i)
  have hW : W*W.conjTranspose=(Fintype.card (Fin 2 ⊕ Fin (n-2)):ℂ) • 1 := by
    ext i j
    have hh := congrArg (fun M : Matrix (Fin (n-2)) (Fin (n-2)) ℂ => M i j) hgram
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul] at hh ⊢
    simp only [W,star_star]
    rw [Equiv.sum_comp e (fun k => star (V k i)*V k j),hcard]
    exact hh
  obtain ⟨H,hH,hHc,hret⟩ := complex_frame_extension W hW
  let R : Matrix (Fin n) (Fin 2) ℂ := fun i a => star (H (Sum.inl a) (e.symm i))
  have hRg : R.conjTranspose*R=(n:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext a b
    have hh := congrArg (fun M : Matrix (Fin 2 ⊕ Fin (n-2)) (Fin 2 ⊕ Fin (n-2)) ℂ =>
      M (Sum.inl a) (Sum.inl b)) hH
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.smul_apply,Matrix.one_apply,
      smul_eq_mul,Sum.inl.injEq,hcard] at hh ⊢
    simp only [R,star_star]
    rw [Equiv.sum_comp e.symm (fun k => H (Sum.inl a) k*star (H (Sum.inl b) k))]
    exact hh
  refine ⟨R,hRg,?_⟩
  ext i j
  have hh := congrArg (fun M : Matrix (Fin 2 ⊕ Fin (n-2)) (Fin 2 ⊕ Fin (n-2)) ℂ =>
    M (e.symm i) (e.symm j)) hHc
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.smul_apply,Matrix.one_apply,
    smul_eq_mul,Fintype.sum_sum_type,hcard] at hh
  simp_rw [hret,W,e.apply_symm_apply,star_star] at hh
  have he : (e.symm i=e.symm j) ↔ i=j := e.symm.injective.eq_iff
  simp only [he] at hh
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.sub_apply,Matrix.smul_apply,
    Matrix.one_apply,smul_eq_mul,R,star_star]
  linear_combination hh

theorem complex_residual_row_norm_two {n : ℕ} (hn : 2≤n)
    (V : Matrix (Fin n) (Fin (n-2)) ℂ) (R : Matrix (Fin n) (Fin 2) ℂ)
    (hflat : ∀ i j,Complex.normSq (V i j)=1)
    (hres : R*R.conjTranspose=(n:ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)-V*V.conjTranspose) :
    ∀ i,rowNormSq (R i)=2 := by
  intro i
  have hh := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i i) hres
  have hv : (V*V.conjTranspose) i i=((n-2:ℕ):ℂ) := by
    simp [Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.star_def,Complex.mul_conj,hflat]
  have hr : (R*R.conjTranspose) i i=(rowNormSq (R i):ℂ) := by
    simp [Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.star_def,Complex.mul_conj,
      Fin.sum_univ_succ,rowNormSq]
  rw [hr,Matrix.sub_apply,hv] at hh
  simp only [Matrix.smul_apply,Matrix.one_apply,ite_true,smul_eq_mul,mul_one] at hh
  have he : (rowNormSq (R i):ℂ)=2 := by
    rw [Nat.cast_sub (show 2≤n by omega)] at hh
    linear_combination hh
  exact_mod_cast he

end
end CompletionTheory.Bloch
