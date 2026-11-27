/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCyclicExistence.IntegralGramDeterminant
public import CompletionCyclicExistence.UnitAdaptedBasis
public import CompletionCyclicExistence.OrthogonalUnitSplitting
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
@[expose] public section
namespace CompletionTheory.ThreeSquares
open Module

 theorem integral_gram_determinant_reindex {M ι κ : Type*} [AddCommGroup M]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (b : Basis ι ℤ M) (e : ι ≃ κ) (B : LinearMap.BilinForm ℤ M) :
    (LinearMap.BilinForm.toMatrix (b.reindex e) B).det=
      (LinearMap.BilinForm.toMatrix b B).det := by
  have he : LinearMap.BilinForm.toMatrix (b.reindex e) B=
      Matrix.reindex e e (LinearMap.BilinForm.toMatrix b B) := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply,Matrix.reindex_apply]
  rw [he,Matrix.det_reindex_self]

 theorem unit_kernel_unimodular (n : ℕ) (B : LinearMap.BilinForm ℤ (Fin n → ℤ))
    (v : Fin n → ℤ) (hv : B v v=1) (hs : ∀ x y,B x y=B y x)
    (hdet : (LinearMap.BilinForm.toMatrix (Pi.basisFun ℤ (Fin n)) B).det=1) :
    ∃ k : Basis (Fin (n-1)) ℤ (LinearMap.ker (B v)),
      Matrix.det (fun i j => B (k i : Fin n → ℤ) (k j : Fin n → ℤ))=1 := by
  classical
  obtain ⟨k⟩ := unit_kernel_basis n (B v) v hv
  let b := unitAdaptedBasis (B v) v hv k
  have hn := unit_kernel_rank n (B v) v hv
  have hc : Fintype.card (Fin n)=Fintype.card (Unit ⊕ Fin (n-1)) := by
    simp only [Fintype.card_fin,Fintype.card_sum,Fintype.card_unit]
    omega
  let e := Fintype.equivOfCardEq hc
  let c := (Pi.basisFun ℤ (Fin n)).reindex e
  have hcDet : (LinearMap.BilinForm.toMatrix c B).det=1 := by
    rw [integral_gram_determinant_reindex]
    exact hdet
  have hbDet : (LinearMap.BilinForm.toMatrix b B).det=1 :=
    (integral_gram_determinant_basis_invariant b c B).trans hcDet
  let K : Matrix (Fin (n-1)) (Fin (n-1)) ℤ := fun i j => B (k i) (k j)
  have hblock : LinearMap.BilinForm.toMatrix b B=
      Matrix.fromBlocks (1:Matrix Unit Unit ℤ) 0 0 K := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · cases i
      cases j
      simp [b,LinearMap.BilinForm.toMatrix_apply,unit_adapted_basis_first,hv,Matrix.fromBlocks_apply₁₁]
    · simp only [LinearMap.BilinForm.toMatrix_apply,Matrix.fromBlocks_apply₁₂,
        Matrix.zero_apply]
      rw [show b (Sum.inl i)=v by cases i;exact unit_adapted_basis_first _ _ _ _,
        show b (Sum.inr j)=(k j:Fin n → ℤ) from unit_adapted_basis_kernel _ _ _ _ j]
      exact (k j).property
    · simp only [LinearMap.BilinForm.toMatrix_apply,Matrix.fromBlocks_apply₂₁,
        Matrix.zero_apply]
      rw [show b (Sum.inl j)=v by cases j;exact unit_adapted_basis_first _ _ _ _,
        show b (Sum.inr i)=(k i:Fin n → ℤ) from unit_adapted_basis_kernel _ _ _ _ i,hs]
      exact (k i).property
    · rw [LinearMap.BilinForm.toMatrix_apply,Matrix.fromBlocks_apply₂₂]
      rw [show b (Sum.inr i)=(k i:Fin n → ℤ) from unit_adapted_basis_kernel _ _ _ _ i,
        show b (Sum.inr j)=(k j:Fin n → ℤ) from unit_adapted_basis_kernel _ _ _ _ j]
  refine ⟨k,?_⟩
  rw [hblock,Matrix.det_fromBlocks_zero₂₁,Matrix.det_one,one_mul] at hbDet
  exact hbDet

end CompletionTheory.ThreeSquares
