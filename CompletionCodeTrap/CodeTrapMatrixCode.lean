/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.ModularCodeParity
public import Mathlib.LinearAlgebra.Dimension.Finrank
@[expose] public section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory
open Module

noncomputable def trapMatrixCode {K : Type*} [Field K] {r N : ℕ}
    (B : Matrix (Fin r) (Fin N) K) : Submodule K (Fin N → K) :=
  LinearMap.range (Matrix.toLin' B.transpose)

theorem trapMatrixCode_finrank {K : Type*} [Field K] {r N : ℕ}
    (B : Matrix (Fin r) (Fin N) K) (S : Matrix (Fin r) (Fin N) K)
    (hleft : S*B.transpose=1) : Module.finrank K (trapMatrixCode B)=r := by
  have hl : Function.LeftInverse (Matrix.toLin' S) (Matrix.toLin' B.transpose) := by
    intro x
    rw [← Matrix.toLin'_mul_apply,hleft]
    simp
  have hi := hl.injective
  unfold trapMatrixCode
  rw [LinearMap.finrank_range_of_inj hi]
  simp

theorem trapMatrixCode_self_orthogonal {K : Type*} [Field K] {r N : ℕ}
    (B : Matrix (Fin r) (Fin N) K) (hgram : B*B.transpose=0) :
    trapMatrixCode B≤(coordinateDotForm K N).orthogonal (trapMatrixCode B) := by
  rintro x ⟨u,rfl⟩ y ⟨v,rfl⟩
  change dotProduct (B.transpose.mulVec v) (B.transpose.mulVec u)=0
  rw [Matrix.dotProduct_transpose_mulVec,Matrix.mulVec_mulVec,hgram,Matrix.zero_mulVec,dotProduct_zero]

theorem trapMatrixCode_self_dual {K : Type*} [Field K] {r N : ℕ}
    (B : Matrix (Fin r) (Fin N) K) (S : Matrix (Fin r) (Fin N) K)
    (hleft : S*B.transpose=1) (hgram : B*B.transpose=0) (hhalf : 2*r=N) :
    trapMatrixCode B=(coordinateDotForm K N).orthogonal (trapMatrixCode B) := by
  have hr := trapMatrixCode_finrank B S hleft
  have ha : Module.finrank K (Fin N → K)=N := by simp
  have hd : Module.finrank K ((coordinateDotForm K N).orthogonal (trapMatrixCode B))=r := by
    rw [(coordinateDotForm K N).finrank_orthogonal (coordinateDotForm_nondegenerate K N),ha,hr]
    omega
  apply Submodule.eq_of_le_of_finrank_le (trapMatrixCode_self_orthogonal B hgram)
  rw [hd,hr]

theorem trapMatrixCode_row_mem {K : Type*} [Field K] {r N : ℕ}
    (B : Matrix (Fin r) (Fin N) K) (i : Fin r) : B i∈trapMatrixCode B := by
  refine ⟨Pi.single i 1,?_⟩
  funext j
  simp [Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Pi.single_apply,mul_ite]

theorem trapMatrixCode_le_of_rows {K : Type*} [Field K] {r N : ℕ}
    (B : Matrix (Fin r) (Fin N) K) (D : Submodule K (Fin N → K))
    (hrows : ∀ i,B i∈D) : trapMatrixCode B≤D := by
  rintro x ⟨u,rfl⟩
  change B.transpose.mulVec u∈D
  have he : B.transpose.mulVec u=∑ i,u i • B i := by
    funext j
    simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    exact Finset.sum_congr rfl (fun i hi => mul_comm _ _)
  rw [he]
  exact D.sum_mem (fun i hi => D.smul_mem (u i) (hrows i))

theorem trapMatrixCode_eq_span_rows {K : Type*} [Field K] {r N : ℕ}
    (B : Matrix (Fin r) (Fin N) K) :
    trapMatrixCode B=Submodule.span K (Set.range B) := by
  apply le_antisymm
  · exact trapMatrixCode_le_of_rows B _ (fun i => Submodule.subset_span ⟨i,rfl⟩)
  · exact Submodule.span_le.mpr (fun x ⟨i,hi⟩ => hi ▸ trapMatrixCode_row_mem B i)

theorem trapMatrixCode_mul_le {K : Type*} [Field K] {a b N : ℕ}
    (A : Matrix (Fin a) (Fin N) K) (T : Matrix (Fin b) (Fin a) K) :
    trapMatrixCode (T*A)≤trapMatrixCode A := by
  rintro x ⟨u,rfl⟩
  refine ⟨T.transpose.mulVec u,?_⟩
  change A.transpose.mulVec (T.transpose.mulVec u)=(T*A).transpose.mulVec u
  rw [Matrix.mulVec_mulVec,Matrix.transpose_mul]
end CompletionTheory
