/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.InformationCoordinates
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Data.Matrix.Block
@[expose] public section
set_option maxHeartbeats 2000000
namespace CompletionTheory
open Matrix
open scoped ComplexConjugate

def IsFourthRoot (z : ℂ) : Prop := z=1 ∨ z= -1 ∨ z=Complex.I ∨ z= -Complex.I

noncomputable def realifiedMatrix {ι κ : Type*} (V : Matrix ι κ ℂ) : Matrix (ι⊕ι) (κ⊕κ) ℝ :=
  Matrix.fromBlocks (fun i j => (V i j).re) (fun i j => -(V i j).im)
    (fun i j => (V i j).im) (fun i j => (V i j).re)

noncomputable def packComplexVector {ι : Type*} (w : ι⊕ι → ℝ) : ι → ℂ :=
  fun i => (w (Sum.inl i) : ℂ)+Complex.I*(w (Sum.inr i) : ℂ)

noncomputable def unpackComplexVector {ι : Type*} (z : ι → ℂ) : ι⊕ι → ℝ :=
  Sum.elim (fun i => (z i).re) (fun i => (z i).im)

theorem pack_unpack_complex {ι : Type*} (z : ι → ℂ) : packComplexVector (unpackComplexVector z)=z := by
  funext i
  apply Complex.ext <;> simp [packComplexVector,unpackComplexVector]

theorem realified_transpose_mulVec_re {ι κ : Type*} [Fintype ι]
    (V : Matrix ι κ ℂ) (w : ι⊕ι → ℝ) (j : κ) :
    ((V.conjTranspose.mulVec (packComplexVector w)) j).re=
      ((realifiedMatrix V).transpose.mulVec w) (Sum.inl j) := by
  simp [Matrix.mulVec,dotProduct,realifiedMatrix,packComplexVector,Matrix.fromBlocks,Complex.mul_re,
    Complex.mul_im,Finset.sum_add_distrib]

theorem realified_transpose_mulVec_im {ι κ : Type*} [Fintype ι]
    (V : Matrix ι κ ℂ) (w : ι⊕ι → ℝ) (j : κ) :
    ((V.conjTranspose.mulVec (packComplexVector w)) j).im=
      ((realifiedMatrix V).transpose.mulVec w) (Sum.inr j) := by
  simp [Matrix.mulVec,dotProduct,realifiedMatrix,packComplexVector,Matrix.fromBlocks,Complex.mul_re,
    Complex.mul_im,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  ring

theorem realification_orthogonality_iff {ι κ : Type*} [Fintype ι]
    (V : Matrix ι κ ℂ) (w : ι⊕ι → ℝ) :
    (realifiedMatrix V).transpose.mulVec w=0 ↔ V.conjTranspose.mulVec (packComplexVector w)=0 := by
  constructor
  · intro h
    funext j
    apply Complex.ext
    · rw [realified_transpose_mulVec_re,h];rfl
    · rw [realified_transpose_mulVec_im,h];rfl
  · intro h
    funext j
    cases j with
    | inl j => rw [← realified_transpose_mulVec_re,h];rfl
    | inr j => rw [← realified_transpose_mulVec_im,h];rfl


theorem fourthRoot_paired_signs (z : ℂ) : IsFourthRoot z ↔
    (((1+Complex.I)*z).re=1 ∨ ((1+Complex.I)*z).re= -1) ∧
    (((1+Complex.I)*z).im=1 ∨ ((1+Complex.I)*z).im= -1) := by
  constructor
  · intro h
    rcases h with rfl|rfl|rfl|rfl <;> norm_num [Complex.mul_re,Complex.mul_im]
  · rintro ⟨hr,hi⟩
    rcases hr with hr|hr <;> rcases hi with hi|hi
    all_goals norm_num [Complex.mul_re,Complex.mul_im] at hr hi
    · left;apply Complex.ext <;> norm_num <;> linarith
    · right;right;right;apply Complex.ext <;> norm_num <;> linarith
    · right;right;left;apply Complex.ext <;> norm_num <;> linarith
    · right;left;apply Complex.ext <;> norm_num <;> linarith

theorem scaled_complex_orthogonality_iff {ι κ : Type*} [Fintype ι]
    (V : Matrix ι κ ℂ) (u : ι → ℂ) (c : ℂ) (hc : c≠0) :
    (c • V).conjTranspose.mulVec u=0 ↔ V.conjTranspose.mulVec (c⁻¹ • u)=0 := by
  rw [Matrix.conjTranspose_smul,Matrix.smul_mulVec,Matrix.mulVec_smul]
  simp only [smul_eq_zero,star_eq_zero,inv_eq_zero,hc,false_or]

theorem fourth_root_realification_extension_gate {ι κ : Type*} [Fintype ι] (V : Matrix ι κ ℂ) :
    (∃ z : ι → ℂ,(∀ i,IsFourthRoot (z i)) ∧ V.conjTranspose.mulVec z=0) ↔
    ∃ w : ι⊕ι → ℝ,IsCubeVector w ∧
      (realifiedMatrix (((1+Complex.I) : ℂ) • V)).transpose.mulVec w=0 := by
  let c : ℂ := 1+Complex.I
  have hc : c≠0 := by norm_num [c,Complex.ext_iff]
  constructor
  · rintro ⟨z,hz,horth⟩
    let u : ι → ℂ := c • z
    let w := unpackComplexVector u
    refine ⟨w,?_,?_⟩
    · intro j
      cases j with
      | inl i => simpa [w,unpackComplexVector,u,c,Pi.smul_apply,smul_eq_mul] using (fourthRoot_paired_signs (z i)).mp (hz i) |>.1
      | inr i => simpa [w,unpackComplexVector,u,c,Pi.smul_apply,smul_eq_mul] using (fourthRoot_paired_signs (z i)).mp (hz i) |>.2
    · apply (realification_orthogonality_iff (c • V) w).mpr
      change (c • V).conjTranspose.mulVec (packComplexVector (unpackComplexVector u))=0
      rw [pack_unpack_complex]
      apply (scaled_complex_orthogonality_iff V u c hc).mpr
      simpa only [u,inv_smul_smul₀ hc] using horth
  · rintro ⟨w,hw,horth⟩
    let u := packComplexVector w
    let z : ι → ℂ := c⁻¹ • u
    refine ⟨z,?_,?_⟩
    · intro i
      apply (fourthRoot_paired_signs (z i)).mpr
      have heq : (1+Complex.I)*z i=u i := by
        change c*(c⁻¹*u i)=u i
        rw [← mul_assoc,mul_inv_cancel₀ hc,one_mul]
      rw [heq]
      simpa [u,packComplexVector] using And.intro (hw (Sum.inl i)) (hw (Sum.inr i))
    · apply (scaled_complex_orthogonality_iff V u c hc).mp
      exact (realification_orthogonality_iff (c • V) w).mp horth

theorem quaternary_realification_sign_entries {ι κ : Type*} (V : Matrix ι κ ℂ)
    (hV : ∀ i j,IsFourthRoot (V i j)) :
    ∀ i j, (realifiedMatrix (((1+Complex.I) : ℂ) • V)) i j=1 ∨
      (realifiedMatrix (((1+Complex.I) : ℂ) • V)) i j= -1 := by
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j => simpa [realifiedMatrix,Matrix.fromBlocks] using (fourthRoot_paired_signs (V i j)).mp (hV i j) |>.1
    | inr j =>
      have hh := (fourthRoot_paired_signs (V i j)).mp (hV i j) |>.2
      have hn : -(((1+Complex.I)*V i j).im)=1 ∨ -(((1+Complex.I)*V i j).im)= -1 := by
        rcases hh with hh|hh
        · right;simp [hh]
        · left;simp [hh]
      simpa [realifiedMatrix,Matrix.fromBlocks] using hn
  | inr i =>
    cases j with
    | inl j => simpa [realifiedMatrix,Matrix.fromBlocks] using (fourthRoot_paired_signs (V i j)).mp (hV i j) |>.2
    | inr j => simpa [realifiedMatrix,Matrix.fromBlocks] using (fourthRoot_paired_signs (V i j)).mp (hV i j) |>.1

theorem realifiedMatrix_mul {ι κ η : Type*} [Fintype κ]
    (A : Matrix ι κ ℂ) (B : Matrix κ η ℂ) : realifiedMatrix (A*B)=realifiedMatrix A*realifiedMatrix B := by
  ext i j
  cases i <;> cases j <;>
    simp [realifiedMatrix,Matrix.fromBlocks,Matrix.mul_apply,Complex.mul_re,Complex.mul_im,
      Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_neg_distrib] <;> ring

theorem realifiedMatrix_conjTranspose {ι κ : Type*} (A : Matrix ι κ ℂ) :
    realifiedMatrix A.conjTranspose=(realifiedMatrix A).transpose := by
  ext i j
  cases i <;> cases j <;> simp [realifiedMatrix,Matrix.fromBlocks]

theorem realifiedMatrix_real_smul {ι κ : Type*} (a : ℝ) (A : Matrix ι κ ℂ) :
    realifiedMatrix ((a : ℂ) • A)=a • realifiedMatrix A := by
  ext i j
  cases i <;> cases j <;> simp [realifiedMatrix,Matrix.fromBlocks] <;> ring

theorem realifiedMatrix_one {ι : Type*} [DecidableEq ι] :
    realifiedMatrix (1 : Matrix ι ι ℂ)=(1 : Matrix (ι⊕ι) (ι⊕ι) ℝ) := by
  ext i j
  cases i <;> cases j <;> simp [realifiedMatrix,Matrix.fromBlocks,Matrix.one_apply,apply_ite]

theorem realification_column_gram {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) (a : ℝ) (hgram : V.conjTranspose*V=(a : ℂ) • (1 : Matrix κ κ ℂ)) :
    (realifiedMatrix (((1+Complex.I) : ℂ) • V)).transpose*
      realifiedMatrix (((1+Complex.I) : ℂ) • V)=
        (2*a) • (1 : Matrix (κ⊕κ) (κ⊕κ) ℝ) := by
  let c : ℂ := 1+Complex.I
  have hc : star c*c=(2 : ℂ) := by norm_num [c,Complex.ext_iff,Complex.mul_re,Complex.mul_im]
  have hh : (c • V).conjTranspose*(c • V)=((2*a : ℝ) : ℂ) • (1 : Matrix κ κ ℂ) := by
    rw [Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,hc,hgram,smul_smul]
    simp
  rw [← realifiedMatrix_conjTranspose,← realifiedMatrix_mul]
  change realifiedMatrix ((c • V).conjTranspose*(c • V))=_
  rw [hh,realifiedMatrix_real_smul,realifiedMatrix_one]

theorem quaternary_realification_gate {n m : ℕ} (V : Matrix (Fin n) (Fin m) ℂ)
    (hV : ∀ i j,IsFourthRoot (V i j))
    (hgram : V.conjTranspose*V=(n : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) :
    let A := realifiedMatrix (((1+Complex.I) : ℂ) • V)
    (∀ i j,A i j=1 ∨ A i j= -1) ∧
    A.transpose*A=(2*(n : ℝ)) • (1 : Matrix (Fin m⊕Fin m) (Fin m⊕Fin m) ℝ) ∧
    ((∃ z : Fin n → ℂ,(∀ i,IsFourthRoot (z i)) ∧ V.conjTranspose.mulVec z=0) ↔
      ∃ w : Fin n⊕Fin n → ℝ,IsCubeVector w ∧ A.transpose.mulVec w=0) := by
  refine ⟨quaternary_realification_sign_entries V hV,?_,fourth_root_realification_extension_gate V⟩
  apply realification_column_gram V (n : ℝ)
  simpa only [Complex.ofReal_natCast] using hgram

end CompletionTheory

