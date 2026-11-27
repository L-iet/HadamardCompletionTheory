/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionBloch.ResidualBloch
public import CompletionBloch.RowRotation
public import Mathlib.Tactic.Abel
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory.Bloch
noncomputable section
open scoped BigOperators

def appendComplexColumns {n : ℕ} (V : Matrix (Fin n) (Fin (n-2)) ℂ)
    (R : Matrix (Fin n) (Fin 2) ℂ) : Matrix (Fin n) (Fin (n-2) ⊕ Fin 2) ℂ :=
  fun i j => Sum.elim (V i) (R i) j

def HasTwoFlatCompletingColumns {n : ℕ} (V : Matrix (Fin n) (Fin (n-2)) ℂ) : Prop :=
  ∃ R : Matrix (Fin n) (Fin 2) ℂ,(∀ i j,Complex.normSq (R i j)=1) ∧
    (appendComplexColumns V R).conjTranspose*appendComplexColumns V R=
      (n:ℂ) • (1 : Matrix (Fin (n-2) ⊕ Fin 2) (Fin (n-2) ⊕ Fin 2) ℂ)

theorem scaled_row_gram_to_column {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (hcard : Fintype.card ι=Fintype.card κ)
    (A : Matrix ι κ ℂ) {c : ℂ} (hc : c≠0) (hrow : A*A.conjTranspose=c • 1) :
    A.conjTranspose*A=c • 1 := by
  let B : Matrix κ ι ℂ := c⁻¹ • A.conjTranspose
  have hAB : A*B=1 := by
    simp only [B,Matrix.mul_smul,hrow,smul_smul,inv_mul_cancel₀ hc,one_smul]
  have hBA : B*A=1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hcard)).mp hAB
  have hh := congrArg (fun M : Matrix κ κ ℂ => c • M) hBA
  simpa only [B,Matrix.smul_mul,smul_smul,mul_inv_cancel₀ hc,one_smul] using hh

theorem appendComplexColumns_row_gram {n : ℕ} (V : Matrix (Fin n) (Fin (n-2)) ℂ)
    (R : Matrix (Fin n) (Fin 2) ℂ) :
    appendComplexColumns V R*(appendComplexColumns V R).conjTranspose=
      V*V.conjTranspose+R*R.conjTranspose := by
  ext i j
  simp [appendComplexColumns,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_sum_type]

def blochRows {n : ℕ} (R : Matrix (Fin n) (Fin 2) ℂ) : Matrix (Fin n) (Fin 3) ℝ :=
  fun i => blochVector (R i)

theorem residual_bloch_gram_of_factor {n : ℕ} (V : Matrix (Fin n) (Fin (n-2)) ℂ)
    (R : Matrix (Fin n) (Fin 2) ℂ) (hr : ∀ i,rowNormSq (R i)=2)
    (hres : R*R.conjTranspose=complexResidualGram V) :
    residualBlochGram V=blochRows R*(blochRows R).transpose := by
  ext i j
  have he : rowInner (R i) (R j)=complexResidualGram V i j := by
    have hh := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) hres
    simpa [rowInner,Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_succ] using hh
  change Complex.normSq (complexResidualGram V i j)/2-1=dot3 (blochVector (R i)) (blochVector (R j))
  rw [←he]
  exact (bloch_gram_of_row_norm_two (R i) (R j) (hr i) (hr j)).symm

theorem complex_defect_two_rank_criterion {n : ℕ} (hn : 2≤n)
    (V : Matrix (Fin n) (Fin (n-2)) ℂ)
    (hflat : ∀ i j,Complex.normSq (V i j)=1)
    (hgram : V.conjTranspose*V=(n:ℂ) • (1 : Matrix (Fin (n-2)) (Fin (n-2)) ℂ)) :
    HasTwoFlatCompletingColumns V ↔ (residualBlochGram V).rank≤2 := by
  classical
  have hcard : Fintype.card (Fin n)=Fintype.card (Fin (n-2) ⊕ Fin 2) := by simp; omega
  have hnC : (n:ℂ)≠0 := by exact_mod_cast (show n≠0 by omega)
  constructor
  · rintro ⟨R,hR,hcol⟩
    have hrow : appendComplexColumns V R*(appendComplexColumns V R).conjTranspose=(n:ℂ) • 1 := by
      have hh := scaled_row_gram_to_column hcard.symm (appendComplexColumns V R).conjTranspose hnC
        (by simpa only [Matrix.conjTranspose_conjTranspose] using hcol)
      simpa only [Matrix.conjTranspose_conjTranspose] using hh
    have hres : R*R.conjTranspose=complexResidualGram V := by
      unfold complexResidualGram
      rw [←hrow,appendComplexColumns_row_gram]
      abel
    have hnorm : ∀ i,rowNormSq (R i)=2 := by intro i; norm_num [rowNormSq,hR]
    have hb := residual_bloch_gram_of_factor V R hnorm hres
    rw [hb]
    apply (real_gram_rank_axis_iff (blochRows R)).mpr
    refine ⟨![0,0,1],?_,?_⟩
    · norm_num [dot3,Fin.sum_univ_succ]
    · intro i
      simp [dot3,blochRows,blochVector,Fin.sum_univ_succ,hR]
  · intro hrank
    obtain ⟨R,hRg,hres⟩ := complex_residual_factor hn V hgram
    have hnorm := complex_residual_row_norm_two hn V R hflat hres
    have hb := residual_bloch_gram_of_factor V R hnorm hres
    rw [hb] at hrank
    obtain ⟨s,hs,horth⟩ := (real_gram_rank_axis_iff (blochRows R)).mp hrank
    obtain ⟨U,hU,hUc,hrotate⟩ := flat_rows_after_axis_rotation s hs
    let Q : Matrix (Fin n) (Fin 2) ℂ := R*U
    have hQ : ∀ i j,Complex.normSq (Q i j)=1 := by
      intro i j
      exact hrotate (R i) (hnorm i) (horth i) j
    have hQres : Q*Q.conjTranspose=complexResidualGram V := by
      calc
        _ = R*(U*U.conjTranspose)*R.conjTranspose := by simp only [Q,Matrix.conjTranspose_mul,Matrix.mul_assoc]
        _ = R*R.conjTranspose := by rw [hU,Matrix.mul_one]
        _ = _ := hres
    have hrow : appendComplexColumns V Q*(appendComplexColumns V Q).conjTranspose=(n:ℂ) • 1 := by
      rw [appendComplexColumns_row_gram,hQres]
      unfold complexResidualGram
      abel
    exact ⟨Q,hQ,scaled_row_gram_to_column hcard _ hnC hrow⟩

end
end CompletionTheory.Bloch
