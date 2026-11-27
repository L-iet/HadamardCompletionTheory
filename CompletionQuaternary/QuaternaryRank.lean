/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionQuaternary.QuantizedFrame
public import CompletionQuaternary.QuaternaryResidual
public import CompletionBloch.RankCriterion
@[expose] public section
namespace CompletionTheory.Bloch
noncomputable section
open scoped BigOperators

def HasTwoFourthRootCompletingColumns {n : ℕ} (V : Matrix (Fin n) (Fin (n-2)) ℂ) : Prop :=
  ∃ R : Matrix (Fin n) (Fin 2) ℂ,(∀ i j,(R i j)^4=1) ∧
    (appendComplexColumns V R).conjTranspose*appendComplexColumns V R=
      (n:ℂ) • (1 : Matrix (Fin (n-2) ⊕ Fin 2) (Fin (n-2) ⊕ Fin 2) ℂ)

theorem quaternary_bloch_discreteness {n : ℕ} (hn : 2≤n) (heven : Even n)
    (V : Matrix (Fin n) (Fin (n-2)) ℂ) (hfour : ∀ i j,(V i j)^4=1)
    (hgram : V.conjTranspose*V=(n:ℂ) • (1 : Matrix (Fin (n-2)) (Fin (n-2)) ℂ)) :
    (∀ i j,residualBlochGram V i j= -1 ∨ residualBlochGram V i j=0 ∨ residualBlochGram V i j=1) ∧
      (residualBlochGram V).rank≤3 := by
  refine ⟨quaternary_residual_bloch_entries hn heven V hfour hgram,?_⟩
  exact residual_bloch_rank_le_three hn V (fun i j => fourth_root_normSq_one (hfour i j)) hgram

theorem quaternary_defect_two_completion_equivalence {n : ℕ} (hn : 2≤n) (heven : Even n)
    (V : Matrix (Fin n) (Fin (n-2)) ℂ) (hfour : ∀ i j,(V i j)^4=1)
    (hgram : V.conjTranspose*V=(n:ℂ) • (1 : Matrix (Fin (n-2)) (Fin (n-2)) ℂ)) :
    (HasTwoFourthRootCompletingColumns V ↔ HasTwoFlatCompletingColumns V) ∧
      (HasTwoFourthRootCompletingColumns V ↔ (residualBlochGram V).rank≤2) := by
  classical
  have hflatV (i j) : Complex.normSq (V i j)=1 := fourth_root_normSq_one (hfour i j)
  have hcard : Fintype.card (Fin n)=Fintype.card (Fin (n-2) ⊕ Fin 2) := by simp; omega
  have hnC : (n:ℂ)≠0 := by exact_mod_cast (show n≠0 by omega)
  haveI : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  have heq : HasTwoFourthRootCompletingColumns V ↔ HasTwoFlatCompletingColumns V := by
    constructor
    · rintro ⟨R,hR,hcol⟩
      exact ⟨R,fun i j => fourth_root_normSq_one (hR i j),hcol⟩
    · rintro ⟨R,hflat,hcol⟩
      have hrow : appendComplexColumns V R*(appendComplexColumns V R).conjTranspose=(n:ℂ) • 1 := by
        have hh := scaled_row_gram_to_column hcard.symm (appendComplexColumns V R).conjTranspose hnC
          (by simpa only [Matrix.conjTranspose_conjTranspose] using hcol)
        simpa only [Matrix.conjTranspose_conjTranspose] using hh
      have hres : R*R.conjTranspose=complexResidualGram V := by
        unfold complexResidualGram
        rw [←hrow,appendComplexColumns_row_gram]
        abel
      have hnorm (i : Fin n) : rowNormSq (R i)=2 := by norm_num [rowNormSq,hflat]
      have hb := residual_bloch_gram_of_factor V R hnorm hres
      have hBentries := quaternary_residual_bloch_entries hn heven V hfour hgram
      have hB : ∀ i j,dot3 (blochVector (R i)) (blochVector (R j))= -1 ∨
          dot3 (blochVector (R i)) (blochVector (R j))=0 ∨
          dot3 (blochVector (R i)) (blochVector (R j))=1 := by
        intro i j
        have he : dot3 (blochVector (R i)) (blochVector (R j))=residualBlochGram V i j := by
          have hh := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hb
          simpa [Matrix.mul_apply,Matrix.transpose_apply,blochRows,dot3] using hh.symm
        rw [he]
        exact hBentries i j
      have hG (i j : Fin n) : GaussianEven (rowInner (R i) (R j)) := by
        have he : rowInner (R i) (R j)=complexResidualGram V i j := by
          have hh := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) hres
          simpa [rowInner,Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_succ] using hh
        rw [he]
        exact quaternary_residual_gaussian_even hn heven V hfour i j
      obtain ⟨Q,hQ,hGram⟩ := quantize_flat_rows (fun i => R i) hflat hB hG
      let S : Matrix (Fin n) (Fin 2) ℂ := Q
      have hSres : S*S.conjTranspose=complexResidualGram V := by
        have hh : S*S.conjTranspose=R*R.conjTranspose := by
          ext i j
          change (∑ k : Fin 2, Q i k * star (Q j k)) =
            ∑ k : Fin 2, R i k * star (R j k)
          simpa [rowInner, Fin.sum_univ_succ] using hGram i j
        exact hh.trans hres
      have hSrow : appendComplexColumns V S*(appendComplexColumns V S).conjTranspose=(n:ℂ) • 1 := by
        rw [appendComplexColumns_row_gram,hSres]
        unfold complexResidualGram
        abel
      exact ⟨S,hQ,scaled_row_gram_to_column hcard _ hnC hSrow⟩
  exact ⟨heq,heq.trans (complex_defect_two_rank_criterion hn V hflatV hgram)⟩

end
end CompletionTheory.Bloch
