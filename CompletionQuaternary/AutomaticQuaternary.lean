/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionQuaternary.ResidualTriples
public import CompletionQuaternary.DiscreteGramRank
public import CompletionQuaternary.QuaternaryRank
@[expose] public section
namespace CompletionTheory.Bloch
noncomputable section

theorem automatic_quaternary_bloch_rank {n : ℕ} (hn : 2≤n) (heven : Even n)
    (V : Matrix (Fin n) (Fin (n-2)) ℂ) (hfour : ∀ i j,(V i j)^4=1)
    (hgram : V.conjTranspose*V=(n:ℂ) • (1 : Matrix (Fin (n-2)) (Fin (n-2)) ℂ)) :
    (residualBlochGram V).rank≤2 := by
  have hflat (i j) : Complex.normSq (V i j)=1 := fourth_root_normSq_one (hfour i j)
  obtain ⟨b,hunit,hB⟩ := residual_bloch_unit_gram hn V hflat hgram
  have hdot (i j : Fin n) : residualBlochGram V i j=dot3 (b i) (b j) := by
    have hh := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hB
    simpa [Matrix.mul_apply,Matrix.transpose_apply,dot3] using hh
  have hentries := quaternary_residual_bloch_entries hn heven V hfour hgram
  have hdiscrete (i j : Fin n) : dot3 (b i) (b j)= -1 ∨ dot3 (b i) (b j)=0 ∨ dot3 (b i) (b j)=1 := by
    simpa only [hdot i j] using hentries i j
  have hno (i j k : Fin n) : ¬(dot3 (b i) (b j)=0 ∧ dot3 (b j) (b k)=0 ∧ dot3 (b k) (b i)=0) := by
    intro h
    apply quaternary_residual_no_orthogonal_triple hn heven V hfour i j k
    simpa only [hdot i j,hdot j k,hdot k i] using h
  rw [hB]
  exact discrete_unit_gram_rank_le_two (by omega) b hunit hdiscrete hno

theorem automatic_quaternary_defect_two_completion {n : ℕ} (hn : 2≤n) (heven : Even n)
    (V : Matrix (Fin n) (Fin (n-2)) ℂ) (hfour : ∀ i j,(V i j)^4=1)
    (hgram : V.conjTranspose*V=(n:ℂ) • (1 : Matrix (Fin (n-2)) (Fin (n-2)) ℂ)) :
    HasTwoFourthRootCompletingColumns V :=
  (quaternary_defect_two_completion_equivalence hn heven V hfour hgram).2.mpr
    (automatic_quaternary_bloch_rank hn heven V hfour hgram)

end
end CompletionTheory.Bloch
