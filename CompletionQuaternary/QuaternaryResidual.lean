/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionQuaternary.GaussianParity
public import CompletionBloch.ResidualBloch
@[expose] public section
namespace CompletionTheory.Bloch
noncomputable section
open scoped BigOperators ComplexConjugate

theorem two_row_lagrange (r s : Fin 2 → ℂ) :
    Complex.normSq (rowInner r s)+Complex.normSq (r 0*s 1-r 1*s 0)=rowNormSq r*rowNormSq s := by
  simp [rowInner,rowNormSq,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im]
  ring

theorem residual_norm_le_four {n : ℕ} (hn : 2≤n)
    (V : Matrix (Fin n) (Fin (n-2)) ℂ)
    (hflat : ∀ i j,Complex.normSq (V i j)=1)
    (hgram : V.conjTranspose*V=(n:ℂ) • (1 : Matrix (Fin (n-2)) (Fin (n-2)) ℂ)) :
    ∀ i j,Complex.normSq (complexResidualGram V i j)≤4 := by
  obtain ⟨R,hRg,hres⟩ := complex_residual_factor hn V hgram
  have hnorm := complex_residual_row_norm_two hn V R hflat hres
  intro i j
  have he : rowInner (R i) (R j)=complexResidualGram V i j := by
    have hh := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) hres
    simpa [rowInner,complexResidualGram,Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_succ] using hh
  have hh := two_row_lagrange (R i) (R j)
  rw [he,hnorm i,hnorm j] at hh
  nlinarith [Complex.normSq_nonneg (R i 0*R j 1-R i 1*R j 0)]

theorem fourth_root_normSq_one {z : ℂ} (hz : z^4=1) : Complex.normSq z=1 := by
  rcases fourth_root_cases hz with rfl|rfl|rfl|rfl <;> norm_num [Complex.normSq_apply]

theorem quaternary_residual_gaussian_even {n : ℕ} (hn : 2≤n) (heven : Even n)
    (V : Matrix (Fin n) (Fin (n-2)) ℂ) (hfour : ∀ i j,(V i j)^4=1) :
    ∀ i j,GaussianEven (complexResidualGram V i j) := by
  classical
  have hflat (i j) : Complex.normSq (V i j)=1 := fourth_root_normSq_one (hfour i j)
  intro i j
  by_cases hij : i=j
  · subst j
    have he : complexResidualGram V i i=2 := by
      simp [complexResidualGram,Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply,
        Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.mul_conj,hflat,
        Nat.cast_sub hn] <;> ring
    rw [he]
    exact ⟨2,0,by norm_num,1,by norm_num⟩
  · have ht (k : Fin (n-2)) : GaussianParity (V i k*star (V j k)) 1 := by
      have hh := gaussianParity_mul (fourth_root_gaussianParity (hfour i k))
        (gaussianParity_conj (fourth_root_gaussianParity (hfour j k)))
      simpa only [mul_one,Complex.star_def] using hh
    have hsum := gaussianParity_sum Finset.univ (fun k => V i k*star (V j k)) (fun k _ => ht k)
    have hneg : GaussianParity (-(∑ k,V i k*star (V j k))) (-((n-2:ℕ):ℤ)) := by
      simpa only [Finset.card_univ,Fintype.card_fin] using gaussianParity_neg hsum
    have hparity : Even (-((n-2:ℕ):ℤ)) := by
      obtain ⟨m,hm⟩ := heven
      refine ⟨1-(m:ℤ),?_⟩
      omega
    have hg := gaussianEven_of_parity_even hneg hparity
    simpa [complexResidualGram,Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply,hij,
      Matrix.mul_apply,Matrix.conjTranspose_apply] using hg

theorem quaternary_residual_bloch_entries {n : ℕ} (hn : 2≤n) (heven : Even n)
    (V : Matrix (Fin n) (Fin (n-2)) ℂ) (hfour : ∀ i j,(V i j)^4=1)
    (hgram : V.conjTranspose*V=(n:ℂ) • (1 : Matrix (Fin (n-2)) (Fin (n-2)) ℂ)) :
    ∀ i j,residualBlochGram V i j= -1 ∨ residualBlochGram V i j=0 ∨ residualBlochGram V i j=1 := by
  have hflat (i j) : Complex.normSq (V i j)=1 := fourth_root_normSq_one (hfour i j)
  have hG := quaternary_residual_gaussian_even hn heven V hfour
  have hN := residual_norm_le_four hn V hflat hgram
  intro i j
  rcases gaussian_even_norm_classification (hG i j) (hN i j) with h|h|h
  · left
    norm_num [residualBlochGram,h]
  · right;left
    norm_num [residualBlochGram,h]
  · right;right
    norm_num [residualBlochGram,h]

end
end CompletionTheory.Bloch
