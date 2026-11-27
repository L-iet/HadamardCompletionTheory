/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionQuaternary.GaussianRealParity
public import CompletionQuaternary.QuaternaryResidual
@[expose] public section
namespace CompletionTheory.Bloch
noncomputable section
open scoped BigOperators ComplexConjugate

theorem residual_bloch_diagonal_one {n : ℕ} (hn : 2≤n)
    (V : Matrix (Fin n) (Fin (n-2)) ℂ) (hfour : ∀ i j,(V i j)^4=1) :
    ∀ i,residualBlochGram V i i=1 := by
  have hflat (i j) : Complex.normSq (V i j)=1 := fourth_root_normSq_one (hfour i j)
  intro i
  have he : complexResidualGram V i i=2 := by
    simp [complexResidualGram,Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply,
      Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.mul_conj,hflat,Nat.cast_sub hn] <;> ring
  norm_num [residualBlochGram,he,Complex.normSq_apply]

theorem residual_triple_real_even {n : ℕ} (hn : 2≤n) (heven : Even n)
    (V : Matrix (Fin n) (Fin (n-2)) ℂ) (hfour : ∀ i j,(V i j)^4=1)
    (i j k : Fin n) (hij : i≠j) (hjk : j≠k) (hki : k≠i) :
    GaussianRealParity (complexResidualGram V i j+complexResidualGram V j k+complexResidualGram V k i) 0 := by
  classical
  let T (a : Fin (n-2)) := V i a*conj (V j a)+V j a*conj (V k a)+V k a*conj (V i a)
  have ht (a : Fin (n-2)) : GaussianRealParity (T a) 1 :=
    gaussian_odd_triple_real (fourth_root_gaussianParity (hfour i a))
      (fourth_root_gaussianParity (hfour j a)) (fourth_root_gaussianParity (hfour k a))
  have hh := gaussianRealParity_neg (gaussianRealParity_sum Finset.univ T (fun a _ => ht a))
  have hp : Even (-((n-2:ℕ):ℤ)) := by
    obtain ⟨m,hm⟩ := heven
    refine ⟨1-(m:ℤ),?_⟩
    omega
  have hneg : GaussianRealParity (-(∑ a,T a)) 0 := by
    apply gaussianRealParity_zero_of_even
    · simpa only [Finset.card_univ,Fintype.card_fin] using hh
    · exact hp
  have he : complexResidualGram V i j+complexResidualGram V j k+complexResidualGram V k i= -(∑ a,T a) := by
    simp [complexResidualGram,Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply,
      Matrix.mul_apply,Matrix.conjTranspose_apply,hij,hjk,hki,T,Finset.sum_add_distrib,Complex.star_def] <;> ring
  rw [he]
  exact hneg

theorem quaternary_residual_no_orthogonal_triple {n : ℕ} (hn : 2≤n) (heven : Even n)
    (V : Matrix (Fin n) (Fin (n-2)) ℂ) (hfour : ∀ i j,(V i j)^4=1) :
    ∀ i j k,¬(residualBlochGram V i j=0 ∧ residualBlochGram V j k=0 ∧ residualBlochGram V k i=0) := by
  intro i j k hzero
  have hdiag := residual_bloch_diagonal_one hn V hfour
  have hij : i≠j := by intro h; subst j; rw [hdiag] at hzero; norm_num at hzero
  have hjk : j≠k := by intro h; subst k; rw [hdiag] at hzero; norm_num at hzero
  have hki : k≠i := by intro h; subst k; rw [hdiag] at hzero; norm_num at hzero
  have hn2 (a b : Fin n) (h : residualBlochGram V a b=0) : Complex.normSq (complexResidualGram V a b)=2 := by
    unfold residualBlochGram at h
    linarith
  have hG := quaternary_residual_gaussian_even hn heven V hfour
  have h0 := gaussian_norm_two_real_odd (hG i j) (hn2 i j hzero.1)
  have h1 := gaussian_norm_two_real_odd (hG j k) (hn2 j k hzero.2.1)
  have h2 := gaussian_norm_two_real_odd (hG k i) (hn2 k i hzero.2.2)
  have hodd : GaussianRealParity (complexResidualGram V i j+complexResidualGram V j k+complexResidualGram V k i) 3 := by
    simpa using gaussianRealParity_add (gaussianRealParity_add h0 h1) h2
  have he := residual_triple_real_even hn heven V hfour i j k hij hjk hki
  have hbad := gaussianRealParity_unique hodd he
  obtain ⟨t, ht⟩ := hbad
  omega

end
end CompletionTheory.Bloch
