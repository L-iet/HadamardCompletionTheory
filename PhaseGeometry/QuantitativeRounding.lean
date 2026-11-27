/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import PhaseGeometry.FourthPhase
public import PhaseGeometry.Rounding
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PhaseGeometry
open scoped ComplexConjugate

open scoped ComplexConjugate

theorem unit_fourth_normSq_error {z : ℂ} (hz : ‖z‖=1) :
    Complex.normSq (z^4-1)=16*z.re^2*z.im^2 := by
  have hn : Complex.normSq z=1 := by rw [Complex.normSq_eq_norm_sq,hz]; norm_num
  have hxy : z.re^2+z.im^2=1 := by simpa [Complex.normSq_apply,pow_two] using hn
  have hr : (z^4).re=z.re^4-6*z.re^2*z.im^2+z.im^4 := by
    simp only [pow_succ,pow_zero,mul_one,Complex.mul_re,Complex.mul_im,Complex.one_re,Complex.one_im]
    ring
  have hp : Complex.normSq (z^4)=1 := by
    rw [Complex.normSq_eq_norm_sq,norm_pow,hz]
    norm_num
  rw [Complex.normSq_sub,hp]
  simp only [Complex.normSq_one,map_one,mul_one]
  nlinarith [congrArg (fun t : ℝ => t^2) hxy]

theorem root_one_rounding_bound {z : ℂ} (hz : ‖z‖=1)
    (hx : 0 ≤ z.re) (hsector : z.im^2 ≤ z.re^2) :
    Complex.normSq (z-1) ≤ Complex.normSq (z^4-1)/4 := by
  have hn : Complex.normSq z=1 := by rw [Complex.normSq_eq_norm_sq,hz]; norm_num
  have hxy : z.re^2+z.im^2=1 := by simpa [Complex.normSq_apply,pow_two] using hn
  have hx1 : z.re ≤ 1 := by nlinarith [sq_nonneg z.im,sq_nonneg (z.re-1)]
  have hc : 0 ≤ 4*z.re^3+4*z.re^2-2 := by nlinarith [pow_nonneg hx 3]
  have hp := mul_nonneg (sub_nonneg.mpr hx1) hc
  rw [unit_fourth_normSq_error hz,Complex.normSq_sub,hn]
  simp only [Complex.normSq_one,map_one,mul_one]
  nlinarith [congrArg (fun t : ℝ => t*z.re^2) hxy]

theorem root_rounding_bound_from_sector {z q : ℂ} (hz : ‖z‖=1) (hq : IsFourthRoot q)
    (hx : 0 ≤ (z*conj q).re) (hs : (z*conj q).im^2 ≤ (z*conj q).re^2) :
    Complex.normSq (z-q) ≤ Complex.normSq (z^4-1)/4 := by
  have hqn : ‖q‖=1 := by rcases hq with rfl | rfl | rfl | rfl <;> simp
  have hq4 := (fourth_root_iff q).mp hq
  have hw : ‖z*conj q‖=1 := by simp [norm_mul,hz,hqn]
  have hpow : (z*conj q)^4=z^4 := by rw [mul_pow,← map_pow,hq4,map_one,mul_one]
  have he : (z*conj q-1)*q=z-q := by
    rw [sub_mul,mul_assoc,mul_comm (conj q) q,unit_mul_conj hqn]
    ring
  have hd : Complex.normSq (z-q)=Complex.normSq (z*conj q-1) := by
    rw [← he,Complex.normSq_mul,Complex.normSq_eq_norm_sq q,hqn]
    norm_num
  rw [hd]
  simpa only [hpow] using root_one_rounding_bound hw hx hs

theorem exists_fourth_root_rounding_bound {z : ℂ} (hz : ‖z‖=1) :
    ∃ q : ℂ,IsFourthRoot q ∧ Complex.normSq (z-q) ≤ Complex.normSq (z^4-1)/4 := by
  by_cases hc : z.im^2 ≤ z.re^2
  · by_cases hx : 0 ≤ z.re
    · refine ⟨1,Or.inl rfl,?_⟩
      exact root_one_rounding_bound hz hx hc
    · refine ⟨-1,Or.inr (Or.inl rfl),?_⟩
      apply root_rounding_bound_from_sector hz (Or.inr (Or.inl rfl))
      · simpa using le_of_lt (neg_pos.mpr (lt_of_not_ge hx))
      · simpa using hc
  · have hc' : z.re^2 ≤ z.im^2 := le_of_lt (lt_of_not_ge hc)
    by_cases hy : 0 ≤ z.im
    · refine ⟨Complex.I,Or.inr (Or.inr (Or.inl rfl)),?_⟩
      apply root_rounding_bound_from_sector hz (Or.inr (Or.inr (Or.inl rfl)))
      · simpa [Complex.mul_re,Complex.conj_I] using hy
      · simpa [Complex.mul_re,Complex.mul_im,Complex.conj_I] using hc'
    · refine ⟨-Complex.I,Or.inr (Or.inr (Or.inr rfl)),?_⟩
      apply root_rounding_bound_from_sector hz (Or.inr (Or.inr (Or.inr rfl)))
      · simpa [Complex.mul_re,Complex.conj_I] using le_of_lt (neg_pos.mpr (lt_of_not_ge hy))
      · simpa [Complex.mul_re,Complex.mul_im,Complex.conj_I] using hc'

theorem exists_matrix_fourth_root_rounding {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ)
    (hF : ∀ i j, ‖F i j‖=1) :
    ∃ Q : Matrix (Fin n) (Fin n) ℂ,(∀ i j,IsFourthRoot (Q i j)) ∧
      (∑ i,∑ j,Complex.normSq (F i j-Q i j)) ≤
        (∑ i,∑ j,Complex.normSq ((F i j)^4-1))/4 := by
  classical
  choose Q hQ hbound using (fun i j => exists_fourth_root_rounding_bound (hF i j))
  refine ⟨Q,hQ,?_⟩
  calc
    _ ≤ ∑ i,∑ j,Complex.normSq ((F i j)^4-1)/4 := by
      exact Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hbound i j))
    _ = _ := by simp only [Finset.sum_div]

theorem exists_pivot_fourth_root_rounding {n : ℕ} (hn : 0<n)
    (F : Matrix (Fin n) (Fin n) ℂ) (hF : ∀ i j, ‖F i j‖=1) :
    ∃ k l,∃ Q : Matrix (Fin n) (Fin n) ℂ,(∀ i j,IsFourthRoot (Q i j)) ∧
      (∑ i,∑ j,Complex.normSq (pivotDephase F k l i j-Q i j)) ≤
        fourthGramDeficit F/(2*(n : ℝ)^2) := by
  obtain ⟨k,l,hkl⟩ := exists_pivot_fourth_error_le hn F hF
  obtain ⟨Q,hQ,herror⟩ := exists_matrix_fourth_root_rounding
    (fun i j => pivotDephase F k l i j) (pivotDephase_unit F hF k l)
  refine ⟨k,l,Q,hQ,?_⟩
  change (∑ i,∑ j,Complex.normSq (pivotDephase F k l i j-Q i j)) ≤ pivotFourthError F k l/4 at herror
  have hdiv := div_le_div_of_nonneg_right hkl (by norm_num : (0 : ℝ) ≤ 4)
  have hEq : (2*fourthGramDeficit F/(n : ℝ)^2)/4=fourthGramDeficit F/(2*(n : ℝ)^2) := by ring
  rw [hEq] at hdiv
  exact herror.trans hdiv


open scoped ComplexConjugate

theorem fourth_root_unit {z : ℂ} (hz : IsFourthRoot z) : ‖z‖=1 := by
  rcases hz with rfl | rfl | rfl | rfl <;> simp

theorem fourth_root_mul_conj {z w : ℂ} (hz : IsFourthRoot z) (hw : IsFourthRoot w) :
    IsFourthRoot (z*conj w) := by
  apply (fourth_root_iff _).mpr
  rw [mul_pow,← map_pow,(fourth_root_iff z).mp hz,(fourth_root_iff w).mp hw,map_one,mul_one]

theorem fourth_root_gaussian {z : ℂ} (hz : IsFourthRoot z) :
    ∃ a b : ℤ,z=(a : ℂ)+(b : ℂ)*Complex.I ∧ Even (a+b-1) := by
  rcases hz with rfl | rfl | rfl | rfl
  · exact ⟨1,0,by norm_num,by norm_num⟩
  · exact ⟨-1,0,by norm_num,by norm_num⟩
  · exact ⟨0,1,by norm_num,by norm_num⟩
  · exact ⟨0,-1,by norm_num,by norm_num⟩

theorem fourth_root_sum_gaussian {n : ℕ} (v : Fin n → ℂ) (hv : ∀ j,IsFourthRoot (v j)) :
    ∃ a b : ℤ,(∑ j,v j)=(a : ℂ)+(b : ℂ)*Complex.I ∧ Even (a+b-(n : ℤ)) := by
  choose a b he hp using (fun j => fourth_root_gaussian (hv j))
  refine ⟨∑ j,a j,∑ j,b j,?_,?_⟩
  · simp only [he,Finset.sum_add_distrib,← Finset.sum_mul,← Int.cast_sum]
  · have hsum : Even (∑ j,(a j+b j-1)) := by
      choose c hc using hp
      exact ⟨∑ j,c j,by simp only [hc,Finset.sum_add_distrib]⟩
    simpa [Finset.sum_sub_distrib,Finset.sum_add_distrib] using hsum

theorem fourth_root_sum_small_zero {n : ℕ} (v : Fin n → ℂ) (hv : ∀ j,IsFourthRoot (v j))
    (hsmall : Complex.normSq (∑ j,v j)<1) : (∑ j,v j)=0 := by
  obtain ⟨a,b,he,hp⟩ := fourth_root_sum_gaussian v hv
  have hs : a^2+b^2<1 := by
    rw [he] at hsmall
    exact_mod_cast (by simpa [Complex.normSq_apply,pow_two] using hsmall : (a : ℝ)^2+(b : ℝ)^2<1)
  obtain ⟨ha,hb⟩ := gaussian_gap hs
  simp [he,ha,hb]

theorem fourth_root_sum_even_small_zero {n : ℕ} (hn : Even n)
    (v : Fin n → ℂ) (hv : ∀ j,IsFourthRoot (v j))
    (hsmall : Complex.normSq (∑ j,v j)<2) : (∑ j,v j)=0 := by
  obtain ⟨a,b,he,hp⟩ := fourth_root_sum_gaussian v hv
  have hnI : Even (n : ℤ) := by exact_mod_cast hn
  have hab : Even (a+b) := by
    have := hp.add hnI
    simpa only [sub_add_cancel] using this
  have hs : a^2+b^2<2 := by
    rw [he] at hsmall
    exact_mod_cast (by simpa [Complex.normSq_apply,pow_two] using hsmall : (a : ℝ)^2+(b : ℝ)^2<2)
  obtain ⟨ha,hb⟩ := even_gaussian_gap hab hs
  simp [he,ha,hb]

theorem fourth_root_gram_small_zero {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : ∀ i j,IsFourthRoot (Q i j)) (i k : Fin n)
    (hsmall : Complex.normSq (complexRowGram Q i k)<1) : complexRowGram Q i k=0 := by
  exact fourth_root_sum_small_zero _ (fun j => fourth_root_mul_conj (hQ i j) (hQ k j)) hsmall

theorem fourth_root_even_gram_small_zero {n : ℕ} (hn : Even n)
    (Q : Matrix (Fin n) (Fin n) ℂ) (hQ : ∀ i j,IsFourthRoot (Q i j)) (i k : Fin n)
    (hsmall : Complex.normSq (complexRowGram Q i k)<2) : complexRowGram Q i k=0 := by
  exact fourth_root_sum_even_small_zero hn _ (fun j => fourth_root_mul_conj (hQ i j) (hQ k j)) hsmall


open scoped ComplexConjugate

def rowRoundingError {n : ℕ} (F Q : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : ℝ :=
  ∑ j,Complex.normSq (Q i j-F i j)

theorem rounded_row_gram_bound {n : ℕ} (F Q : Matrix (Fin n) (Fin n) ℂ)
    (hF : ∀ i j, ‖F i j‖=1) (hQ : ∀ i j, ‖Q i j‖=1) (i k : Fin n)
    (horth : complexRowGram F i k=0) :
    Complex.normSq (complexRowGram Q i k) ≤
      2*(n : ℝ)*(rowRoundingError F Q i+rowRoundingError F Q k) := by
  classical
  have he : complexRowGram Q i k=∑ j,
      ((Q i j-F i j)*conj (Q k j)+F i j*conj (Q k j-F k j)) := by
    calc
      _ = complexRowGram Q i k-complexRowGram F i k := by rw [horth,sub_zero]
      _ = _ := by
        unfold complexRowGram
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [map_sub]
        ring
  have hnorm : ‖complexRowGram Q i k‖ ≤
      ∑ j,(‖Q i j-F i j‖+‖Q k j-F k j‖) := by
    rw [he]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    have ht := norm_add_le ((Q i j-F i j)*conj (Q k j)) (F i j*conj (Q k j-F k j))
    simpa only [norm_mul,Complex.norm_conj,hQ,hF,mul_one,one_mul] using ht
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
    (fun j => ‖Q i j-F i j‖+‖Q k j-F k j‖) (fun _ => (1 : ℝ))
  simp only [mul_one,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hcs
  have hs : (∑ j,(‖Q i j-F i j‖+‖Q k j-F k j‖)^2) ≤
      2*(rowRoundingError F Q i+rowRoundingError F Q k) := by
    unfold rowRoundingError
    rw [← Finset.sum_add_distrib,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (‖Q i j-F i j‖-‖Q k j-F k j‖)]
  have hm := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hpos : 0 ≤ ∑ j,(‖Q i j-F i j‖+‖Q k j-F k j‖) := by positivity
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg (complexRowGram Q i k)]


def totalRoundingError {n : ℕ} (F Q : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i,rowRoundingError F Q i

theorem rounded_gram_global_bound {n : ℕ} (F Q : Matrix (Fin n) (Fin n) ℂ)
    (hF : ∀ i j, ‖F i j‖=1) (hQ : ∀ i j, ‖Q i j‖=1) (i k : Fin n) (hik : i ≠ k)
    (horth : complexRowGram F i k=0) :
    Complex.normSq (complexRowGram Q i k) ≤ 2*(n : ℝ)*totalRoundingError F Q := by
  classical
  have hp : rowRoundingError F Q i+rowRoundingError F Q k ≤ totalRoundingError F Q := by
    calc
      _ = ∑ r ∈ ({i,k} : Finset (Fin n)),rowRoundingError F Q r := by simp [hik]
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro r hr hnot
        exact Finset.sum_nonneg (fun j hj => Complex.normSq_nonneg _)
  exact (rounded_row_gram_bound F Q hF hQ i k horth).trans
    (mul_le_mul_of_nonneg_left hp (by positivity))

def IsQuaternaryHadamard {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ i j,IsFourthRoot (Q i j)) ∧ ∀ i k,complexRowGram Q i k=if i=k then (n : ℂ) else 0

theorem rounded_exact_of_error_small {n : ℕ} (F Q : Matrix (Fin n) (Fin n) ℂ)
    (hF : ∀ i j, ‖F i j‖=1) (hQ : ∀ i j,IsFourthRoot (Q i j))
    (horth : ∀ i k,i ≠ k → complexRowGram F i k=0)
    (hsmall : 2*(n : ℝ)*totalRoundingError F Q<1) : IsQuaternaryHadamard Q := by
  refine ⟨hQ,?_⟩
  intro i k
  by_cases hik : i=k
  · subst k
    simp only [if_pos rfl,complexRowGram]
    have he (j : Fin n) : Q i j*conj (Q i j)=1 := unit_mul_conj (fourth_root_unit (hQ i j))
    simp [he]
  · rw [if_neg hik]
    apply fourth_root_gram_small_zero Q hQ i k
    exact (rounded_gram_global_bound F Q hF (fun i j => fourth_root_unit (hQ i j)) i k hik (horth i k hik)).trans_lt hsmall

theorem rounded_exact_of_even_error_small {n : ℕ} (hn : Even n)
    (F Q : Matrix (Fin n) (Fin n) ℂ)
    (hF : ∀ i j, ‖F i j‖=1) (hQ : ∀ i j,IsFourthRoot (Q i j))
    (horth : ∀ i k,i ≠ k → complexRowGram F i k=0)
    (hsmall : 2*(n : ℝ)*totalRoundingError F Q<2) : IsQuaternaryHadamard Q := by
  refine ⟨hQ,?_⟩
  intro i k
  by_cases hik : i=k
  · subst k
    simp only [if_pos rfl,complexRowGram]
    have he (j : Fin n) : Q i j*conj (Q i j)=1 := unit_mul_conj (fourth_root_unit (hQ i j))
    simp [he]
  · rw [if_neg hik]
    apply fourth_root_even_gram_small_zero hn Q hQ i k
    exact (rounded_gram_global_bound F Q hF (fun i j => fourth_root_unit (hQ i j)) i k hik (horth i k hik)).trans_lt hsmall

theorem rounding_error_swap {n : ℕ} (F Q : Matrix (Fin n) (Fin n) ℂ) :
    totalRoundingError F Q=∑ i,∑ j,Complex.normSq (F i j-Q i j) := by
  unfold totalRoundingError rowRoundingError
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq,norm_sub_rev]

theorem finite_dephasing_rounding_certificate {n : ℕ} (hn : 0<n)
    (F : Matrix (Fin n) (Fin n) ℂ) (hF : ∀ i j, ‖F i j‖=1)
    (horth : ∀ i k,complexRowGram F i k=if i=k then (n : ℂ) else 0)
    (hD : fourthGramDeficit F<(n : ℝ)) :
    ∃ k l,∃ Q : Matrix (Fin n) (Fin n) ℂ,IsQuaternaryHadamard Q ∧
      totalRoundingError (fun i j => pivotDephase F k l i j) Q ≤
        fourthGramDeficit F/(2*(n : ℝ)^2) := by
  obtain ⟨k,l,Q,hQ,herror⟩ := exists_pivot_fourth_root_rounding hn F hF
  let P : Matrix (Fin n) (Fin n) ℂ := fun i j => pivotDephase F k l i j
  have he : totalRoundingError P Q ≤ fourthGramDeficit F/(2*(n : ℝ)^2) := by
    rw [rounding_error_swap]
    exact herror
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have hm := (le_div_iff₀ (show 0<2*(n : ℝ)^2 by positivity)).mp he
  have hs : 2*(n : ℝ)*totalRoundingError P Q<1 := by
    by_contra! hh
    have := mul_le_mul_of_nonneg_left hh hnR.le
    nlinarith
  refine ⟨k,l,Q,?_,he⟩
  apply rounded_exact_of_error_small P Q (pivotDephase_unit F hF k l) hQ
  · intro i r hir
    have ho : ∀ i r,(∑ j,F i j*conj (F r j))=if i=r then (n : ℂ) else 0 := horth
    exact (pivotDephase_hadamard_gram F hF ho k l i r).trans (if_neg hir)
  · exact hs

theorem finite_dephasing_even_rounding_certificate {n : ℕ} (hn : 0<n) (heven : Even n)
    (F : Matrix (Fin n) (Fin n) ℂ) (hF : ∀ i j, ‖F i j‖=1)
    (horth : ∀ i k,complexRowGram F i k=if i=k then (n : ℂ) else 0)
    (hD : fourthGramDeficit F<2*(n : ℝ)) :
    ∃ k l,∃ Q : Matrix (Fin n) (Fin n) ℂ,IsQuaternaryHadamard Q ∧
      totalRoundingError (fun i j => pivotDephase F k l i j) Q ≤
        fourthGramDeficit F/(2*(n : ℝ)^2) := by
  obtain ⟨k,l,Q,hQ,herror⟩ := exists_pivot_fourth_root_rounding hn F hF
  let P : Matrix (Fin n) (Fin n) ℂ := fun i j => pivotDephase F k l i j
  have he : totalRoundingError P Q ≤ fourthGramDeficit F/(2*(n : ℝ)^2) := by
    rw [rounding_error_swap]
    exact herror
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have hs : 2*(n : ℝ)*totalRoundingError P Q<2 :=
    even_rounding_error_threshold hnR he hD
  refine ⟨k,l,Q,?_,he⟩
  apply rounded_exact_of_even_error_small heven P Q (pivotDephase_unit F hF k l) hQ
  · intro i r hir
    have ho : ∀ i r,(∑ j,F i j*conj (F r j))=if i=r then (n : ℂ) else 0 := horth
    exact (pivotDephase_hadamard_gram F hF ho k l i r).trans (if_neg hir)
  · exact hs

theorem no_quaternary_deficit_lower {n : ℕ} (hn : 0<n)
    (F : Matrix (Fin n) (Fin n) ℂ) (hF : ∀ i j, ‖F i j‖=1)
    (horth : ∀ i k,complexRowGram F i k=if i=k then (n : ℂ) else 0)
    (hno : ¬ ∃ Q : Matrix (Fin n) (Fin n) ℂ,IsQuaternaryHadamard Q) :
    (n : ℝ) ≤ fourthGramDeficit F := by
  by_contra! hh
  obtain ⟨k,l,Q,hQ,he⟩ := finite_dephasing_rounding_certificate hn F hF horth hh
  exact hno ⟨Q,hQ⟩

theorem no_quaternary_even_deficit_lower {n : ℕ} (hn : 0<n) (heven : Even n)
    (F : Matrix (Fin n) (Fin n) ℂ) (hF : ∀ i j, ‖F i j‖=1)
    (horth : ∀ i k,complexRowGram F i k=if i=k then (n : ℂ) else 0)
    (hno : ¬ ∃ Q : Matrix (Fin n) (Fin n) ℂ,IsQuaternaryHadamard Q) :
    2*(n : ℝ) ≤ fourthGramDeficit F := by
  by_contra! hh
  obtain ⟨k,l,Q,hQ,he⟩ := finite_dephasing_even_rounding_certificate hn heven F hF horth hh
  exact hno ⟨Q,hQ⟩
end PhaseGeometry
