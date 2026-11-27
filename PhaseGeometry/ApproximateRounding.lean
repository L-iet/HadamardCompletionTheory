/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import PhaseGeometry.QuantitativeRounding
public import Mathlib.Analysis.SpecialFunctions.Sqrt
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PhaseGeometry
open scoped ComplexConjugate

theorem row_gram_difference_bound {n : ℕ} (F Q : Matrix (Fin n) (Fin n) ℂ)
    (hF : ∀ i j, ‖F i j‖=1) (hQ : ∀ i j, ‖Q i j‖=1) (i k : Fin n) :
    Complex.normSq (complexRowGram Q i k-complexRowGram F i k) ≤
      2*(n : ℝ)*(rowRoundingError F Q i+rowRoundingError F Q k) := by
  classical
  have he : complexRowGram Q i k-complexRowGram F i k=∑ j,
      ((Q i j-F i j)*conj (Q k j)+F i j*conj (Q k j-F k j)) := by
    unfold complexRowGram
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [map_sub]
    ring
  have hnorm : ‖complexRowGram Q i k-complexRowGram F i k‖ ≤
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
  nlinarith [norm_nonneg (complexRowGram Q i k-complexRowGram F i k)]

theorem gram_difference_global_bound {n : ℕ} (F Q : Matrix (Fin n) (Fin n) ℂ)
    (hF : ∀ i j, ‖F i j‖=1) (hQ : ∀ i j, ‖Q i j‖=1) (i k : Fin n) (hik : i ≠ k) :
    Complex.normSq (complexRowGram Q i k-complexRowGram F i k) ≤
      2*(n : ℝ)*totalRoundingError F Q := by
  classical
  have hp : rowRoundingError F Q i+rowRoundingError F Q k ≤ totalRoundingError F Q := by
    calc
      _ = ∑ r ∈ ({i,k} : Finset (Fin n)),rowRoundingError F Q r := by simp [hik]
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro r hr hnot
        exact Finset.sum_nonneg (fun j hj => Complex.normSq_nonneg _)
  exact (row_gram_difference_bound F Q hF hQ i k).trans
    (mul_le_mul_of_nonneg_left hp (by positivity))

theorem rounded_gram_norm_approximation {n : ℕ} (F Q : Matrix (Fin n) (Fin n) ℂ)
    (hF : ∀ i j, ‖F i j‖=1) (hQ : ∀ i j, ‖Q i j‖=1) (i k : Fin n) (hik : i ≠ k) :
    ‖complexRowGram Q i k‖ ≤ ‖complexRowGram F i k‖+
      Real.sqrt (2*(n : ℝ)*totalRoundingError F Q) := by
  have he := gram_difference_global_bound F Q hF hQ i k hik
  rw [Complex.normSq_eq_norm_sq] at he
  have hs := Real.le_sqrt_of_sq_le he
  calc
    _ = ‖complexRowGram F i k+(complexRowGram Q i k-complexRowGram F i k)‖ := by congr 1; ring
    _ ≤ ‖complexRowGram F i k‖+‖complexRowGram Q i k-complexRowGram F i k‖ := norm_add_le _ _
    _ ≤ _ := add_le_add_right hs _

theorem two_objective_rounding_certificate {n : ℕ} (hn : 0<n)
    (F : Matrix (Fin n) (Fin n) ℂ) (hF : ∀ i j, ‖F i j‖=1) (beta : ℝ)
    (hbeta : ∀ i k,i ≠ k → ‖complexRowGram F i k‖ ≤ beta)
    (hboundary : beta+Real.sqrt (fourthGramDeficit F/(n : ℝ))<
      if Even n then Real.sqrt 2 else 1) :
    ∃ Q : Matrix (Fin n) (Fin n) ℂ,IsQuaternaryHadamard Q := by
  classical
  obtain ⟨k,l,Q,hQ,herror⟩ := exists_pivot_fourth_root_rounding hn F hF
  let P : Matrix (Fin n) (Fin n) ℂ := fun i j => pivotDephase F k l i j
  have he : totalRoundingError P Q ≤ fourthGramDeficit F/(2*(n : ℝ)^2) := by
    rw [rounding_error_swap]
    exact herror
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have he2 : 2*(n : ℝ)*totalRoundingError P Q ≤ fourthGramDeficit F/(n : ℝ) := by
    calc
      _ ≤ 2*(n : ℝ)*(fourthGramDeficit F/(2*(n : ℝ)^2)) := mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by field_simp [hnR.ne']
  have hPbeta (i r : Fin n) (hir : i ≠ r) : ‖complexRowGram P i r‖ ≤ beta := by
    change ‖∑ j,pivotDephase F k l i j*conj (pivotDephase F k l r j)‖ ≤ beta
    rw [pivotDephase_gram F hF]
    simpa only [norm_mul,Complex.norm_conj,hF,one_mul,complexRowGram] using hbeta i r hir
  refine ⟨Q,hQ,?_⟩
  intro i r
  by_cases hir : i=r
  · subst r
    simp only [if_pos rfl,complexRowGram]
    have hh (j : Fin n) : Q i j*conj (Q i j)=1 := unit_mul_conj (fourth_root_unit (hQ i j))
    simp [hh]
  · rw [if_neg hir]
    have hnorm := rounded_gram_norm_approximation P Q (pivotDephase_unit F hF k l)
      (fun a b => fourth_root_unit (hQ a b)) i r hir
    have hlim : ‖complexRowGram Q i r‖ < (if Even n then Real.sqrt 2 else 1) := by
      calc
        _ ≤ ‖complexRowGram P i r‖+Real.sqrt (2*(n : ℝ)*totalRoundingError P Q) := hnorm
        _ ≤ beta+Real.sqrt (fourthGramDeficit F/(n : ℝ)) := add_le_add (hPbeta i r hir) (Real.sqrt_le_sqrt he2)
        _ < _ := hboundary
    by_cases hev : Even n
    · rw [if_pos hev] at hlim
      apply fourth_root_even_gram_small_zero hev Q hQ i r
      rw [Complex.normSq_eq_norm_sq]
      have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
      nlinarith [norm_nonneg (complexRowGram Q i r),Real.sqrt_nonneg (2 : ℝ)]
    · rw [if_neg hev] at hlim
      apply fourth_root_gram_small_zero Q hQ i r
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg (complexRowGram Q i r)]
end PhaseGeometry
