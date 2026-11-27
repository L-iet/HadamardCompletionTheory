/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import PhaseGeometry.ApproximateRounding
public import Mathlib.Analysis.CStarAlgebra.Matrix
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PhaseGeometry
open scoped ComplexConjugate Matrix

theorem complex_sum_mul_norm_sq_le {n : ℕ} (a b : Fin n → ℂ) :
    ‖∑ j,a j*b j‖^2 ≤ (∑ j,‖a j‖^2)*(∑ j,‖b j‖^2) := by
  have ht : ‖∑ j,a j*b j‖ ≤ ∑ j,‖a j‖*‖b j‖ := by
    simpa only [norm_mul] using norm_sum_le Finset.univ (fun j => a j*b j)
  have hs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
    (fun j => ‖a j‖) (fun j => ‖b j‖)
  have hp : 0 ≤ ∑ j,‖a j‖*‖b j‖ := by positivity
  nlinarith [norm_nonneg (∑ j,a j*b j)]

theorem euclidean_matrix_apply_entries {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (x : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) A x).ofLp i=∑ j,A i j*x.ofLp j := by
  rfl

noncomputable def euclideanOperatorNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) A‖

def matrixFrobeniusSq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i,∑ j,Complex.normSq (A i j)

theorem euclidean_matrix_apply_sq_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (x : EuclideanSpace ℂ (Fin n)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) A x‖^2 ≤ matrixFrobeniusSq A*‖x‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
  simp_rw [euclidean_matrix_apply_entries]
  calc
    _ ≤ ∑ i,(∑ j,‖A i j‖^2)*(∑ j,‖x.ofLp j‖^2) := by
      exact Finset.sum_le_sum (fun i hi => complex_sum_mul_norm_sq_le (fun j => A i j) (fun j => x.ofLp j))
    _ = _ := by
      rw [← Finset.sum_mul]
      simp only [matrixFrobeniusSq,Complex.normSq_eq_norm_sq]

theorem euclideanOperatorNorm_le_frobenius {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    euclideanOperatorNorm A ≤ Real.sqrt (matrixFrobeniusSq A) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  have hS : 0 ≤ matrixFrobeniusSq A :=
    Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => Complex.normSq_nonneg _))
  have hx := euclidean_matrix_apply_sq_bound A x
  have hs : (Real.sqrt (matrixFrobeniusSq A)*‖x‖)^2=matrixFrobeniusSq A*‖x‖^2 := by
    rw [mul_pow,Real.sq_sqrt hS]
  have hp : 0 ≤ Real.sqrt (matrixFrobeniusSq A)*‖x‖ := by positivity
  nlinarith [norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) A x)]

open scoped Matrix.Norms.L2Operator in
theorem euclideanOperatorNorm_gram {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    euclideanOperatorNorm (A*Aᴴ)=(euclideanOperatorNorm A)^2 := by
  change ‖A*Aᴴ‖=‖A‖^2
  have he := Matrix.l2_opNorm_conjTranspose_mul_self Aᴴ
  simpa only [Matrix.conjTranspose_conjTranspose,Matrix.l2_opNorm_conjTranspose,pow_two] using he

def fourthPowerMatrix {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (F i j)^4

noncomputable def rhoFourth {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  euclideanOperatorNorm (fourthPowerMatrix F)/(n : ℝ)

theorem fourthGramDeficit_eq_matrix {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) :
    fourthGramDeficit F=(n : ℝ)^4-matrixFrobeniusSq (fourthPowerMatrix F*(fourthPowerMatrix F)ᴴ) := by
  rfl

theorem fourthGramDeficit_operator_bound {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) :
    fourthGramDeficit F ≤ (n : ℝ)^4-(euclideanOperatorNorm (fourthPowerMatrix F))^4 := by
  have hs := euclideanOperatorNorm_le_frobenius (fourthPowerMatrix F*(fourthPowerMatrix F)ᴴ)
  rw [euclideanOperatorNorm_gram] at hs
  have hn : 0 ≤ matrixFrobeniusSq (fourthPowerMatrix F*(fourthPowerMatrix F)ᴴ) :=
    Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => Complex.normSq_nonneg _))
  have he := Real.sq_sqrt hn
  rw [fourthGramDeficit_eq_matrix]
  nlinarith [sq_nonneg (euclideanOperatorNorm (fourthPowerMatrix F)),Real.sqrt_nonneg (matrixFrobeniusSq (fourthPowerMatrix F*(fourthPowerMatrix F)ᴴ))]

theorem fourthGramDeficit_rho_bound {n : ℕ} (hn : 0<n)
    (F : Matrix (Fin n) (Fin n) ℂ) :
    fourthGramDeficit F ≤ (n : ℝ)^4*(1-rhoFourth F^4) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have he : (n : ℝ)^4*(1-rhoFourth F^4)=(n : ℝ)^4-(euclideanOperatorNorm (fourthPowerMatrix F))^4 := by
    unfold rhoFourth
    field_simp [hnR]
    <;> ring
  rw [he]
  exact fourthGramDeficit_operator_bound F

theorem deficit_lt_of_rho_threshold {n : ℕ} (hn : 0<n)
    (F : Matrix (Fin n) (Fin n) ℂ) (c : ℝ)
    (hs : 1-rhoFourth F^4<c/(n : ℝ)^3) : fourthGramDeficit F<c*(n : ℝ) := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have hδ := (lt_div_iff₀ (pow_pos hnR 3)).mp hs
  have hm := mul_lt_mul_of_pos_right hδ hnR
  have hb := fourthGramDeficit_rho_bound hn F
  nlinarith

theorem rho_finite_rounding_certificate {n : ℕ} (hn : 0<n)
    (F : Matrix (Fin n) (Fin n) ℂ) (hF : ∀ i j, ‖F i j‖=1)
    (horth : ∀ i k,complexRowGram F i k=if i=k then (n : ℂ) else 0)
    (hs : 1-rhoFourth F^4<1/(n : ℝ)^3) :
    ∃ Q : Matrix (Fin n) (Fin n) ℂ,IsQuaternaryHadamard Q := by
  have hd := deficit_lt_of_rho_threshold hn F 1 hs
  rw [one_mul] at hd
  obtain ⟨k,l,Q,hQ,he⟩ := finite_dephasing_rounding_certificate hn F hF horth hd
  exact ⟨Q,hQ⟩

theorem rho_even_finite_rounding_certificate {n : ℕ} (hn : 0<n) (heven : Even n)
    (F : Matrix (Fin n) (Fin n) ℂ) (hF : ∀ i j, ‖F i j‖=1)
    (horth : ∀ i k,complexRowGram F i k=if i=k then (n : ℂ) else 0)
    (hs : 1-rhoFourth F^4<2/(n : ℝ)^3) :
    ∃ Q : Matrix (Fin n) (Fin n) ℂ,IsQuaternaryHadamard Q := by
  have hd := deficit_lt_of_rho_threshold hn F 2 hs
  obtain ⟨k,l,Q,hQ,he⟩ := finite_dephasing_even_rounding_certificate hn heven F hF horth hd
  exact ⟨Q,hQ⟩

theorem no_quaternary_rho_separation {n : ℕ} (hn : 0<n)
    (F : Matrix (Fin n) (Fin n) ℂ) (hF : ∀ i j, ‖F i j‖=1)
    (horth : ∀ i k,complexRowGram F i k=if i=k then (n : ℂ) else 0)
    (hno : ¬ ∃ Q : Matrix (Fin n) (Fin n) ℂ,IsQuaternaryHadamard Q) :
    1/(n : ℝ)^3 ≤ 1-rhoFourth F^4 := by
  by_contra! hs
  exact hno (rho_finite_rounding_certificate hn F hF horth hs)

theorem no_quaternary_even_rho_separation {n : ℕ} (hn : 0<n) (heven : Even n)
    (F : Matrix (Fin n) (Fin n) ℂ) (hF : ∀ i j, ‖F i j‖=1)
    (horth : ∀ i k,complexRowGram F i k=if i=k then (n : ℂ) else 0)
    (hno : ¬ ∃ Q : Matrix (Fin n) (Fin n) ℂ,IsQuaternaryHadamard Q) :
    2/(n : ℝ)^3 ≤ 1-rhoFourth F^4 := by
  by_contra! hs
  exact hno (rho_even_finite_rounding_certificate hn heven F hF horth hs)

def IsNearestFourthRoot (z q : ℂ) : Prop := IsFourthRoot q ∧
  ∀ r : ℂ,IsFourthRoot r → Complex.normSq (z-q) ≤ Complex.normSq (z-r)

theorem exists_nearest_fourth_root_bound {z : ℂ} (hz : ‖z‖=1) :
    ∃ q : ℂ,IsNearestFourthRoot z q ∧ Complex.normSq (z-q) ≤ Complex.normSq (z^4-1)/4 := by
  classical
  let S : Finset ℂ := {1,-1,Complex.I,-Complex.I}
  have hmem (r : ℂ) : r ∈ S ↔ IsFourthRoot r := by simp [S,IsFourthRoot]
  obtain ⟨q,hq,hmin⟩ := Finset.exists_min_image S (fun r => Complex.normSq (z-r))
    (show S.Nonempty from ⟨1,(hmem 1).mpr (Or.inl rfl)⟩)
  obtain ⟨r,hr,hbound⟩ := exists_fourth_root_rounding_bound hz
  refine ⟨q,⟨(hmem q).mp hq,fun r hr => hmin r ((hmem r).mpr hr)⟩,?_⟩
  exact (hmin r ((hmem r).mpr hr)).trans hbound

theorem exists_nearest_matrix_rounding {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ)
    (hF : ∀ i j, ‖F i j‖=1) :
    ∃ Q : Matrix (Fin n) (Fin n) ℂ,(∀ i j,IsNearestFourthRoot (F i j) (Q i j)) ∧
      totalRoundingError F Q ≤ (∑ i,∑ j,Complex.normSq ((F i j)^4-1))/4 := by
  classical
  choose Q hQ hb using (fun i j => exists_nearest_fourth_root_bound (hF i j))
  refine ⟨Q,hQ,?_⟩
  rw [rounding_error_swap]
  calc
    _ ≤ ∑ i,∑ j,Complex.normSq ((F i j)^4-1)/4 :=
      Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hb i j))
    _ = _ := by simp only [Finset.sum_div]

theorem finite_dephasing_nearest_rounding_certificate {n : ℕ} (hn : 0<n)
    (F : Matrix (Fin n) (Fin n) ℂ) (hF : ∀ i j, ‖F i j‖=1)
    (horth : ∀ i k,complexRowGram F i k=if i=k then (n : ℂ) else 0)
    (hD : fourthGramDeficit F<(if Even n then 2*(n : ℝ) else (n : ℝ))) :
    ∃ k l,∃ Q : Matrix (Fin n) (Fin n) ℂ,IsQuaternaryHadamard Q ∧
      (∀ i j,IsNearestFourthRoot (pivotDephase F k l i j) (Q i j)) ∧
      totalRoundingError (fun i j => pivotDephase F k l i j) Q ≤ fourthGramDeficit F/(2*(n : ℝ)^2) := by
  classical
  obtain ⟨k,l,hpivot⟩ := exists_pivot_fourth_error_le hn F hF
  let P : Matrix (Fin n) (Fin n) ℂ := fun i j => pivotDephase F k l i j
  obtain ⟨Q,hnear,herror⟩ := exists_nearest_matrix_rounding P (pivotDephase_unit F hF k l)
  have hQ (i j : Fin n) : IsFourthRoot (Q i j) := (hnear i j).1
  have he : totalRoundingError P Q ≤ fourthGramDeficit F/(2*(n : ℝ)^2) := by
    have hdiv := div_le_div_of_nonneg_right hpivot (by norm_num : (0 : ℝ) ≤ 4)
    have hEq : (2*fourthGramDeficit F/(n : ℝ)^2)/4=fourthGramDeficit F/(2*(n : ℝ)^2) := by ring
    rw [hEq] at hdiv
    exact herror.trans hdiv
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have ho (i r : Fin n) (hir : i ≠ r) : complexRowGram P i r=0 := by
    have ho' : ∀ i r,(∑ j,F i j*conj (F r j))=if i=r then (n : ℂ) else 0 := horth
    exact (pivotDephase_hadamard_gram F hF ho' k l i r).trans (if_neg hir)
  refine ⟨k,l,Q,?_,hnear,he⟩
  by_cases hev : Even n
  · rw [if_pos hev] at hD
    exact rounded_exact_of_even_error_small hev P Q (pivotDephase_unit F hF k l) hQ ho
      (even_rounding_error_threshold hnR he hD)
  · rw [if_neg hev] at hD
    have hm := (le_div_iff₀ (show 0<2*(n : ℝ)^2 by positivity)).mp he
    have hs : 2*(n : ℝ)*totalRoundingError P Q<1 := by
      by_contra! hh
      have := mul_le_mul_of_nonneg_left hh hnR.le
      nlinarith
    exact rounded_exact_of_error_small P Q (pivotDephase_unit F hF k l) hQ ho hs

theorem rho_nearest_rounding_certificate {n : ℕ} (hn : 0<n)
    (F : Matrix (Fin n) (Fin n) ℂ) (hF : ∀ i j, ‖F i j‖=1)
    (horth : ∀ i k,complexRowGram F i k=if i=k then (n : ℂ) else 0)
    (hs : 1-rhoFourth F^4<(if Even n then 2 else 1)/(n : ℝ)^3) :
    ∃ k l,∃ Q : Matrix (Fin n) (Fin n) ℂ,IsQuaternaryHadamard Q ∧
      ∀ i j,IsNearestFourthRoot (pivotDephase F k l i j) (Q i j) := by
  classical
  have hd : fourthGramDeficit F<(if Even n then 2*(n : ℝ) else (n : ℝ)) := by
    by_cases hev : Even n
    · rw [if_pos hev] at hs ⊢
      exact deficit_lt_of_rho_threshold hn F 2 hs
    · rw [if_neg hev] at hs ⊢
      simpa only [one_mul] using deficit_lt_of_rho_threshold hn F 1 hs
  obtain ⟨k,l,Q,hQ,hnear,he⟩ := finite_dephasing_nearest_rounding_certificate hn F hF horth hd
  exact ⟨k,l,Q,hQ,hnear⟩

theorem pivot_search_card (n : ℕ) : Fintype.card (Fin n × Fin n)=n^2 := by
  simp [pow_two]
end PhaseGeometry
