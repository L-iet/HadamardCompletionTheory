/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import PhaseGeometry.OperatorDeficit
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.Permutation
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PhaseGeometry
open scoped ComplexConjugate Matrix

theorem unit_fourth_power_lipschitz {z w : ℂ} (hz : ‖z‖=1) (hw : ‖w‖=1) :
    ‖z^4-w^4‖ ≤ 4*‖z-w‖ := by
  have hs : ‖z^3+z^2*w+z*w^2+w^3‖ ≤ 4 := by
    have h1 := norm_add_le (z^3+z^2*w+z*w^2) (w^3)
    have h2 := norm_add_le (z^3+z^2*w) (z*w^2)
    have h3 := norm_add_le (z^3) (z^2*w)
    simp only [norm_mul,norm_pow,hz,hw,one_pow,mul_one] at h1 h2 h3
    linarith
  calc
    _ = ‖z-w‖*‖z^3+z^2*w+z*w^2+w^3‖ := by rw [← norm_mul]; congr 1; ring
    _ ≤ ‖z-w‖*4 := mul_le_mul_of_nonneg_left hs (norm_nonneg _)
    _ = _ := by ring

theorem fourth_root_power_error_bound {z q : ℂ} (hz : ‖z‖=1) (hq : IsFourthRoot q) :
    Complex.normSq (z^4-1) ≤ 16*Complex.normSq (z-q) := by
  have he := unit_fourth_power_lipschitz hz (fourth_root_unit hq)
  rw [(fourth_root_iff q).mp hq] at he
  rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg (z^4-1),norm_nonneg (z-q)]

theorem rhoFourth_le_one {n : ℕ} (hn : 0<n) (F : Matrix (Fin n) (Fin n) ℂ)
    (hF : ∀ i j, ‖F i j‖=1) : rhoFourth F ≤ 1 := by
  have hs : matrixFrobeniusSq (fourthPowerMatrix F)=(n : ℝ)^2 := by
    simp only [matrixFrobeniusSq,fourthPowerMatrix,Complex.normSq_eq_norm_sq,norm_pow,hF,one_pow]
    simp
    ring
  have hb := euclideanOperatorNorm_le_frobenius (fourthPowerMatrix F)
  rw [hs,Real.sqrt_sq (Nat.cast_nonneg n)] at hb
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  exact (div_le_one hnR).mpr hb

theorem matrix_sum_norm_le_operator {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖∑ i,∑ j,A i j‖ ≤ (n : ℝ)*euclideanOperatorNorm A := by
  classical
  let x : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (fun _ => (1 : ℂ))
  let y : EuclideanSpace ℂ (Fin n) := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) A x
  have hx : ‖x‖^2=(n : ℝ) := by rw [PiLp.norm_sq_eq_of_L2]; simp [x]
  have hentry (i : Fin n) : y.ofLp i=∑ j,A i j := by
    rw [euclidean_matrix_apply_entries]
    simp [x]
  have hc : ‖∑ i,y.ofLp i‖^2 ≤ (n : ℝ)*‖y‖^2 := by
    have hh := complex_sum_mul_norm_sq_le (fun _ : Fin n => (1 : ℂ)) (fun i => y.ofLp i)
    simpa only [one_mul,norm_one,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
      PiLp.norm_sq_eq_of_L2] using hh
  have hy : ‖y‖ ≤ euclideanOperatorNorm A*‖x‖ := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) A).le_opNorm x
  have hnonneg : 0 ≤ euclideanOperatorNorm A := norm_nonneg _
  have hsq : ‖y‖^2 ≤ euclideanOperatorNorm A^2*(n : ℝ) := by
    have he : (euclideanOperatorNorm A*‖x‖)^2=euclideanOperatorNorm A^2*(n : ℝ) := by rw [mul_pow,hx]
    have hp : 0 ≤ euclideanOperatorNorm A*‖x‖ := mul_nonneg hnonneg (norm_nonneg _)
    nlinarith [norm_nonneg y]
  have hm := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hs : (∑ i,∑ j,A i j)=∑ i,y.ofLp i := by simp only [hentry]
  rw [hs]
  have hp : 0 ≤ (n : ℝ)*euclideanOperatorNorm A := mul_nonneg (Nat.cast_nonneg n) hnonneg
  nlinarith [norm_nonneg (∑ i,y.ofLp i)]

theorem unit_matrix_error_identity {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ i j, ‖M i j‖=1) :
    (∑ i,∑ j,Complex.normSq (M i j-1))=2*(n : ℝ)^2-2*(∑ i,∑ j,M i j).re := by
  have he (i j : Fin n) : Complex.normSq (M i j-1)=2-2*(M i j).re := by
    rw [Complex.normSq_sub]
    have hh : Complex.normSq (M i j)=1 := by rw [Complex.normSq_eq_norm_sq,hM]; norm_num
    rw [hh]
    simp
    ring
  simp_rw [he,Finset.sum_sub_distrib,← Finset.mul_sum]
  simp only [Complex.re_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

theorem fourth_power_error_operator_lower {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ)
    (hF : ∀ i j, ‖F i j‖=1) :
    2*(n : ℝ)^2-2*(n : ℝ)*euclideanOperatorNorm (fourthPowerMatrix F) ≤
      ∑ i,∑ j,Complex.normSq ((F i j)^4-1) := by
  have hu (i j : Fin n) : ‖fourthPowerMatrix F i j‖=1 := by simp only [fourthPowerMatrix,norm_pow,hF,one_pow]
  have he := unit_matrix_error_identity (fourthPowerMatrix F) hu
  have hb := (Complex.re_le_norm (∑ i,∑ j,fourthPowerMatrix F i j)).trans
    (matrix_sum_norm_le_operator (fourthPowerMatrix F))
  change _ ≤ ∑ i,∑ j,Complex.normSq (fourthPowerMatrix F i j-1)
  rw [he]
  linarith

theorem quaternary_distance_lower_bound {n : ℕ} (hn : 0<n)
    (F Q : Matrix (Fin n) (Fin n) ℂ) (hF : ∀ i j, ‖F i j‖=1)
    (hQ : ∀ i j,IsFourthRoot (Q i j)) :
    (1-rhoFourth F)/8 ≤ totalRoundingError F Q/(n : ℝ)^2 := by
  have hu : (∑ i,∑ j,Complex.normSq ((F i j)^4-1)) ≤ 16*totalRoundingError F Q := by
    rw [rounding_error_swap,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j hj => fourth_root_power_error_bound (hF i j) (hQ i j))
  have hl := fourth_power_error_operator_lower F hF
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have he : (n : ℝ)^2*(1-rhoFourth F)=(n : ℝ)^2-(n : ℝ)*euclideanOperatorNorm (fourthPowerMatrix F) := by
    unfold rhoFourth
    field_simp [hnR.ne']
  apply (le_div_iff₀ (pow_pos hnR 2)).mpr
  nlinarith

def phaseTransform {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) (r c : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ := fun i j => r i*F i j*c j

theorem phase_diagonal_unitary {n : ℕ} (r : Fin n → ℂ) (hr : ∀ i,‖r i‖=1) :
    Matrix.diagonal r ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := by
  rw [Matrix.diagonal_mem_unitary,Unitary.mem_iff]
  constructor
  · ext i
    change conj (r i)*r i=1
    rw [mul_comm]
    exact unit_mul_conj (hr i)
  · ext i
    exact unit_mul_conj (hr i)

open scoped Matrix.Norms.L2Operator in
theorem euclideanOperatorNorm_phase_transform {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ)
    (r c : Fin n → ℂ) (hr : ∀ i,‖r i‖=1) (hc : ∀ j,‖c j‖=1) :
    euclideanOperatorNorm (phaseTransform F r c)=euclideanOperatorNorm F := by
  have he : phaseTransform F r c=Matrix.diagonal r*F*Matrix.diagonal c := by
    ext i j
    simp [phaseTransform,Matrix.diagonal_mul,Matrix.mul_diagonal]
  rw [he]
  change ‖Matrix.diagonal r*F*Matrix.diagonal c‖=‖F‖
  rw [CStarRing.norm_mul_mem_unitary _ (phase_diagonal_unitary c hc),
    CStarRing.norm_mem_unitary_mul _ (phase_diagonal_unitary r hr)]

theorem rhoFourth_phase_invariant {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ)
    (r c : Fin n → ℂ) (hr : ∀ i,‖r i‖=1) (hc : ∀ j,‖c j‖=1) :
    rhoFourth (phaseTransform F r c)=rhoFourth F := by
  have he : fourthPowerMatrix (phaseTransform F r c)=
      phaseTransform (fourthPowerMatrix F) (fun i => (r i)^4) (fun j => (c j)^4) := by
    ext i j
    simp only [fourthPowerMatrix,phaseTransform,mul_pow]
  unfold rhoFourth
  rw [he,euclideanOperatorNorm_phase_transform]
  · intro i; simp [norm_pow,hr]
  · intro j; simp [norm_pow,hc]

def permuteMatrix {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) (s t : Equiv.Perm (Fin n)) :
    Matrix (Fin n) (Fin n) ℂ := fun i j => F (s i) (t j)

theorem permutation_matrix_unitary {n : ℕ} (s : Equiv.Perm (Fin n)) :
    s.permMatrix ℂ ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := by
  simp only [Unitary.mem_iff,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_permMatrix]
  constructor <;> rw [← Matrix.permMatrix_mul] <;> simp

open scoped Matrix.Norms.L2Operator in
theorem euclideanOperatorNorm_permute {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ)
    (s t : Equiv.Perm (Fin n)) :
    euclideanOperatorNorm (permuteMatrix F s t)=euclideanOperatorNorm F := by
  have he : permuteMatrix F s t=s.permMatrix ℂ*F*(t⁻¹).permMatrix ℂ := by
    rw [PEquiv.toMatrix_toPEquiv_mul,PEquiv.mul_toMatrix_toPEquiv]
    ext i j
    rfl
  rw [he]
  change ‖s.permMatrix ℂ*F*(t⁻¹).permMatrix ℂ‖=‖F‖
  rw [CStarRing.norm_mul_mem_unitary _ (permutation_matrix_unitary (t⁻¹)),
    CStarRing.norm_mem_unitary_mul _ (permutation_matrix_unitary s)]

theorem rhoFourth_permutation_invariant {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ)
    (s t : Equiv.Perm (Fin n)) : rhoFourth (permuteMatrix F s t)=rhoFourth F := by
  have he : fourthPowerMatrix (permuteMatrix F s t)=permuteMatrix (fourthPowerMatrix F) s t := rfl
  unfold rhoFourth
  rw [he,euclideanOperatorNorm_permute]

theorem equivalent_quaternary_distance_lower {n : ℕ} (hn : 0<n)
    (F Q : Matrix (Fin n) (Fin n) ℂ) (hF : ∀ i j, ‖F i j‖=1)
    (hQ : ∀ i j,IsFourthRoot (Q i j)) (s t : Equiv.Perm (Fin n))
    (r c : Fin n → ℂ) (hr : ∀ i,‖r i‖=1) (hc : ∀ j,‖c j‖=1) :
    (1-rhoFourth F)/8 ≤ totalRoundingError (phaseTransform (permuteMatrix F s t) r c) Q/(n : ℝ)^2 := by
  have hu (i j : Fin n) : ‖phaseTransform (permuteMatrix F s t) r c i j‖=1 := by
    simp only [phaseTransform,permuteMatrix,norm_mul,hr,hc,hF,mul_one,one_mul]
  have hb := quaternary_distance_lower_bound hn _ Q hu hQ
  rwa [rhoFourth_phase_invariant _ r c hr hc,rhoFourth_permutation_invariant] at hb

theorem ones_euclideanOperatorNorm {n : ℕ} (hn : 0<n) :
    euclideanOperatorNorm (fun _ _ : Fin n => (1 : ℂ))=(n : ℝ) := by
  let J : Matrix (Fin n) (Fin n) ℂ := fun _ _ => 1
  have hS : matrixFrobeniusSq J=(n : ℝ)^2 := by simp [matrixFrobeniusSq,J]; ring
  have hupper := euclideanOperatorNorm_le_frobenius J
  rw [hS,Real.sqrt_sq (Nat.cast_nonneg n)] at hupper
  have hsum : (∑ i : Fin n,∑ j : Fin n,J i j)=(n : ℂ)^2 := by simp [J]; ring
  have hlower := matrix_sum_norm_le_operator J
  rw [hsum,norm_pow,Complex.norm_natCast] at hlower
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  change euclideanOperatorNorm J=(n : ℝ)
  nlinarith

theorem rhoFourth_one_iff_four_phase_gauge {n : ℕ} (hn : 0<n)
    (F : Matrix (Fin n) (Fin n) ℂ) (hF : ∀ i j, ‖F i j‖=1) :
    rhoFourth F=1 ↔ HasFourPhaseGauge F := by
  constructor
  · intro hrho
    have hD : fourthGramDeficit F=0 := by
      have hb := fourthGramDeficit_rho_bound hn F
      rw [hrho] at hb
      norm_num at hb
      exact le_antisymm hb (fourthGramDeficit_nonneg F hF)
    obtain ⟨k,l,hkl⟩ := exists_pivot_fourth_error_le hn F hF
    simp only [hD,mul_zero,zero_div] at hkl
    have hroots (i j : Fin n) : IsFourthRoot (pivotDephase F k l i j) := by
      have hi : (∑ a,Complex.normSq ((pivotDephase F k l i a)^4-1)) ≤ pivotFourthError F k l := by
        unfold pivotFourthError
        exact Finset.single_le_sum (s := Finset.univ)
          (f := fun r : Fin n => ∑ a : Fin n,Complex.normSq ((pivotDephase F k l r a)^4-1))
          (fun r hr => Finset.sum_nonneg (fun a ha => Complex.normSq_nonneg ((pivotDephase F k l r a)^4-1))) (Finset.mem_univ i)
      have hj : Complex.normSq ((pivotDephase F k l i j)^4-1) ≤ ∑ a,Complex.normSq ((pivotDephase F k l i a)^4-1) :=
        Finset.single_le_sum (s := Finset.univ)
          (f := fun a : Fin n => Complex.normSq ((pivotDephase F k l i a)^4-1))
          (fun a ha => Complex.normSq_nonneg ((pivotDephase F k l i a)^4-1)) (Finset.mem_univ j)
      have hz : Complex.normSq ((pivotDephase F k l i j)^4-1)=0 :=
        le_antisymm (by linarith) (Complex.normSq_nonneg _)
      apply (fourth_root_iff _).mpr
      exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp hz)
    exact (four_phase_gauge_iff_cross_ratios F hF k l).mpr
      ((fourth_power_cross_ratio_criterion F hF k l).mp hroots)
  · rintro ⟨r,c,hr,hc,hQ⟩
    have he : fourthPowerMatrix (phaseTransform F r c)=(fun _ _ : Fin n => (1 : ℂ)) := by
      ext i j
      exact (fourth_root_iff _).mp (hQ i j)
    have hnorm : rhoFourth (phaseTransform F r c)=1 := by
      unfold rhoFourth
      rw [he,ones_euclideanOperatorNorm hn]
      exact div_self (by exact_mod_cast (Nat.ne_of_gt hn))
    rwa [rhoFourth_phase_invariant F r c hr hc] at hnorm

theorem rhoFourth_one_iff_quaternary_phase_equivalent {n : ℕ} (hn : 0<n)
    (F : Matrix (Fin n) (Fin n) ℂ) (hF : ∀ i j, ‖F i j‖=1)
    (horth : ∀ i k,complexRowGram F i k=if i=k then (n : ℂ) else 0) :
    rhoFourth F=1 ↔ ∃ r c : Fin n → ℂ,(∀ i,‖r i‖=1) ∧ (∀ j,‖c j‖=1) ∧
      IsQuaternaryHadamard (phaseTransform F r c) := by
  constructor
  · intro hrho
    let k : Fin n := ⟨0,hn⟩
    have hg := (rhoFourth_one_iff_four_phase_gauge hn F hF).mp hrho
    have hcross := (four_phase_gauge_iff_cross_ratios F hF k k).mp hg
    have hroot := (fourth_power_cross_ratio_criterion F hF k k).mpr hcross
    let r : Fin n → ℂ := fun i => conj (F i k)
    let c : Fin n → ℂ := fun j => conj (F k j)*F k k
    refine ⟨r,c,?_,?_,?_⟩
    · intro i; simpa [r] using hF i k
    · intro j; simp [c,norm_mul,hF]
    · have he : phaseTransform F r c=(fun i j => pivotDephase F k k i j) := by
        ext i j
        unfold phaseTransform pivotDephase r c
        ring
      rw [he]
      refine ⟨hroot,?_⟩
      intro i j
      have ho : ∀ i j,(∑ a,F i a*conj (F j a))=if i=j then (n : ℂ) else 0 := horth
      exact pivotDephase_hadamard_gram F hF ho k k i j
  · rintro ⟨r,c,hr,hc,hQ⟩
    exact (rhoFourth_one_iff_four_phase_gauge hn F hF).mpr ⟨r,c,hr,hc,hQ.1⟩
end PhaseGeometry
