/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.ExchangeBudget
public import CompletionTheory.RepetitionObstruction
public import CompletionTheory.InformationCoordinates
public import CompletionTheory.TensorExchange
@[expose] public section
namespace CompletionTheory
open Matrix

noncomputable def supportedSigns {κ : Type*} [DecidableEq κ]
    (w : κ → ℝ) (T : Finset κ) : κ → ℝ := fun j => if j ∈ T then w j else 0

theorem supportedSigns_dot {κ : Type*} [Fintype κ] [DecidableEq κ]
    (p w : κ → ℝ) (T : Finset κ) :
    (∑ j, p j * supportedSigns w T j) = ∑ j : T, p j.val * w j.val := by
  classical
  simp only [supportedSigns, mul_ite, mul_zero]
  rw [Finset.sum_ite_mem]
  simpa only [Finset.univ_inter] using (Finset.sum_coe_sort T (fun j => p j * w j)).symm

theorem supportedSigns_norm {κ : Type*} [Fintype κ] [DecidableEq κ]
    (w : κ → ℝ) (hw : IsCubeVector w) (T : Finset κ) :
    (∑ j, supportedSigns w T j ^ 2) = T.card := by
  classical
  have ht (j : κ) : supportedSigns w T j ^ 2 = if j ∈ T then 1 else 0 := by
    by_cases h : j ∈ T
    · simp only [supportedSigns, if_pos h]
      exact isSign_sq (hw j)
    · simp [supportedSigns, h]
  simp_rw [ht]
  simp

theorem supportedSigns_dot_isSign {κ : Type*} (p w : κ → ℝ)
    (hp : IsCubeVector p) (hw : IsCubeVector w) (j : κ) : IsSign (p j * w j) := by
  rcases hp j with h | h <;> rcases hw j with h' | h' <;> simp [h, h', IsSign]

theorem supportedSigns_odd_dot_ne_zero {κ : Type*} [Fintype κ] [DecidableEq κ]
    (p w : κ → ℝ) (hp : IsCubeVector p) (hw : IsCubeVector w)
    (T : Finset κ) (ht : Odd T.card) : (∑ j, p j * supportedSigns w T j) ≠ 0 := by
  intro hz
  rw [supportedSigns_dot] at hz
  have he := sign_sum_zero_even (fun j : T => p j.val * w j.val)
    (fun j => supportedSigns_dot_isSign p w hp hw j.val) hz
  have he' : Even T.card := by simpa using he
  exact (Nat.not_even_iff_odd.mpr ht) he'

theorem supportedSigns_even_dot_sq {κ : Type*} [Fintype κ] [DecidableEq κ]
    (p w : κ → ℝ) (hp : IsCubeVector p) (hw : IsCubeVector w)
    (T : Finset κ) (ht : Even T.card)
    (hne : (∑ j, p j * supportedSigns w T j) ≠ 0) :
    4 ≤ (∑ j, p j * supportedSigns w T j) ^ 2 := by
  have he : Even (Fintype.card T) := by simpa using ht
  obtain ⟨z, hz⟩ := sign_sum_even he (fun j : T => p j.val * w j.val)
    (fun j => supportedSigns_dot_isSign p w hp hw j.val)
  rw [supportedSigns_dot, hz] at hne ⊢
  have hzn : z ≠ 0 := by intro h; simp [h] at hne
  have hcases : z ≤ -1 ∨ 1 ≤ z := by omega
  rcases hcases with h | h
  · have hr : (z : ℝ) ≤ -1 := by exact_mod_cast h
    nlinarith [sq_nonneg ((z : ℝ) + 1)]
  · have hr : (1 : ℝ) ≤ z := by exact_mod_cast h
    nlinarith [sq_nonneg ((z : ℝ) - 1)]

theorem supportedSigns_even_bad_row_bound {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P)
    (w : κ → ℝ) (hw : IsCubeVector w) (T : Finset κ) (ht : Even T.card) :
    4 * ((Finset.univ.filter (fun i => (∑ j, P i j * supportedSigns w T j) ≠ 0)).card : ℝ) ≤
      (Fintype.card κ : ℝ) * T.card := by
  classical
  let D := Finset.univ.filter (fun i => (∑ j, P i j * supportedSigns w T j) ≠ 0)
  have hlower : 4 * (D.card : ℝ) ≤ ∑ i, (∑ j, P i j * supportedSigns w T j) ^ 2 := by
    calc
      _ = ∑ i ∈ D, (4 : ℝ) := by simp [mul_comm]
      _ ≤ ∑ i ∈ D, (∑ j, P i j * supportedSigns w T j) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact supportedSigns_even_dot_sq (P i) w (hP.1 i) hw T ht
          (Finset.mem_filter.mp hi).2
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ D)
        (fun i _ _ => sq_nonneg _)
  have hn : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  have hb := rowGram_bessel P _ hn hP.2 (supportedSigns w T)
  rw [supportedSigns_norm w hw T] at hb
  exact hlower.trans hb

noncomputable def roundedSign {κ : Type*} (v : κ → ℝ) : κ → ℝ :=
  fun j => if 0 < v j then 1 else -1

noncomputable def tripleCoordinates {κ : Type*} [Fintype κ] (v : κ → ℝ) : Finset κ :=
  Finset.univ.filter (fun j => v j = 3 ∨ v j = -3)

noncomputable def roundingBadRows {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Matrix ι κ ℝ) (v : κ → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => (∑ j, P i j * roundedSign v j) ≠ 0)

theorem roundedSign_isCube {κ : Type*} (v : κ → ℝ) : IsCubeVector (roundedSign v) := by
  intro j
  unfold roundedSign
  split_ifs <;> simp

theorem rounding_reconstruction {κ : Type*} [Fintype κ] [DecidableEq κ]
    (v : κ → ℝ) (hv : ∀ j, v j = 1 ∨ v j = -1 ∨ v j = 3 ∨ v j = -3) (j : κ) :
    v j = roundedSign v j + 2 * supportedSigns (roundedSign v) (tripleCoordinates v) j := by
  rcases hv j with h | h | h | h <;>
    norm_num [roundedSign, supportedSigns, tripleCoordinates, h]

theorem rounding_kernel_dot {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (P : Matrix ι κ ℝ) (v : κ → ℝ)
    (hv : ∀ j, v j = 1 ∨ v j = -1 ∨ v j = 3 ∨ v j = -3)
    (hker : P.mulVec v = 0) (i : ι) :
    (∑ j, P i j * roundedSign v j) =
      -2 * (∑ j, P i j * supportedSigns (roundedSign v) (tripleCoordinates v) j) := by
  have hz : (∑ j, P i j * v j) = 0 := congrFun hker i
  have ht (j : κ) : P i j * v j = P i j * roundedSign v j +
      2 * (P i j * supportedSigns (roundedSign v) (tripleCoordinates v) j) := by
    conv_lhs => rw [rounding_reconstruction v hv j]
    ring
  simp_rw [ht] at hz
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hz
  linarith

theorem rounding_defect {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (v : κ → ℝ)
    (hv : ∀ j, v j = 1 ∨ v j = -1 ∨ v j = 3 ∨ v j = -3)
    (hker : P.mulVec v = 0) :
    IsCubeVector (roundedSign v) ∧
    (∀ j, v j = roundedSign v j + 2 * supportedSigns (roundedSign v) (tripleCoordinates v) j) ∧
    (∀ i, (∑ j, P i j * roundedSign v j) =
      -2 * (∑ j, P i j * supportedSigns (roundedSign v) (tripleCoordinates v) j)) ∧
    (Odd (tripleCoordinates v).card → ∀ i, (∑ j, P i j * roundedSign v j) ≠ 0) ∧
    (Even (tripleCoordinates v).card →
      4 * ((roundingBadRows P v).card : ℝ) ≤ (Fintype.card κ : ℝ) * (tripleCoordinates v).card) ∧
    (roundingBadRows P v).card ≤ Fintype.card ι ∧
    (∀ i, i ∉ roundingBadRows P v → (∑ j, P i j * roundedSign v j) = 0) := by
  classical
  have hw := roundedSign_isCube v
  have hdot := rounding_kernel_dot P v hv hker
  refine ⟨hw, rounding_reconstruction v hv, hdot, ?_, ?_, ?_, ?_⟩
  · intro ht i hz
    have hn := supportedSigns_odd_dot_ne_zero (P i) (roundedSign v) (hP.1 i) hw
      (tripleCoordinates v) ht
    have hh := hdot i
    apply hn
    linarith
  · intro ht
    have heq : roundingBadRows P v = Finset.univ.filter
        (fun i => (∑ j, P i j * supportedSigns (roundedSign v) (tripleCoordinates v) j) ≠ 0) := by
      ext i
      simp only [roundingBadRows, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hdot i]
      simp
    rw [heq]
    exact supportedSigns_even_bad_row_bound P hP (roundedSign v) hw (tripleCoordinates v) ht
  · exact (Finset.card_filter_le _ _).trans_eq (Finset.card_univ)
  · intro i hi
    simpa only [roundingBadRows, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hi

theorem rounding_defect_bound {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (v : κ → ℝ)
    (hv : ∀ j, v j = 1 ∨ v j = -1 ∨ v j = 3 ∨ v j = -3)
    (hker : P.mulVec v = 0) (ht : Even (tripleCoordinates v).card) :
    ((roundingBadRows P v).card : ℝ) ≤
      min (Fintype.card ι : ℝ) ((Fintype.card κ : ℝ) * (tripleCoordinates v).card / 4) := by
  obtain ⟨_, _, _, _, heven, hcard, _⟩ := rounding_defect P hP v hv hker
  apply le_min
  · exact_mod_cast hcard
  · have hb := heven ht
    linarith

theorem rounded_row_repair {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (v : κ → ℝ) :
    IsPartialHadamard (exchangeFrame P (roundingBadRows P v)
      (fun (_i : Fin 1) j => roundedSign v j)) := by
  classical
  have hw := roundedSign_isCube v
  have hnorm : (∑ j, roundedSign v j ^ 2) = (Fintype.card κ : ℝ) := by
    simp_rw [isSign_sq (hw _)]
    simp
  let V : Matrix (Fin 1) κ ℝ := fun _i j => roundedSign v j
  have hV : IsPartialHadamard V := by
    constructor
    · intro i j; exact hw j
    · ext i j
      fin_cases i
      fin_cases j
      rw [@Matrix.mul_apply _ _ _ ℝ inferInstance Real.instMul Real.instAddCommMonoid]
      simp only [Matrix.transpose_apply]
      simpa [V, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, pow_two] using hnorm
  apply exchangeFrame_partialHadamard P (roundingBadRows P v) V hP hV
  intro i hi a
  simpa only [roundingBadRows, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hi

end CompletionTheory
