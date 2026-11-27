/- Copyright (c) 2026 Joshua Mark. Apache-2.0. -/
module
public import CompletionTheory.CodimensionTwo
@[expose] public section
namespace CompletionTheory
open Matrix

/-- Vanishing sums of real signs have even cardinality. -/
theorem sign_sum_zero_even {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (hf : ∀ i, IsSign (f i)) (hzero : ∑ i, f i = 0) :
    Even (Fintype.card ι) := by
  classical
  let d : ℕ := ∑ i, if f i = -1 then 1 else 0
  have hd : (d : ℝ) = ∑ i, if f i = -1 then (1 : ℝ) else 0 := by simp [d]
  have hterm : ∀ i, f i = 1 - 2 * (if f i = -1 then (1 : ℝ) else 0) := by
    intro i
    rcases hf i with h | h <;> norm_num [h]
  have heq : (Fintype.card ι : ℝ) = 2*d := by
    have hh : (∑ i, f i) = (Fintype.card ι : ℝ) - 2*d := by
      calc
        (∑ i, f i) = ∑ i, (1-2*(if f i = -1 then (1:ℝ) else 0)) :=
          Finset.sum_congr rfl (fun i _ => hterm i)
        _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hd]; simp
    linarith
  refine ⟨d, ?_⟩
  have hn : Fintype.card ι = 2*d := by exact_mod_cast heq
  omega


/-- Repetition preserves the exact partial-Hadamard Gram identity. -/
theorem repetition_partialHadamard {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (K : Matrix ι ι ℝ) (hK : IsHadamard K) :
    IsPartialHadamard (fun i (j : ι × κ) => K i j.1) := by
  constructor
  · intro i j
    exact hK.1 i j.1
  · ext i j
    have hg := congrArg (fun M => M i j) hK.2
    change (∑ k : ι × κ, K i k.1 * K j k.1) =
      (Fintype.card (ι × κ) : ℝ) * (if i = j then 1 else 0)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul] at hg ⊢
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul]
    rw [← Finset.mul_sum, hg]
    ring

/-- Repeating each column an odd number of times leaves no orthogonal sign row. -/
theorem odd_repetition_unextendible {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype κ]
    (hodd : Odd (Fintype.card κ)) (K : Matrix ι ι ℝ) (hK : IsHadamard K) :
    ¬ ∃ f : (ι × κ) → ℝ, (∀ j, IsSign (f j)) ∧
      (∀ i, ∑ j : ι × κ, K i j.1 * f j = 0) := by
  classical
  rintro ⟨f, hf, horth⟩
  let v : ι → ℝ := fun j => ∑ k, f (j,k)
  have hkv : K.mulVec v = 0 := by
    ext i
    simpa only [Matrix.mulVec, dotProduct, v, Finset.mul_sum,
      Fintype.sum_prod_type, Pi.zero_apply] using horth i
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  let M : Matrix ι ι ℝ := (Fintype.card ι : ℝ)⁻¹ • Kᵀ
  have hKM : K * M = 1 := by
    simp [M, Matrix.mul_smul, hK.2, smul_smul, hcard]
  have hMK : M * K = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hKM
  have hv : v = 0 := by
    have h := congrArg (fun x => M.mulVec x) hkv
    simpa only [Matrix.mulVec_mulVec, hMK, Matrix.one_mulVec, Matrix.mulVec_zero] using h
  let j : ι := Classical.choice inferInstance
  have hsum : ∑ k, f (j,k) = 0 := congrFun hv j
  have heven := sign_sum_zero_even (fun k => f (j,k)) (fun k => hf (j,k)) hsum
  exact (Nat.not_even_iff_odd.mpr hodd) heven


/-- A fixed Sylvester seed for the four-by-twelve obstruction. -/
def seedFour : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,1,1,1; 1,-1,1,-1; 1,1,-1,-1; 1,-1,-1,1]

theorem seedFour_hadamard : IsHadamard seedFour := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [seedFour, IsSign]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [seedFour, Matrix.mul_apply, Fin.sum_univ_succ]

/-- An explicit order-twelve Paley matrix; every entry and Gram entry is checked. -/
def seedTwelve : Matrix (Fin 12) (Fin 12) ℝ :=
  !![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1;
      -1, 1, 1, -1, 1, 1, 1, -1, -1, -1, 1, -1;
      -1, -1, 1, 1, -1, 1, 1, 1, -1, -1, -1, 1;
      -1, 1, -1, 1, 1, -1, 1, 1, 1, -1, -1, -1;
      -1, -1, 1, -1, 1, 1, -1, 1, 1, 1, -1, -1;
      -1, -1, -1, 1, -1, 1, 1, -1, 1, 1, 1, -1;
      -1, -1, -1, -1, 1, -1, 1, 1, -1, 1, 1, 1;
      -1, 1, -1, -1, -1, 1, -1, 1, 1, -1, 1, 1;
      -1, 1, 1, -1, -1, -1, 1, -1, 1, 1, -1, 1;
      -1, 1, 1, 1, -1, -1, -1, 1, -1, 1, 1, -1;
      -1, -1, 1, 1, 1, -1, -1, -1, 1, -1, 1, 1;
      -1, 1, -1, 1, 1, 1, -1, -1, -1, 1, -1, 1]

set_option maxHeartbeats 2000000 in
theorem seedTwelve_hadamard : Matrix.IsHadamard seedTwelve := by
  apply isHadamard_mathlib
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [seedTwelve, IsSign]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [seedTwelve, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Eight missing rows do not suffice for completion, even at an existing Hadamard order. -/
theorem eight_missing_rows_obstruction :
    (∃ X : Matrix (Fin 4) (Fin 4 × Fin 3) ℝ,
      IsPartialHadamard X ∧
      ¬ ∃ f : (Fin 4 × Fin 3) → ℝ, (∀ j, IsSign (f j)) ∧
        (∀ i, ∑ j : Fin 4 × Fin 3, X i j * f j = 0)) ∧
    (∃ H : Matrix (Fin 12) (Fin 12) ℝ, Matrix.IsHadamard H) := by
  refine ⟨⟨(fun i j => seedFour i j.1), repetition_partialHadamard seedFour seedFour_hadamard, ?_⟩,
    ⟨seedTwelve, seedTwelve_hadamard⟩⟩
  exact odd_repetition_unextendible (κ := Fin 3) (by exact ⟨1,rfl⟩)
    seedFour seedFour_hadamard

end CompletionTheory
