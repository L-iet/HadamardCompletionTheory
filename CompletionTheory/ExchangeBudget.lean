/- Copyright (c) 2026 Joshua Mark. Apache-2.0. -/
module
public import CompletionTheory.CodimensionTwo
@[expose] public section
namespace CompletionTheory
open Matrix

/-- Bessel's inequality in the exact scaled row-Gram form used by the budget results. -/
theorem rowGram_bessel {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (P : Matrix ι κ ℝ) (N : ℝ) (hN : 0 < N) (hP : P * Pᵀ = N • 1)
    (f : κ → ℝ) :
    (∑ i, (∑ j, P i j * f j)^2) ≤ N * ∑ j, (f j)^2 := by
  classical
  let v : ι → EuclideanSpace ℝ κ :=
    fun i => WithLp.toLp 2 (fun j => P i j / Real.sqrt N)
  let x : EuclideanSpace ℝ κ := WithLp.toLp 2 f
  have hs : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN.le
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    have hg := congrArg (fun M => M j i) hP
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul] at hg
    simp only [v, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      div_mul_div_comm, ← Finset.sum_div]
    rw [hs, hg]
    by_cases hij : i = j
    · subst j; simp [ne_of_gt hN]
    · simp [hij, Ne.symm hij]
  have hi (i : ι) : inner ℝ (v i) x = (∑ j, P i j * f j) / Real.sqrt N := by
    change (∑ j, f j * (P i j / Real.sqrt N)) = _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hb := hv.sum_inner_products_le (s := Finset.univ) x
  simp only [hi, Real.norm_eq_abs, sq_abs,
    EuclideanSpace.real_norm_sq_eq, x] at hb
  simp_rw [div_pow, Real.sq_sqrt hN.le] at hb
  rw [← Finset.sum_div] at hb
  simpa only [mul_comm] using (div_le_iff₀ hN).mp hb


/-- Dotting a sign row with an integer odd-sum vector gives an odd integer. -/
theorem sign_odd_dot {κ : Type*} [Fintype κ]
    (p : κ → ℝ) (hp : ∀ j, IsSign (p j))
    (f : κ → ℤ) (hf : Odd (∑ j, f j)) :
    ∃ z : ℤ, Odd z ∧ (∑ j, p j * (f j : ℝ)) = z := by
  classical
  let d : ℤ := ∑ j, if p j = -1 then f j else 0
  let z : ℤ := (∑ j, f j) - 2*d
  have hzodd : Odd z := by
    obtain ⟨k,hk⟩ := hf
    refine ⟨k-d, ?_⟩
    dsimp [z]
    omega
  refine ⟨z, hzodd, ?_⟩
  have hterm : ∀ j, p j * (f j : ℝ) =
      (f j : ℝ) - 2 * (if p j = -1 then (f j : ℝ) else 0) := by
    intro j
    rcases hp j with h | h <;> norm_num [h] <;> ring
  calc
    (∑ j, p j * (f j : ℝ)) = ∑ j, ((f j : ℝ)-2*(if p j = -1 then (f j : ℝ) else 0)) :=
      Finset.sum_congr rfl (fun j _ => hterm j)
    _ = (z : ℝ) := by simp [z,d,Finset.sum_sub_distrib,Finset.mul_sum]

theorem sign_odd_dot_sq {κ : Type*} [Fintype κ]
    (p : κ → ℝ) (hp : ∀ j, IsSign (p j))
    (f : κ → ℤ) (hf : Odd (∑ j, f j)) :
    1 ≤ (∑ j, p j * (f j : ℝ))^2 := by
  obtain ⟨z, hz, he⟩ := sign_odd_dot p hp f hf
  rw [he]
  obtain ⟨k,hk⟩ := hz
  have hcases : z ≤ -1 ∨ 1 ≤ z := by omega
  rcases hcases with hlo | hhi
  · have h : (z : ℝ) ≤ -1 := by exact_mod_cast hlo
    nlinarith [sq_nonneg ((z : ℝ)+1)]
  · have h : (1 : ℝ) ≤ z := by exact_mod_cast hhi
    nlinarith [sq_nonneg ((z : ℝ)-1)]

/-- Retain exactly the indicated original rows and insert an arbitrary new family. -/
def retainAndInsert {ι κ τ : Type*} (P : Matrix ι κ ℝ) (Q : Matrix τ κ ℝ)
    (S : Finset ι) : Matrix (↥S ⊕ τ) κ ℝ :=
  fun i j => Sum.elim (fun k : S => P k.val j) (fun k => Q k j) i


/-- Residual quadratic energy of an integer witness. -/
def witnessBudget {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Matrix ι κ ℝ) (f : κ → ℤ) : ℝ :=
  (Fintype.card κ : ℝ) * (∑ j, (f j : ℝ)^2) -
    ∑ i, (∑ j, P i j * (f j : ℝ))^2


/-- The scalar budget equals the residual Gram quadratic form exactly. -/
theorem witnessBudget_eq_residual {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (P : Matrix ι κ ℝ) (f : κ → ℤ) :
    witnessBudget P f = dotProduct (fun j => (f j : ℝ))
      (((Fintype.card κ : ℝ) • (1 : Matrix κ κ ℝ) - Pᵀ * P).mulVec
        (fun j => (f j : ℝ))) := by
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_smul, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec]
  simp [witnessBudget, dotProduct, Matrix.mulVec, pow_two]

/-- The full weighted odd-witness row-exchange budget, including the completion consequence. -/
theorem weighted_odd_witness_budget {ι κ τ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ]
    [Fintype τ] [DecidableEq τ]
    (P : Matrix ι κ ℝ) (Q : Matrix τ κ ℝ) (S : Finset ι)
    (hP : IsPartialHadamard P) (hA : IsPartialHadamard (retainAndInsert P Q S))
    (f : κ → ℤ) (hf : Odd (∑ j, f j)) :
    0 ≤ witnessBudget P f ∧
    (Fintype.card τ : ℝ) ≤ witnessBudget P f +
      ∑ i ∈ Sᶜ, (∑ j, P i j * (f j : ℝ))^2 ∧
    (S.card + Fintype.card τ = Fintype.card κ →
      (Fintype.card κ : ℝ) - Fintype.card ι - witnessBudget P f ≤
        ∑ i ∈ Sᶜ, ((∑ j, P i j * (f j : ℝ))^2 - 1)) := by
  classical
  have hN : (0 : ℝ) < Fintype.card κ := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card κ)
  have hp := rowGram_bessel P (Fintype.card κ) hN hP.2 (fun j => (f j : ℝ))
  have ha := rowGram_bessel (retainAndInsert P Q S) (Fintype.card κ) hN hA.2
    (fun j => (f j : ℝ))
  simp only [Fintype.sum_sum_type, retainAndInsert, Sum.elim_inl, Sum.elim_inr] at ha
  have hq : (Fintype.card τ : ℝ) ≤ ∑ i : τ, (∑ j, Q i j * (f j : ℝ))^2 := by
    calc
      (Fintype.card τ : ℝ) = ∑ _ : τ, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => sign_odd_dot_sq (Q i)
        (fun j => by simpa only [retainAndInsert, Sum.elim_inr] using hA.1 (Sum.inr i) j) f hf)
  have hs : (∑ i : S, (∑ j, P i.val j * (f j : ℝ))^2) =
      ∑ i ∈ S, (∑ j, P i j * (f j : ℝ))^2 := Finset.sum_coe_sort S (fun i => (∑ j, P i j * (f j : ℝ))^2)
  rw [hs] at ha
  have hsplit := Finset.sum_add_sum_compl S (fun i => (∑ j, P i j * (f j : ℝ))^2)
  have hbudget : (Fintype.card τ : ℝ) ≤ witnessBudget P f +
      ∑ i ∈ Sᶜ, (∑ j, P i j * (f j : ℝ))^2 := by
    dsimp [witnessBudget]
    linarith
  refine ⟨by dsimp [witnessBudget]; linarith, hbudget, ?_⟩
  intro hfull
  have hfull' : (S.card : ℝ) + Fintype.card τ = Fintype.card κ := by exact_mod_cast hfull
  have hcards : (S.card : ℝ) + Sᶜ.card = Fintype.card ι := by
    exact_mod_cast Finset.card_add_card_compl S
  have hsum : (∑ i ∈ Sᶜ, ((∑ j, P i j * (f j : ℝ))^2-1)) =
      (∑ i ∈ Sᶜ, (∑ j, P i j * (f j : ℝ))^2) - Sᶜ.card := by
    simp [Finset.sum_sub_distrib]
  rw [hsum]
  linarith

end CompletionTheory
