/- Copyright (c) 2026 Joshua Mark. Apache-2.0. -/
module
public import CompletionTheory.ExchangeBudget
public import CompletionTheory.RepetitionObstruction
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
@[expose] public section
namespace CompletionTheory
open Matrix

/-- Exact odd-block exchange bound and its ceiling deletion requirement. -/
theorem odd_block_exchange_budget {ι κ τ : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype κ]
    [Fintype τ] [DecidableEq τ]
    (hodd : Odd (Fintype.card κ)) (hs : 1 < Fintype.card κ)
    (K : Matrix ι ι ℝ) (hK : IsHadamard K)
    (Q : Matrix τ (ι × κ) ℝ) (S : Finset ι)
    (hA : IsPartialHadamard (retainAndInsert (fun i (j : ι × κ) => K i j.1) Q S)) :
    (Fintype.card τ : ℝ) ≤ (Sᶜ.card : ℝ) * (Fintype.card κ : ℝ)^2 ∧
    (S.card + Fintype.card τ = Fintype.card ι * Fintype.card κ →
      ⌈(Fintype.card ι : ℝ) / ((Fintype.card κ : ℝ)+1)⌉₊ ≤ Sᶜ.card) := by
  classical
  haveI : Nonempty κ := Fintype.card_pos_iff.mp (by omega)
  let P : Matrix ι (ι × κ) ℝ := fun i j => K i j.1
  let j₀ : ι := Classical.choice inferInstance
  let f : (ι × κ) → ℤ := fun j => if j.1 = j₀ then 1 else 0
  have hfval : (∑ j, f j) = (Fintype.card κ : ℤ) := by
    change (∑ j : ι × κ, if j.1 = j₀ then (1:ℤ) else 0) = _
    rw [Fintype.sum_prod_type]
    calc
      (∑ i : ι, ∑ _ : κ, if i=j₀ then (1:ℤ) else 0) =
          ∑ i : ι, if i=j₀ then (Fintype.card κ : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases h : i=j₀ <;> simp [h]
      _ = _ := by simp
  have hf : Odd (∑ j, f j) := by
    rw [hfval]
    obtain ⟨k,hk⟩ := hodd
    exact ⟨(k : ℤ),by exact_mod_cast hk⟩
  have hdot (i : ι) : (∑ j, P i j * (f j : ℝ)) =
      (Fintype.card κ : ℝ) * K i j₀ := by
    simp [P,f,Fintype.sum_prod_type,mul_ite,Finset.mul_sum,Finset.sum_mul,mul_comm]
  have hnorm : (∑ j, (f j : ℝ)^2) = (Fintype.card κ : ℝ) := by
    have hh (j : ι × κ) : (f j : ℝ)^2 = (f j : ℝ) := by
      dsimp [f]
      split_ifs <;> norm_num
    calc
      (∑ j, (f j : ℝ)^2) = ∑ j, (f j : ℝ) := Finset.sum_congr rfl (fun j _ => hh j)
      _ = ((∑ j, f j) : ℤ) := by simp
      _ = _ := by rw [hfval]; simp
  have hsq (i : ι) : K i j₀ ^ 2 = 1 := isSign_sq (hK.1 i j₀)
  have hbudget : witnessBudget P f = 0 := by
    simp [witnessBudget,hdot,hnorm,mul_pow,hsq,Fintype.card_prod]
    ring
  have hdeleted : (∑ i ∈ Sᶜ, (∑ j, P i j * (f j : ℝ))^2) =
      (Sᶜ.card : ℝ) * (Fintype.card κ : ℝ)^2 := by
    simp [hdot,mul_pow,hsq]
  have hb := (weighted_odd_witness_budget P Q S
    (repetition_partialHadamard K hK) hA f hf).2.1
  rw [hbudget,hdeleted,zero_add] at hb
  refine ⟨hb,?_⟩
  intro hfull
  have hfull' : (S.card : ℝ)+(Fintype.card τ : ℝ) =
      (Fintype.card ι : ℝ)*(Fintype.card κ : ℝ) := by exact_mod_cast hfull
  have hcards : (S.card : ℝ)+(Sᶜ.card : ℝ) = (Fintype.card ι : ℝ) := by
    exact_mod_cast Finset.card_add_card_compl S
  have hs' : (1 : ℝ) < Fintype.card κ := by exact_mod_cast hs
  have hmul : (Fintype.card ι : ℝ)*((Fintype.card κ : ℝ)-1) ≤
      ((Sᶜ.card : ℝ)*((Fintype.card κ : ℝ)+1))*((Fintype.card κ : ℝ)-1) := by
    nlinarith [hb]
  have hbound : (Fintype.card ι : ℝ) ≤
      (Sᶜ.card : ℝ)*((Fintype.card κ : ℝ)+1) :=
    (mul_le_mul_iff_left₀ (by linarith : (0 : ℝ) < (Fintype.card κ : ℝ)-1)).mp hmul
  apply Nat.ceil_le.mpr
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < (Fintype.card κ : ℝ)+1)).mpr hbound

end CompletionTheory
