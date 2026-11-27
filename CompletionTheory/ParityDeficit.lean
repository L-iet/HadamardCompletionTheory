/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0; see LICENSE.
Exact modulo-eight odd-witness obstruction and its sharp defect-eight threshold. -/
module
public import CompletionTheory.ExchangeBudget
public import CompletionTheory.RepetitionObstruction
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Tactic.Choose
@[expose] public section
namespace CompletionTheory
open Matrix

theorem odd_square_eight (z : ℤ) (hz : Odd z) : ∃ b : ℤ, z^2=1+8*b := by
  obtain ⟨k,hk⟩ := hz
  obtain ⟨b,hb⟩ := Int.even_mul_succ_self k
  exact ⟨b,by rw [hk]; nlinarith⟩

theorem odd_sum_squares {κ : Type*} [Fintype κ]
    (f : κ → ℤ) (hf : Odd (∑ j, f j)) : Odd (∑ j, (f j)^2) := by
  classical
  have hcoord (j) : ∃ b : ℤ, (f j)^2=f j+2*b := by
    obtain ⟨b,hb⟩ := Int.even_mul_pred_self (f j)
    exact ⟨b,by nlinarith⟩
  choose b hb using hcoord
  have hsum : (∑ j, (f j)^2)=(∑ j, f j)+2*(∑ j, b j) := by
    simp_rw [hb]
    simp [Finset.sum_add_distrib,Finset.mul_sum]
  obtain ⟨k,hk⟩ := hf
  exact ⟨k+∑ j, b j,by omega⟩

theorem witnessBudget_mod_eight {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Matrix ι κ ℝ) (hP : IsSignMatrix P)
    (f : κ → ℤ) (hf : Odd (∑ j, f j)) (hdiv : 4 ∣ Fintype.card κ) :
    ∃ t : ℤ, witnessBudget P f = (Fintype.card κ : ℝ)-Fintype.card ι+8*t := by
  classical
  choose z hz using (fun i => sign_odd_dot (P i) (hP i) f hf)
  choose b hb using (fun i => odd_square_eight (z i) (hz i).1)
  obtain ⟨a,ha⟩ := odd_sum_squares f hf
  obtain ⟨m,hm⟩ := hdiv
  refine ⟨(m : ℤ)*a-∑ i, b i,?_⟩
  have hnorm : (∑ j, (f j : ℝ)^2)=2*(a : ℝ)+1 := by exact_mod_cast ha
  have hzi (i) : (∑ j, P i j * (f j : ℝ))^2=1+8*(b i : ℝ) := by
    rw [(hz i).2]
    exact_mod_cast hb i
  have hsum : (∑ i, (∑ j, P i j*(f j : ℝ))^2)=
      (Fintype.card ι : ℝ)+8*(∑ i, (b i : ℝ)) := by
    simp_rw [hzi]
    simp [Finset.sum_add_distrib,Finset.mul_sum]
  have hm' : (Fintype.card κ : ℝ)=4*(m : ℝ) := by exact_mod_cast hm
  unfold witnessBudget
  rw [hnorm,hsum,hm']
  push_cast
  ring


theorem small_defect_budget {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [Nonempty κ] (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P)
    (f : κ → ℤ) (hf : Odd (∑ j, f j)) (hdiv : 4 ∣ Fintype.card κ)
    (d : ℕ) (hd : d ≤ 7) (hcard : Fintype.card κ=Fintype.card ι+d) :
    (d : ℝ) ≤ witnessBudget P f := by
  have hN : (0 : ℝ) < Fintype.card κ := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card κ)
  have hp := rowGram_bessel P (Fintype.card κ) hN hP.2 (fun j => (f j : ℝ))
  have hnonneg : 0 ≤ witnessBudget P f := by dsimp [witnessBudget]; linarith
  obtain ⟨t,ht⟩ := witnessBudget_mod_eight P hP.1 f hf hdiv
  have hcard' : (Fintype.card κ : ℝ) = (Fintype.card ι : ℝ)+d := by exact_mod_cast hcard
  have hd' : (d : ℝ) ≤ 7 := by exact_mod_cast hd
  have htpos : (0 : ℤ) ≤ t := by
    by_contra h
    have hle : t ≤ -1 := by omega
    have hle' : (t : ℝ) ≤ -1 := by exact_mod_cast hle
    nlinarith
  have htpos' : (0 : ℝ) ≤ t := by exact_mod_cast htpos
  nlinarith

theorem defect_eight_zero :
    ∃ (P : Matrix (Fin 4) (Fin 4 × Fin 3) ℝ) (f : (Fin 4 × Fin 3) → ℤ),
      IsPartialHadamard P ∧ Odd (∑ j, f j) ∧ witnessBudget P f=0 := by
  refine ⟨(fun i j => seedFour i j.1),(fun j => if j.1=0 then 1 else 0),
    repetition_partialHadamard seedFour seedFour_hadamard,?_,?_⟩
  · refine ⟨1,?_⟩
    change (∑ j : Fin 4 × Fin 3, if j.1=0 then (1:ℤ) else 0)=1+1+1
    rw [Fintype.sum_prod_type]
    norm_num [Fin.sum_univ_succ]
  · unfold witnessBudget
    simp only [Int.cast_ite,Int.cast_one,Int.cast_zero,Fintype.sum_prod_type]
    norm_num [seedFour,Fin.sum_univ_succ,Fintype.card_prod]

end CompletionTheory
