/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import PhaseGeometry.PhaseHessian
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PhaseGeometry
open scoped ComplexConjugate

def IsFourthRoot (z : ℂ) : Prop := z=1 ∨ z= -1 ∨ z=Complex.I ∨ z= -Complex.I

theorem fourth_root_iff (z : ℂ) : IsFourthRoot z ↔ z^4=1 := by
  constructor
  · rintro (rfl | rfl | rfl | rfl) <;> norm_num [neg_pow,show (4 : ℕ)=2*2 by decide,pow_mul,Complex.I_sq]
  · intro h
    have hf : (z-1)*(z+1)*(z-Complex.I)*(z+Complex.I)=0 := by
      calc
        _ = z^4-1 := by linear_combination -(z^2-1)*Complex.I_sq
        _ = 0 := sub_eq_zero.mpr h
    rcases mul_eq_zero.mp hf with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact Or.inl (sub_eq_zero.mp h)
        · exact Or.inr (Or.inl (eq_neg_of_add_eq_zero_left h))
      · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp h)))
    · exact Or.inr (Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h)))

def pivotDephase {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) (k l i j : Fin n) : ℂ :=
  F i j*conj (F k j)*conj (F i l)*F k l

theorem pivotDephase_unit {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ)
    (hF : ∀ i j, ‖F i j‖=1) (k l i j : Fin n) : ‖pivotDephase F k l i j‖=1 := by
  simp [pivotDephase,norm_mul,hF]

theorem fourth_power_cross_ratio_criterion {n : ℕ}
    (F : Matrix (Fin n) (Fin n) ℂ) (hF : ∀ i j, ‖F i j‖=1) (k l : Fin n) :
    (∀ i j,IsFourthRoot (pivotDephase F k l i j)) ↔
      ∀ i j,(F i j)^4*(F k l)^4=(F k j)^4*(F i l)^4 := by
  have hu (i j : Fin n) : (F i j)^4*conj ((F i j)^4)=1 := by
    rw [map_pow,← mul_pow]
    have hh : F i j*conj (F i j)=1 := by
      rw [Complex.mul_conj]
      norm_cast
      rw [Complex.normSq_eq_norm_sq,hF]
      norm_num
    rw [hh,one_pow]
  constructor
  · intro hh i j
    have he := (fourth_root_iff _).mp (hh i j)
    have he' := congrArg (fun z : ℂ => z*((F k j)^4*(F i l)^4)) he
    simp only [pivotDephase,mul_pow,← map_pow] at he'
    calc
      _ = (F i j)^4*(F k l)^4*((F k j)^4*conj ((F k j)^4))*((F i l)^4*conj ((F i l)^4)) := by rw [hu,hu]; ring
      _ = _ := by linear_combination he'
  · intro hh i j
    apply (fourth_root_iff _).mpr
    simp only [pivotDephase,mul_pow,← map_pow]
    calc
      _ = ((F i j)^4*(F k l)^4)*conj ((F k j)^4)*conj ((F i l)^4) := by ring
      _ = ((F k j)^4*(F i l)^4)*conj ((F k j)^4)*conj ((F i l)^4) := by rw [hh]
      _ = ((F k j)^4*conj ((F k j)^4))*((F i l)^4*conj ((F i l)^4)) := by ring
      _ = 1 := by rw [hu,hu]; norm_num

theorem unit_mul_conj {z : ℂ} (hz : ‖z‖=1) : z*conj z=1 := by
  rw [Complex.mul_conj]
  norm_cast
  rw [Complex.normSq_eq_norm_sq,hz]
  norm_num

theorem pivotDephase_gram {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ)
    (hF : ∀ i j, ‖F i j‖=1) (k l i r : Fin n) :
    (∑ j,pivotDephase F k l i j*conj (pivotDephase F k l r j))=
      conj (F i l)*F r l*(∑ j,F i j*conj (F r j)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [pivotDephase,map_mul,starRingEnd_self_apply]
  calc
    _ = conj (F i l)*F r l*(F i j*conj (F r j))*(F k j*conj (F k j))*(F k l*conj (F k l)) := by ring
    _ = _ := by rw [unit_mul_conj (hF k j),unit_mul_conj (hF k l)]; ring

theorem pivotDephase_hadamard_gram {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ)
    (hF : ∀ i j, ‖F i j‖=1)
    (horth : ∀ i r,(∑ j,F i j*conj (F r j))=if i=r then (n : ℂ) else 0)
    (k l i r : Fin n) :
    (∑ j,pivotDephase F k l i j*conj (pivotDephase F k l r j))=
      if i=r then (n : ℂ) else 0 := by
  rw [pivotDephase_gram F hF,horth]
  split_ifs with h
  · subst r
    rw [mul_comm (conj _) _,unit_mul_conj (hF i l),one_mul]
  · ring


def HasFourPhaseGauge {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ r c : Fin n → ℂ,(∀ i,‖r i‖=1) ∧ (∀ j,‖c j‖=1) ∧
    ∀ i j,IsFourthRoot (r i*F i j*c j)

theorem four_phase_gauge_iff_cross_ratios {n : ℕ}
    (F : Matrix (Fin n) (Fin n) ℂ) (hF : ∀ i j, ‖F i j‖=1) (k l : Fin n) :
    HasFourPhaseGauge F ↔ ∀ i j,(F i j)^4*(F k l)^4=(F k j)^4*(F i l)^4 := by
  constructor
  · rintro ⟨r,c,hr,hc,hg⟩ i j
    have h (a b : Fin n) : (r a)^4*(F a b)^4*(c b)^4=1 := by
      simpa only [mul_pow] using (fourth_root_iff _).mp (hg a b)
    have he : ((r i)^4*(c j)^4*(r k)^4*(c l)^4)*
        ((F i j)^4*(F k l)^4-(F k j)^4*(F i l)^4)=0 := by
      calc
        _ = ((r i)^4*(F i j)^4*(c j)^4)*((r k)^4*(F k l)^4*(c l)^4)-
          ((r k)^4*(F k j)^4*(c j)^4)*((r i)^4*(F i l)^4*(c l)^4) := by ring
        _ = 0 := by rw [h,h,h,h]; ring
    have hr0 (a : Fin n) : r a ≠ 0 := by intro hz; simpa [hz] using hr a
    have hc0 (a : Fin n) : c a ≠ 0 := by intro hz; simpa [hz] using hc a
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (hr0 i)) (pow_ne_zero _ (hc0 j))) (pow_ne_zero _ (hr0 k))) (pow_ne_zero _ (hc0 l))))
  · intro hh
    refine ⟨fun i => conj (F i l),fun j => conj (F k j)*F k l,?_,?_,?_⟩
    · intro i; simpa using hF i l
    · intro j; simp [norm_mul,hF]
    · intro i j
      have he := ((fourth_power_cross_ratio_criterion F hF k l).mpr hh) i j
      have heq : conj (F i l)*F i j*(conj (F k j)*F k l)=pivotDephase F k l i j := by unfold pivotDephase; ring
      rw [heq]
      exact he


def complexRowGram {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i k : Fin n) : ℂ :=
  ∑ j,M i j*conj (M k j)

theorem gram_normSq_four_cycles {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i k : Fin n) :
    Complex.normSq (complexRowGram M i k)=
      ∑ j,∑ l,(M i j*conj (M k j)*conj (M i l)*M k l).re := by
  have he (z : ℂ) : Complex.normSq z=(z*conj z).re := by rw [Complex.mul_conj,Complex.ofReal_re]
  rw [he]
  simp only [complexRowGram,map_sum,map_mul,starRingEnd_self_apply,
    Finset.sum_mul,Finset.mul_sum,Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  congr 1
  ring

theorem pivot_fourth_error {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ)
    (hF : ∀ i j, ‖F i j‖=1) (k l i j : Fin n) :
    Complex.normSq ((pivotDephase F k l i j)^4-1)=
      2-2*((F i j)^4*conj ((F k j)^4)*conj ((F i l)^4)*(F k l)^4).re := by
  rw [Complex.normSq_sub]
  have hu : Complex.normSq ((pivotDephase F k l i j)^4)=1 := by
    rw [Complex.normSq_eq_norm_sq,norm_pow,pivotDephase_unit F hF]
    norm_num
  rw [hu]
  simp only [Complex.normSq_one,map_one,mul_one,pivotDephase,mul_pow,← map_pow]
  ring


def pivotFourthError {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) (k l : Fin n) : ℝ :=
  ∑ i,∑ j,Complex.normSq ((pivotDephase F k l i j)^4-1)

def fourthGramDeficit {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (n : ℝ)^4-∑ i,∑ k,Complex.normSq (complexRowGram (fun a b => (F a b)^4) i k)

theorem sum_four_reorder {n : ℕ} (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ k,∑ l,∑ i,∑ j,f i k j l)=∑ i,∑ k,∑ j,∑ l,f i k j l := by
  calc
    _ = ∑ k,∑ i,∑ l,∑ j,f i k j l := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]
    _ = ∑ i,∑ k,∑ l,∑ j,f i k j l := by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]

set_option maxHeartbeats 1500000 in
theorem pivot_fourth_error_sum {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ)
    (hF : ∀ i j, ‖F i j‖=1) :
    (∑ k,∑ l,pivotFourthError F k l)=2*fourthGramDeficit F := by
  have hs : (∑ k,∑ l,∑ i,∑ j,
      ((F i j)^4*conj ((F k j)^4)*conj ((F i l)^4)*(F k l)^4).re)=
      ∑ i,∑ k,Complex.normSq (complexRowGram (fun a b => (F a b)^4) i k) := by
    rw [sum_four_reorder]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro k hk
    exact (gram_normSq_four_cycles (fun a b => (F a b)^4) i k).symm
  have hc : (∑ k : Fin n,∑ l : Fin n,∑ i : Fin n,∑ j : Fin n,(2 : ℝ))=2*(n : ℝ)^4 := by
    simp
    ring
  unfold pivotFourthError
  simp_rw [pivot_fourth_error F hF,Finset.sum_sub_distrib,← Finset.mul_sum]
  rw [hs]
  change (∑ k : Fin n,∑ l : Fin n,∑ i : Fin n,∑ j : Fin n,(2 : ℝ))-_=_
  rw [hc]
  unfold fourthGramDeficit
  ring


theorem fourthGramDeficit_nonneg {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ)
    (hF : ∀ i j, ‖F i j‖=1) : 0 ≤ fourthGramDeficit F := by
  have hn : 0 ≤ ∑ k,∑ l,pivotFourthError F k l := by
    apply Finset.sum_nonneg
    intro k hk
    apply Finset.sum_nonneg
    intro l hl
    apply Finset.sum_nonneg
    intro i hi
    exact Finset.sum_nonneg (fun j hj => Complex.normSq_nonneg _)
  rw [pivot_fourth_error_sum F hF] at hn
  linarith

theorem exists_pivot_fourth_error_le {n : ℕ} (hn : 0<n)
    (F : Matrix (Fin n) (Fin n) ℂ) (hF : ∀ i j, ‖F i j‖=1) :
    ∃ k l,pivotFourthError F k l ≤ 2*fourthGramDeficit F/(n : ℝ)^2 := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hc : (∑ k : Fin n,∑ l : Fin n,2*fourthGramDeficit F/(n : ℝ)^2)=
      2*fourthGramDeficit F := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp [hnR]
    <;> ring
  by_contra! hh
  have hs : (∑ k : Fin n,∑ l : Fin n,2*fourthGramDeficit F/(n : ℝ)^2)<
      ∑ k,∑ l,pivotFourthError F k l := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro k hk
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun l hl => hh k l)
  rw [hc,pivot_fourth_error_sum F hF] at hs
  exact (lt_irrefl _ hs)

end PhaseGeometry
