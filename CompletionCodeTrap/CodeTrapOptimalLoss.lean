/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapOneDeletion
public import CompletionCodeTrap.CodeTrapFiniteFieldFacts
public import CompletionTheory.Order20Terminal
public import Mathlib.Tactic.Choose
@[expose] public section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory

def trapIntegerHadamard (H : Matrix (Fin 20) (Fin 20) ℤ) : Prop :=
  (∀ i j,H i j=1 ∨ H i j= -1) ∧
  ∀ i j,(∑ k,H i k*H j k)=if i=j then 20 else 0

noncomputable def trapRetainedOldClasses (H : Matrix (Fin 20) (Fin 20) ℤ) : Finset (Fin 12) := by
  classical
  exact Finset.univ.filter (fun i => ∃ j : Fin 20,H j=codeTrapOldIntegerMatrix i ∨ H j= -codeTrapOldIntegerMatrix i)

noncomputable def trapOldRowLoss (H : Matrix (Fin 20) (Fin 20) ℤ) : ℕ := 12-(trapRetainedOldClasses H).card

theorem trapOld_integer_gram : codeTrapOldIntegerMatrix*codeTrapOldIntegerMatrix.transpose=
    (20 : ℤ) • (1 : Matrix (Fin 12) (Fin 12) ℤ) := by
  change (encodedIntFrame codeTrap20Masks : Matrix (Fin 12) (Fin 20) ℤ)*
    (encodedIntFrame codeTrap20Masks).transpose=(20 : ℤ) • (1 : Matrix (Fin 12) (Fin 12) ℤ)
  exact codeTrap20_int_gram

theorem trapOld_row_norm (i : Fin 12) : (∑ k,codeTrapOldIntegerMatrix i k*codeTrapOldIntegerMatrix i k)=20 := by
  have hh := congrArg (fun M : Matrix (Fin 12) (Fin 12) ℤ => M i i) trapOld_integer_gram
  change (∑ k,codeTrapOldIntegerMatrix i k*codeTrapOldIntegerMatrix i k)=20*(if i=i then 1 else 0) at hh
  simpa using hh

theorem trapIntegerHadamard_has_new_class (H : Matrix (Fin 20) (Fin 20) ℤ)
    (hg : ∀ i j,(∑ k,H i k*H j k)=if i=j then 20 else 0) :
    ∃ j : Fin 20,∀ i : Fin 12,H j≠codeTrapOldIntegerMatrix i ∧ H j≠ -codeTrapOldIntegerMatrix i := by
  classical
  by_contra hn
  have hc : ∀ j : Fin 20,∃ i : Fin 12,H j=codeTrapOldIntegerMatrix i ∨ H j= -codeTrapOldIntegerMatrix i := by
    intro j
    by_contra hno
    apply hn
    refine ⟨j,?_⟩
    intro i
    constructor
    · intro he
      exact hno ⟨i,Or.inl he⟩
    · intro he
      exact hno ⟨i,Or.inr he⟩
  choose f hf using hc
  have hinj : Function.Injective f := by
    intro j k he
    by_contra hne
    have hz : (∑ t,H j t*H k t)=0 := by simpa only [if_neg hne] using hg j k
    have hp := trapOld_row_norm (f j)
    have hj := hf j
    have hk := hf k
    rw [← he] at hk
    rcases hj with hj|hj <;> rcases hk with hk|hk <;>
      simp only [hj,hk,Pi.neg_apply,mul_neg,neg_mul,neg_mul_neg,neg_neg,Finset.sum_neg_distrib,hp] at hz <;>
      norm_num at hz
  have hcard := Fintype.card_le_of_injective f hinj
  norm_num at hcard

theorem trapRetainedOldClasses_bound (H : Matrix (Fin 20) (Fin 20) ℤ)
    (hH : trapIntegerHadamard H) : (trapRetainedOldClasses H).card≤10 := by
  classical
  obtain ⟨j,hnew⟩ := trapIntegerHadamard_has_new_class H hH.2
  have hcompat := codeTrap_new_sign_compatibility_at_most_ten (H j) (hH.1 j) hnew
  have hsub : trapRetainedOldClasses H⊆
      Finset.univ.filter (fun i : Fin 12 => (∑ k,codeTrapOldIntegerMatrix i k*H j k)=0) := by
    intro i hi
    obtain ⟨k,hk⟩ := (Finset.mem_filter.mp hi).2
    have hne : k≠j := by
      intro he
      subst k
      rcases hk with h|h
      · exact (hnew i).1 h
      · exact (hnew i).2 h
    have hz : (∑ t,H k t*H j t)=0 := by simpa only [if_neg hne] using hH.2 k j
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rcases hk with h|h
    · simpa only [h] using hz
    · have hn : -(∑ t,codeTrapOldIntegerMatrix i t*H j t)=0 := by
        simpa only [h,Pi.neg_apply,neg_mul,Finset.sum_neg_distrib] using hz
      exact neg_eq_zero.mp hn
  exact le_trans (Finset.card_le_card hsub) hcompat

theorem trapEveryCompletion_loses_two (H : Matrix (Fin 20) (Fin 20) ℤ)
    (hH : trapIntegerHadamard H) : 2≤trapOldRowLoss H := by
  have hh := trapRetainedOldClasses_bound H hH
  unfold trapOldRowLoss
  omega

def trapRetainedOldIndex : Fin 10 → Fin 12 := ![0,1,2,4,5,6,7,9,10,11]

theorem trapRetainedOldIndex_injective : Function.Injective trapRetainedOldIndex := by decide +kernel

theorem trapRetainedOldIndex_properties : ∀ i : Fin 10,
    trapRetainedOldIndex i≠3 ∧ trapRetainedOldIndex i≠8 ∧
    ∀ j,trapCompletedIntegerMatrix (trapTenToTwenty i) j=codeTrapOldIntegerMatrix (trapRetainedOldIndex i) j := by
  intro i
  fin_cases i <;> decide +kernel

theorem trapRetainedOldIndex_covers : ∀ i : Fin 12,i≠3 → i≠8 → ∃ j,trapRetainedOldIndex j=i := by
  decide +kernel

theorem trapCompleted_integer_hadamard : trapIntegerHadamard trapCompletedIntegerMatrix := by
  constructor
  · intro i j
    unfold trapCompletedIntegerMatrix encodedIntFrame encodedSign
    split <;> simp
  · intro i j
    have hh := congrArg (fun M : Matrix (Fin 20) (Fin 20) ℤ => M i j) trapCompleted_integer_gram
    change (∑ k,trapCompletedIntegerMatrix i k*trapCompletedIntegerMatrix j k)=20*(if i=j then 1 else 0) at hh
    simpa only [mul_ite,mul_one,mul_zero] using hh

theorem trapCompleted_retains_ten : 10≤(trapRetainedOldClasses trapCompletedIntegerMatrix).card := by
  classical
  have hsub : Finset.univ.image trapRetainedOldIndex⊆trapRetainedOldClasses trapCompletedIntegerMatrix := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,trapTenToTwenty j,Or.inl ?_⟩
    funext k
    exact (trapRetainedOldIndex_properties j).2.2 k
  have hc := Finset.card_le_card hsub
  simpa only [Finset.card_image_of_injective _ trapRetainedOldIndex_injective,
    Finset.card_univ,Fintype.card_fin] using hc

theorem trapCompleted_old_row_loss_two : trapOldRowLoss trapCompletedIntegerMatrix=2 := by
  have hle := trapRetainedOldClasses_bound trapCompletedIntegerMatrix trapCompleted_integer_hadamard
  have hge := trapCompleted_retains_ten
  unfold trapOldRowLoss
  omega

theorem trapMinimum_old_row_loss_two :
    (∀ H : Matrix (Fin 20) (Fin 20) ℤ,trapIntegerHadamard H → 2≤trapOldRowLoss H) ∧
    trapIntegerHadamard trapCompletedIntegerMatrix ∧ trapOldRowLoss trapCompletedIntegerMatrix=2 :=
  ⟨trapEveryCompletion_loses_two,trapCompleted_integer_hadamard,trapCompleted_old_row_loss_two⟩

noncomputable def trapOldRealMatrix : Matrix (Fin 12) (Fin 20) ℝ := encodedRealFrame codeTrapOldMasks

theorem trapOldReal_partialHadamard : IsPartialHadamard trapOldRealMatrix := by
  change IsPartialHadamard codeTrap20Frame
  exact codeTrap20_partialHadamard

theorem trapOldReal_terminal : NoSignExtension trapOldRealMatrix := by
  change NoSignExtension codeTrap20Frame
  exact codeTrap20_noSignExtension

theorem trapCompleted_mathlib_hadamard : Matrix.IsHadamard trapCompletedRealMatrix :=
  isHadamard_mathlib trapCompleted_isHadamard
end CompletionTheory
