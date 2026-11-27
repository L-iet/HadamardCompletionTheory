/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapDeletedBooleanReflectionSmall
public import CompletionCodeTrap.CodeTrapDeletedReconstruction
public import Mathlib.Data.Finset.Card
@[expose] public section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
namespace CompletionTheory

theorem codeTrap_bool_mask_complete (n : ℕ) (f : Fin n → Bool) :
    ∃ b : Fin (2^n),∀ j : Fin n,b.val.testBit j.val=f j := by
  let d : Fin n → Fin 2 := fun j => if f j then 1 else 0
  let b : Fin (2^n) := finFunctionFinEquiv d
  refine ⟨b,?_⟩
  intro j
  have hh := congrArg Fin.val (congrFun (finFunctionFinEquiv.symm_apply_apply d) j)
  change b.val/2^j.val%2=(d j).val at hh
  rw [Nat.testBit_eq_decide_div_mod_eq,hh]
  cases h : f j <;> simp [d,h]

theorem codeTrapDeleted_sign_kernel_classification (d : Fin 12) (z : Fin 20 → ℤ)
    (hz : ∀ i,z i=1 ∨ z i= -1) (hker : (codeTrapDeletedMatrix d).mulVec z=0) :
    z=codeTrapOldIntegerMatrix d ∨ z= -codeTrapOldIntegerMatrix d := by
  obtain ⟨b,hb⟩ := codeTrap_bool_mask_complete 9
    (fun j => decide (z (codeTrapDeletionFree d j)<0))
  have hu : ∀ j,z (codeTrapDeletionFree d j)=codeTrapDeletionSign b.val j.val := by
    intro j
    have hh := hb j
    rcases hz (codeTrapDeletionFree d j) with h|h <;> simp [codeTrapDeletionSign,hh,h]
  have hr : ∀ i : Fin 20,codeTrapDeletionRow d.val b.val i.val=codeTrapDeletionDenom d.val*z i := by
    intro i
    rw [← codeTrapDeleted_boolean_row]
    simp_rw [← hu]
    exact (codeTrapDeleted_reconstruct d z hker i).symm
  have hs : ∀ i : Fin 20,codeTrapDeletionRow d.val b.val i.val=codeTrapDeletionDenom d.val ∨
      codeTrapDeletionRow d.val b.val i.val= -codeTrapDeletionDenom d.val := by
    intro i
    rw [hr]
    rcases hz i with h|h <;> simp [h]
  rcases codeTrapDeleted_boolean_cover d b hs with hp|hn
  · left
    funext i
    exact mul_left_cancel₀ (codeTrapDeletionDenom_nonzero d) ((hr i).symm.trans (hp i))
  · right
    funext i
    apply mul_left_cancel₀ (codeTrapDeletionDenom_nonzero d)
    simpa only [mul_neg,Pi.neg_apply] using (hr i).symm.trans (hn i)

def codeTrapDeletedOriginalIndex (d : Fin 12) (i : Fin 11) : Fin 12 :=
  if i.val<d.val then ⟨i.val,Nat.lt_trans i.isLt (by decide)⟩
  else ⟨i.val+1,Nat.add_lt_add_right i.isLt 1⟩

theorem codeTrapDeleted_identification : ∀ (d : Fin 12) (i : Fin 11),
    codeTrapDeletedOriginalIndex d i≠d ∧
    ∀ j,codeTrapDeletedMatrix d i j=codeTrapOldIntegerMatrix (codeTrapDeletedOriginalIndex d i) j := by
  intro d i
  fin_cases d <;> fin_cases i <;> decide +kernel

theorem codeTrap_one_deletion_only_old_class (d : Fin 12) (z : Fin 20 → ℤ)
    (hz : ∀ i,z i=1 ∨ z i= -1)
    (horth : ∀ i,i≠d → (∑ j,codeTrapOldIntegerMatrix i j*z j)=0) :
    z=codeTrapOldIntegerMatrix d ∨ z= -codeTrapOldIntegerMatrix d := by
  apply codeTrapDeleted_sign_kernel_classification d z hz
  funext i
  change (∑ j,codeTrapDeletedMatrix d i j*z j)=0
  simp_rw [(codeTrapDeleted_identification d i).2]
  exact horth _ (codeTrapDeleted_identification d i).1

theorem codeTrap_new_sign_compatibility_at_most_ten (z : Fin 20 → ℤ)
    (hz : ∀ i,z i=1 ∨ z i= -1)
    (hnew : ∀ i,z≠codeTrapOldIntegerMatrix i ∧ z≠ -codeTrapOldIntegerMatrix i) :
    (Finset.univ.filter (fun i : Fin 12 => (∑ j,codeTrapOldIntegerMatrix i j*z j)=0)).card≤10 := by
  classical
  let B : Finset (Fin 12) := Finset.univ.filter (fun i => (∑ j,codeTrapOldIntegerMatrix i j*z j)≠0)
  have hB : 2≤B.card := by
    by_contra hn
    have hle : B.card≤1 := by omega
    obtain ⟨d,hd⟩ := Finset.card_le_one_iff_subset_singleton.mp hle
    have horth : ∀ i,i≠d → (∑ j,codeTrapOldIntegerMatrix i j*z j)=0 := by
      intro i hi
      by_contra hh
      have hm : i∈B := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩
      exact hi (Finset.mem_singleton.mp (hd hm))
    rcases codeTrap_one_deletion_only_old_class d z hz horth with h|h
    · exact (hnew d).1 h
    · exact (hnew d).2 h
  have hcount := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 12)))
    (fun i => (∑ j,codeTrapOldIntegerMatrix i j*z j)=0)
  change (Finset.univ.filter (fun i : Fin 12 => (∑ j,codeTrapOldIntegerMatrix i j*z j)=0)).card+B.card=12 at hcount
  omega
end CompletionTheory
