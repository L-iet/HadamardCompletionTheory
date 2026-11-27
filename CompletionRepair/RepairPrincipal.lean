/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionRepair.RepairExchangeBounds
public import CompletionRepair.RepairFiniteFacts
@[expose] public section
set_option maxHeartbeats 4000000
namespace CompletionTheory

def repairTwoToFive (i : Fin 2) : Fin 5 := ⟨i.val,Nat.lt_trans i.isLt (by decide)⟩
def repairRetainedToSixteen (i : Fin 11) : Fin 16 := ⟨i.val,Nat.lt_trans i.isLt (by decide)⟩
def repairInsertedToSixteen (i : Fin 5) : Fin 16 := ⟨11+i.val,Nat.add_lt_add_left i.isLt 11⟩

def repairExchange {r : ℕ} (D : Finset (Fin 12)) (A : Fin r → Fin 24 → ℤ) : Prop :=
  D.card<r ∧ (∀ i j,A i j=1 ∨ A i j= -1) ∧
  (∀ i j,i≠j → (∑ k,A i k*A j k)=0) ∧
  ∀ i,i∉D → ∀ j,(∑ k,repairOriginalMatrix i k*A j k)=0

theorem repairFive_original_cross : ∀ (i : Fin 12) (j : Fin 5),i≠1 →
    (∑ k,repairOriginalMatrix i k*repairPoolRow (repairFiveWitnessIndices j) k)=0 := by
  decide +kernel

theorem repair_two_row_exchange :
    repairExchange {1} (fun i : Fin 2 => repairPoolRow (repairFiveWitnessIndices (repairTwoToFive i))) := by
  refine ⟨by simp,?_,?_,?_⟩
  · intro i j
    exact repair_pool_signs _ _
  · intro i j hij
    have hne : repairTwoToFive i≠repairTwoToFive j := by
      intro h
      exact hij (Fin.ext (congrArg (fun k : Fin 5 => k.val) h))
    simpa only [if_neg hne] using repair_five_pool_rows_orthogonal
      (repairTwoToFive i) (repairTwoToFive j)
  · intro i hi j
    exact repairFive_original_cross i _ (by simpa using hi)

theorem repair_every_exchange_deletes_a_row {r : ℕ} (D : Finset (Fin 12))
    (A : Fin r → Fin 24 → ℤ) (h : repairExchange D A) : 1≤D.card := by
  by_contra hn
  have hc : D.card=0 := by omega
  have hd : D=∅ := Finset.card_eq_zero.mp hc
  obtain ⟨hsize,hsign,horth,hcross⟩ := h
  have hr : 0<r := by omega
  let j : Fin r := ⟨0,hr⟩
  apply repair_original_no_sign_extension
  refine ⟨A j,hsign j,?_⟩
  funext i
  exact hcross i (by simp [hd]) j

theorem repair_exact_one_row_augmentation :
    repairExchange {1} (fun i : Fin 2 => repairPoolRow (repairFiveWitnessIndices (repairTwoToFive i))) ∧
    (∀ (r : ℕ) (D : Finset (Fin 12)) (A : Fin r → Fin 24 → ℤ),repairExchange D A → 1≤D.card) ∧
    (∀ (r : ℕ) (A : Fin r → Fin 24 → ℤ),
      (∀ i j,A i j=1 ∨ A i j= -1) →
      (∀ i,repairRetainedMatrix.mulVec (A i)=0) →
      (∀ i j,i≠j → (∑ k,A i k*A j k)=0) → r≤5) ∧
    ((∀ i : Fin 5,repairRetainedMatrix.mulVec (repairPoolRow (repairFiveWitnessIndices i))=0) ∧
      (∀ i j : Fin 5,(∑ k,repairPoolRow (repairFiveWitnessIndices i) k*
        repairPoolRow (repairFiveWitnessIndices j) k)=if i=j then 24 else 0)) ∧
    (∀ (i : Fin 11) (j : Fin 24),repairAugmentedMatrix (repairRetainedToSixteen i) j=repairRetainedMatrix i j) ∧
    (∀ (i : Fin 5) (j : Fin 24),repairAugmentedMatrix (repairInsertedToSixteen i) j=
      repairPoolRow (repairFiveWitnessIndices i) j) ∧
    (∀ i j : Fin 16,(∑ k,repairAugmentedMatrix i k*repairAugmentedMatrix j k)=if i=j then 24 else 0) ∧
    (¬∃ z : Fin 24 → ℤ,(∀ i,z i=1 ∨ z i= -1) ∧ repairAugmentedMatrix.mulVec z=0) := by
  exact ⟨repair_two_row_exchange,fun _ => repair_every_exchange_deletes_a_row,
    fun _ => repair_retained_orthogonal_family_bound,
    ⟨repairFive_kernel,repair_five_pool_rows_orthogonal⟩,
    repairAugmented_retains,repairAugmented_inserts,repairAugmented_gram_entries,repair_augmented_terminal⟩

theorem repair_augmentation_destroys_odd_feasibility :
    (∀ z : Fin 24 → ℤ,(∀ i,z i%2=1) → repairOriginalMatrix.mulVec z=0 → 40≤∑ i,z i^2) ∧
    (∃ z : Fin 24 → ℤ,(∀ i,z i%2=1) ∧ repairOriginalMatrix.mulVec z=0 ∧ (∑ i,z i^2)=40) ∧
    (¬∃ z : Fin 24 → ℤ,(∀ i,z i%2=1) ∧ repairAugmentedMatrix.mulVec z=0) ∧
    (∀ (i : Fin 11) (j : Fin 24),repairAugmentedMatrix (repairRetainedToSixteen i) j=repairRetainedMatrix i j) ∧
    (∀ (i : Fin 11),repairRetainedOriginalIndex i≠1 ∧
      ∀ j,repairRetainedMatrix i j=repairOriginalMatrix (repairRetainedOriginalIndex i) j) ∧
    (∀ i j : Fin 16,(∑ k,repairAugmentedMatrix i k*repairAugmentedMatrix j k)=if i=j then 24 else 0) := by
  exact ⟨repair_original_odd_minimum_exact.1,repair_original_odd_minimum_exact.2,
    repair_augmented_no_odd_kernel,repairAugmented_retains,repairRetained_is_deletion,repairAugmented_gram_entries⟩
end CompletionTheory
