/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fintype.Fin
public import Lean.Elab.Tactic.Omega
@[expose] public section
set_option autoImplicit false
namespace CompletionTheory
def repairOriginalMasks : Fin 12 → ℕ := ![0,16773120,16519104,9656012,13838682,14783914,1944718,11409518,15230494,5921970,3487346,13018356]

def repairOriginalMatrix : Matrix (Fin 12) (Fin 24) ℤ :=
  fun i j => if (repairOriginalMasks i).testBit j.val then -1 else 1


def repairRetainedMasks : Fin 11 → ℕ := ![0,16519104,9656012,13838682,14783914,1944718,11409518,15230494,5921970,3487346,13018356]

def repairRetainedMatrix : Matrix (Fin 11) (Fin 24) ℤ := fun i j => if (repairRetainedMasks i).testBit j.val then -1 else 1

def repairPoolMasks : Fin 16 → ℕ := ![3198332,3313468,3859816,6777512,6782212,8735670,8847106,8993716,9397154,10996370,11139280,11254416,13957672,14512420,16111636,16773120]

def repairPoolRow (i : Fin 16) (j : Fin 24) : ℤ :=
  if (repairPoolMasks i).testBit j.val then -1 else 1


def repairFiveWitnessIndices : Fin 5 → Fin 16 := ![0,4,5,10,12]


def repairAugmentedMasks : Fin 16 → ℕ := ![0,16519104,9656012,13838682,14783914,1944718,11409518,15230494,5921970,3487346,13018356,3198332,6782212,8735670,11139280,13957672]

def repairAugmentedMatrix : Matrix (Fin 16) (Fin 24) ℤ :=
  fun i j => if (repairAugmentedMasks i).testBit j.val then -1 else 1


def repairRetainedOriginalIndex (i : Fin 11) : Fin 12 :=
  if i.val=0 then 0 else ⟨i.val+1,by have hh := i.isLt; omega⟩


def repairExchange {r : ℕ} (D : Finset (Fin 12)) (A : Fin r → Fin 24 → ℤ) : Prop :=
  D.card<r ∧ (∀ i j,A i j=1 ∨ A i j= -1) ∧
  (∀ i j,i≠j → (∑ k,A i k*A j k)=0) ∧
  ∀ i,i∉D → ∀ j,(∑ k,repairOriginalMatrix i k*A j k)=0


def repairTwoToFive (i : Fin 2) : Fin 5 := ⟨i.val,Nat.lt_trans i.isLt (by decide)⟩

def repairRetainedToSixteen (i : Fin 11) : Fin 16 := ⟨i.val,Nat.lt_trans i.isLt (by decide)⟩

def repairInsertedToSixteen (i : Fin 5) : Fin 16 := ⟨11+i.val,Nat.add_lt_add_left i.isLt 11⟩


theorem repairOriginal_gram_entries : ∀ i j : Fin 12,
    (∑ k,repairOriginalMatrix i k*repairOriginalMatrix j k)=if i=j then 24 else 0 := by sorry

theorem repairRetained_is_deletion : ∀ i : Fin 11,
    repairRetainedOriginalIndex i≠1 ∧
    ∀ j,repairRetainedMatrix i j=repairOriginalMatrix (repairRetainedOriginalIndex i) j := by sorry

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
    (¬∃ z : Fin 24 → ℤ,(∀ i,z i=1 ∨ z i= -1) ∧ repairAugmentedMatrix.mulVec z=0) := by sorry

theorem repair_augmentation_destroys_odd_feasibility :
    (∀ z : Fin 24 → ℤ,(∀ i,z i%2=1) → repairOriginalMatrix.mulVec z=0 → 40≤∑ i,z i^2) ∧
    (∃ z : Fin 24 → ℤ,(∀ i,z i%2=1) ∧ repairOriginalMatrix.mulVec z=0 ∧ (∑ i,z i^2)=40) ∧
    (¬∃ z : Fin 24 → ℤ,(∀ i,z i%2=1) ∧ repairAugmentedMatrix.mulVec z=0) ∧
    (∀ (i : Fin 11) (j : Fin 24),repairAugmentedMatrix (repairRetainedToSixteen i) j=repairRetainedMatrix i j) ∧
    (∀ (i : Fin 11),repairRetainedOriginalIndex i≠1 ∧
      ∀ j,repairRetainedMatrix i j=repairOriginalMatrix (repairRetainedOriginalIndex i) j) ∧
    (∀ i j : Fin 16,(∑ k,repairAugmentedMatrix i k*repairAugmentedMatrix j k)=if i=j then 24 else 0) := by sorry

end CompletionTheory
