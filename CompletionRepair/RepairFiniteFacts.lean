/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Data.Fintype.Fin
public import CompletionRepair.RepairPoolColor
public import CompletionRepair.RepairRetainedRelations
public import CompletionRepair.RepairExactMinimum
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Decide
public import Lean.Elab.Tactic.Omega
@[expose] public section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace CompletionTheory

def repairAugmentedMasks : Fin 16 → ℕ := ![0,16519104,9656012,13838682,14783914,1944718,11409518,15230494,5921970,3487346,13018356,3198332,6782212,8735670,11139280,13957672]
def repairAugmentedMatrix : Matrix (Fin 16) (Fin 24) ℤ :=
  fun i j => if (repairAugmentedMasks i).testBit j.val then -1 else 1

theorem repairAugmented_gram_entries : ∀ i j : Fin 16,
    (∑ k,repairAugmentedMatrix i k*repairAugmentedMatrix j k)=
      if i=j then 24 else 0 := by
  decide +kernel

theorem repairAugmented_integer_gram :
    repairAugmentedMatrix*repairAugmentedMatrix.transpose=
      (24 : ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ) := by
  apply Matrix.ext
  intro i j
  by_cases h : i=j <;>
    simpa [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply,h] using repairAugmented_gram_entries i j

def repairOddObstructionCoeff (i : Fin 16) : ℤ :=
  repairAugmentedMatrix i 0+repairAugmentedMatrix i 9-repairAugmentedMatrix i 11

theorem repairOddObstructionCertificate : ∀ j : Fin 24,
    (∑ i,repairOddObstructionCoeff i*repairAugmentedMatrix i j)=
      24*((if j=0 then 1 else 0)+(if j=9 then 1 else 0)-(if j=11 then 1 else 0)) := by
  decide +kernel

theorem repair_augmented_no_odd_kernel :
    ¬∃ z : Fin 24 → ℤ,(∀ j,z j%2=1) ∧ repairAugmentedMatrix.mulVec z=0 := by
  rintro ⟨z,hz,hker⟩
  have hlinear : (∑ j,(∑ i,repairOddObstructionCoeff i*repairAugmentedMatrix i j)*z j)=
      ∑ i,repairOddObstructionCoeff i*(∑ j,repairAugmentedMatrix i j*z j) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc,← Finset.mul_sum]
  have hzero : (∑ i,repairOddObstructionCoeff i*(∑ j,repairAugmentedMatrix i j*z j))=0 := by
    change (∑ i,repairOddObstructionCoeff i*(repairAugmentedMatrix.mulVec z i))=0
    rw [hker]
    simp
  have hh := hlinear.trans hzero
  simp only [repairOddObstructionCertificate,mul_add,mul_sub,add_mul,sub_mul,
    mul_ite,ite_mul,mul_one,mul_zero,zero_mul] at hh
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib] at hh
  simp at hh
  have h0 := hz 0
  have h9 := hz 9
  have h11 := hz 11
  omega

theorem repairOriginal_gram_entries : ∀ i j : Fin 12,
    (∑ k,repairOriginalMatrix i k*repairOriginalMatrix j k)=if i=j then 24 else 0 := by
  decide +kernel

def repairRetainedOriginalIndex (i : Fin 11) : Fin 12 :=
  if i.val=0 then 0 else ⟨i.val+1,by have hh := i.isLt; omega⟩

theorem repairRetained_is_deletion : ∀ i : Fin 11,
    repairRetainedOriginalIndex i≠1 ∧
    ∀ j,repairRetainedMatrix i j=repairOriginalMatrix (repairRetainedOriginalIndex i) j := by
  intro i
  fin_cases i <;> decide +kernel

theorem repairAugmented_retains : ∀ (i : Fin 11) (j : Fin 24),
    repairAugmentedMatrix ⟨i.val,by have hh := i.isLt; omega⟩ j=repairRetainedMatrix i j := by
  intro i
  fin_cases i <;> decide +kernel

theorem repairAugmented_inserts : ∀ (i : Fin 5) (j : Fin 24),
    repairAugmentedMatrix ⟨11+i.val,by have hh := i.isLt; omega⟩ j=
      repairPoolRow (repairFiveWitnessIndices i) j := by
  decide +kernel

theorem repairFive_kernel_entries : ∀ (i : Fin 5) (j : Fin 11),
    repairRetainedMatrix.mulVec (repairPoolRow (repairFiveWitnessIndices i)) j=0 := by
  decide +kernel

theorem repairFive_kernel (i : Fin 5) :
    repairRetainedMatrix.mulVec (repairPoolRow (repairFiveWitnessIndices i))=0 := by
  funext j
  exact repairFive_kernel_entries i j

theorem repair_pool_signs (i : Fin 16) (j : Fin 24) :
    repairPoolRow i j=1 ∨ repairPoolRow i j= -1 := by
  unfold repairPoolRow
  split <;> simp

theorem repair_augmented_signs (i : Fin 16) (j : Fin 24) :
    repairAugmentedMatrix i j=1 ∨ repairAugmentedMatrix i j= -1 := by
  unfold repairAugmentedMatrix
  split <;> simp

theorem repair_augmented_terminal :
    ¬∃ z : Fin 24 → ℤ,(∀ i,z i=1 ∨ z i= -1) ∧ repairAugmentedMatrix.mulVec z=0 := by
  rintro ⟨z,hz,hk⟩
  apply repair_augmented_no_odd_kernel
  refine ⟨z,?_,hk⟩
  intro i
  rcases hz i with h|h <;> simp [h]
end CompletionTheory
