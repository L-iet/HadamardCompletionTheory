/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionRepair.RepairIntegerEnergy
public import Mathlib.Tactic.NormNum
@[expose] public section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
namespace CompletionTheory

def repairOriginalMasks : Fin 12 → ℕ := ![0,16773120,16519104,9656012,13838682,14783914,1944718,11409518,15230494,5921970,3487346,13018356]
def repairOriginalMatrix : Matrix (Fin 12) (Fin 24) ℤ :=
  fun i j => if (repairOriginalMasks i).testBit j.val then -1 else 1

def repairFreePosition : Fin 12 → Fin 24 := ![11,13,14,15,16,17,18,19,20,21,22,23]
def repairFreeSelector : Matrix (Fin 12) (Fin 24) ℤ :=
  fun i j => if j=repairFreePosition i then 1 else 0

def repairRowRelation : Matrix (Fin 24) (Fin 12) ℤ :=
![
  ![0,0,12,0,0,0,-12,12,12,12,-12,0],
  ![6,0,-6,6,0,6,-6,-6,0,-6,0,6],
  ![16,-12,-8,8,4,4,0,-8,-8,0,8,-4],
  ![-13,12,11,-11,-4,-7,3,5,2,3,-2,1],
  ![2,0,2,-2,-4,2,6,2,-4,-6,4,-2],
  ![-11,12,1,-1,4,-5,9,-5,-2,-3,2,-1],
  ![2,0,2,-2,-4,2,-6,2,8,6,-8,-2],
  ![-6,12,-6,-6,0,6,6,-6,0,-18,12,6],
  ![15,-12,-9,9,0,-3,3,-3,-6,3,6,-3],
  ![-8,12,-8,-4,4,4,12,-8,-8,-12,8,8],
  ![9,-12,9,3,0,-9,-15,15,6,21,-18,-9],
  ![0,0,0,0,0,0,0,0,0,0,0,0],
  ![12,-12,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0,0]
]

theorem repairFreePosition_injective : Function.Injective repairFreePosition := by
  decide +kernel

theorem repairOriginal_relation_row_0 : ∀ j : Fin 24,
    6*(4*(if (0 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairKernelNumerators 0 k*repairFreeSelector k j)=
      ∑ k,repairRowRelation 0 k*repairOriginalMatrix k j := by
  decide +kernel

theorem repairOriginal_relation_row_1 : ∀ j : Fin 24,
    6*(4*(if (1 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairKernelNumerators 1 k*repairFreeSelector k j)=
      ∑ k,repairRowRelation 1 k*repairOriginalMatrix k j := by
  decide +kernel

theorem repairOriginal_relation_row_2 : ∀ j : Fin 24,
    6*(4*(if (2 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairKernelNumerators 2 k*repairFreeSelector k j)=
      ∑ k,repairRowRelation 2 k*repairOriginalMatrix k j := by
  decide +kernel

theorem repairOriginal_relation_row_3 : ∀ j : Fin 24,
    6*(4*(if (3 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairKernelNumerators 3 k*repairFreeSelector k j)=
      ∑ k,repairRowRelation 3 k*repairOriginalMatrix k j := by
  decide +kernel

theorem repairOriginal_relation_row_4 : ∀ j : Fin 24,
    6*(4*(if (4 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairKernelNumerators 4 k*repairFreeSelector k j)=
      ∑ k,repairRowRelation 4 k*repairOriginalMatrix k j := by
  decide +kernel

theorem repairOriginal_relation_row_5 : ∀ j : Fin 24,
    6*(4*(if (5 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairKernelNumerators 5 k*repairFreeSelector k j)=
      ∑ k,repairRowRelation 5 k*repairOriginalMatrix k j := by
  decide +kernel

theorem repairOriginal_relation_row_6 : ∀ j : Fin 24,
    6*(4*(if (6 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairKernelNumerators 6 k*repairFreeSelector k j)=
      ∑ k,repairRowRelation 6 k*repairOriginalMatrix k j := by
  decide +kernel

theorem repairOriginal_relation_row_7 : ∀ j : Fin 24,
    6*(4*(if (7 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairKernelNumerators 7 k*repairFreeSelector k j)=
      ∑ k,repairRowRelation 7 k*repairOriginalMatrix k j := by
  decide +kernel

theorem repairOriginal_relation_row_8 : ∀ j : Fin 24,
    6*(4*(if (8 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairKernelNumerators 8 k*repairFreeSelector k j)=
      ∑ k,repairRowRelation 8 k*repairOriginalMatrix k j := by
  decide +kernel

theorem repairOriginal_relation_row_9 : ∀ j : Fin 24,
    6*(4*(if (9 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairKernelNumerators 9 k*repairFreeSelector k j)=
      ∑ k,repairRowRelation 9 k*repairOriginalMatrix k j := by
  decide +kernel

theorem repairOriginal_relation_row_10 : ∀ j : Fin 24,
    6*(4*(if (10 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairKernelNumerators 10 k*repairFreeSelector k j)=
      ∑ k,repairRowRelation 10 k*repairOriginalMatrix k j := by
  decide +kernel

theorem repairOriginal_relation_row_11 : ∀ j : Fin 24,
    6*(4*(if (11 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairKernelNumerators 11 k*repairFreeSelector k j)=
      ∑ k,repairRowRelation 11 k*repairOriginalMatrix k j := by
  decide +kernel

theorem repairOriginal_relation_row_12 : ∀ j : Fin 24,
    6*(4*(if (12 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairKernelNumerators 12 k*repairFreeSelector k j)=
      ∑ k,repairRowRelation 12 k*repairOriginalMatrix k j := by
  decide +kernel

theorem repairOriginal_relation_row_13 : ∀ j : Fin 24,
    6*(4*(if (13 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairKernelNumerators 13 k*repairFreeSelector k j)=
      ∑ k,repairRowRelation 13 k*repairOriginalMatrix k j := by
  decide +kernel

theorem repairOriginal_relation_row_14 : ∀ j : Fin 24,
    6*(4*(if (14 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairKernelNumerators 14 k*repairFreeSelector k j)=
      ∑ k,repairRowRelation 14 k*repairOriginalMatrix k j := by
  decide +kernel

theorem repairOriginal_relation_row_15 : ∀ j : Fin 24,
    6*(4*(if (15 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairKernelNumerators 15 k*repairFreeSelector k j)=
      ∑ k,repairRowRelation 15 k*repairOriginalMatrix k j := by
  decide +kernel

theorem repairOriginal_relation_row_16 : ∀ j : Fin 24,
    6*(4*(if (16 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairKernelNumerators 16 k*repairFreeSelector k j)=
      ∑ k,repairRowRelation 16 k*repairOriginalMatrix k j := by
  decide +kernel

theorem repairOriginal_relation_row_17 : ∀ j : Fin 24,
    6*(4*(if (17 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairKernelNumerators 17 k*repairFreeSelector k j)=
      ∑ k,repairRowRelation 17 k*repairOriginalMatrix k j := by
  decide +kernel

theorem repairOriginal_relation_row_18 : ∀ j : Fin 24,
    6*(4*(if (18 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairKernelNumerators 18 k*repairFreeSelector k j)=
      ∑ k,repairRowRelation 18 k*repairOriginalMatrix k j := by
  decide +kernel

theorem repairOriginal_relation_row_19 : ∀ j : Fin 24,
    6*(4*(if (19 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairKernelNumerators 19 k*repairFreeSelector k j)=
      ∑ k,repairRowRelation 19 k*repairOriginalMatrix k j := by
  decide +kernel

theorem repairOriginal_relation_row_20 : ∀ j : Fin 24,
    6*(4*(if (20 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairKernelNumerators 20 k*repairFreeSelector k j)=
      ∑ k,repairRowRelation 20 k*repairOriginalMatrix k j := by
  decide +kernel

theorem repairOriginal_relation_row_21 : ∀ j : Fin 24,
    6*(4*(if (21 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairKernelNumerators 21 k*repairFreeSelector k j)=
      ∑ k,repairRowRelation 21 k*repairOriginalMatrix k j := by
  decide +kernel

theorem repairOriginal_relation_row_22 : ∀ j : Fin 24,
    6*(4*(if (22 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairKernelNumerators 22 k*repairFreeSelector k j)=
      ∑ k,repairRowRelation 22 k*repairOriginalMatrix k j := by
  decide +kernel

theorem repairOriginal_relation_row_23 : ∀ j : Fin 24,
    6*(4*(if (23 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairKernelNumerators 23 k*repairFreeSelector k j)=
      ∑ k,repairRowRelation 23 k*repairOriginalMatrix k j := by
  decide +kernel

theorem repairOriginal_relation_entries : ∀ i j : Fin 24,
    6*(4*(if i=j then (1 : ℤ) else 0)-
      ∑ k,repairKernelNumerators i k*repairFreeSelector k j)=
      ∑ k,repairRowRelation i k*repairOriginalMatrix k j := by
  intro i
  fin_cases i
  · exact repairOriginal_relation_row_0
  · exact repairOriginal_relation_row_1
  · exact repairOriginal_relation_row_2
  · exact repairOriginal_relation_row_3
  · exact repairOriginal_relation_row_4
  · exact repairOriginal_relation_row_5
  · exact repairOriginal_relation_row_6
  · exact repairOriginal_relation_row_7
  · exact repairOriginal_relation_row_8
  · exact repairOriginal_relation_row_9
  · exact repairOriginal_relation_row_10
  · exact repairOriginal_relation_row_11
  · exact repairOriginal_relation_row_12
  · exact repairOriginal_relation_row_13
  · exact repairOriginal_relation_row_14
  · exact repairOriginal_relation_row_15
  · exact repairOriginal_relation_row_16
  · exact repairOriginal_relation_row_17
  · exact repairOriginal_relation_row_18
  · exact repairOriginal_relation_row_19
  · exact repairOriginal_relation_row_20
  · exact repairOriginal_relation_row_21
  · exact repairOriginal_relation_row_22
  · exact repairOriginal_relation_row_23

theorem repairOriginal_matrix_relation :
    (6 : ℤ) • ((4 : ℤ) • (1 : Matrix (Fin 24) (Fin 24) ℤ)-
      repairKernelNumerators*repairFreeSelector)=repairRowRelation*repairOriginalMatrix := by
  apply Matrix.ext
  intro i j
  change 6*(4*(if i=j then (1 : ℤ) else 0)-
    ∑ k,repairKernelNumerators i k*repairFreeSelector k j)=
    ∑ k,repairRowRelation i k*repairOriginalMatrix k j
  exact repairOriginal_relation_entries i j

theorem repairFreeSelector_mulVec (z : Fin 24 → ℤ) :
    repairFreeSelector.mulVec z=fun k => z (repairFreePosition k) := by
  funext k
  simp [Matrix.mulVec,dotProduct,repairFreeSelector,ite_mul]

theorem repairOriginal_reconstruct (z : Fin 24 → ℤ) (hker : repairOriginalMatrix.mulVec z=0) :
    ∀ i,4*z i=repairKernelNumerators.mulVec (fun k => z (repairFreePosition k)) i := by
  have hh := congrArg (fun M : Matrix (Fin 24) (Fin 24) ℤ => M.mulVec z)
    repairOriginal_matrix_relation
  simp only [Matrix.smul_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec,hker,Matrix.mulVec_zero] at hh
  rw [repairFreeSelector_mulVec] at hh
  intro i
  have hi := congrFun hh i
  change 6*(4*z i-repairKernelNumerators.mulVec (fun k => z (repairFreePosition k)) i)=0 at hi
  omega
end CompletionTheory
