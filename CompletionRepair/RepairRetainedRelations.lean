/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionRepair.RepairOriginalRelations
public import CompletionRepair.RepairCoverBoolean
@[expose] public section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
namespace CompletionTheory
def repairRetainedMasks : Fin 11 → ℕ := ![0,16519104,9656012,13838682,14783914,1944718,11409518,15230494,5921970,3487346,13018356]
def repairRetainedMatrix : Matrix (Fin 11) (Fin 24) ℤ := fun i j => if (repairRetainedMasks i).testBit j.val then -1 else 1
def repairRetainedBasis : Matrix (Fin 24) (Fin 13) ℤ := ![
  ![4,0,-8,4,-8,-12,4,-4,8,-4,4,8,8],
  ![-8,0,0,0,2,2,0,-4,-8,-4,-2,0,2],
  ![-4,4,0,0,0,8,0,-4,-8,4,-4,-4,-4],
  ![6,-4,0,-2,-1,-7,-2,6,8,0,3,2,-1],
  ![0,0,0,-4,2,2,-4,4,0,0,2,-4,-2],
  ![2,-4,4,-2,1,3,-2,2,0,4,-3,-2,-3],
  ![0,0,-4,4,-2,-6,0,-4,4,-4,2,4,2],
  ![-8,-4,8,-8,6,6,-8,4,-8,-4,2,-4,-2],
  ![-2,4,0,2,-1,5,2,-2,-4,4,-5,-6,-5],
  ![-4,-4,8,-8,8,8,-4,4,-8,0,-4,-4,-4],
  ![10,4,-12,10,-11,-13,10,-6,12,0,1,6,5],
  ![4,0,0,0,0,0,0,0,0,0,0,0,0],
  ![0,4,0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,4,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,4,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,4,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,4,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,4,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,4,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,4,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,4,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,4,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0,4,0],
  ![0,0,0,0,0,0,0,0,0,0,0,0,4]
]
def repairRetainedPosition : Fin 13 → Fin 24 := ![11,12,13,14,15,16,17,18,19,20,21,22,23]
def repairRetainedSelector : Matrix (Fin 13) (Fin 24) ℤ := fun i j => if j=repairRetainedPosition i then 1 else 0
def repairRetainedRelation : Matrix (Fin 24) (Fin 11) ℤ := ![
  ![0,12,0,0,0,-12,12,12,12,-12,0],
  ![6,-6,6,0,6,-6,-6,0,-6,0,6],
  ![4,-8,8,4,4,0,-8,-8,0,8,-4],
  ![-1,11,-11,-4,-7,3,5,2,3,-2,1],
  ![2,2,-2,-4,2,6,2,-4,-6,4,-2],
  ![1,1,-1,4,-5,9,-5,-2,-3,2,-1],
  ![2,2,-2,-4,2,-6,2,8,6,-8,-2],
  ![6,-6,-6,0,6,6,-6,0,-18,12,6],
  ![3,-9,9,0,-3,3,-3,-6,3,6,-3],
  ![4,-8,-4,4,4,12,-8,-8,-12,8,8],
  ![-3,9,3,0,-9,-15,15,6,21,-18,-9],
  ![0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0]
]
theorem repairRetained_relation_row_0 : ∀ j : Fin 24,
    6*(4*(if (0 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairRetainedBasis 0 k*repairRetainedSelector k j)=
      ∑ k,repairRetainedRelation 0 k*repairRetainedMatrix k j := by
  decide +kernel

theorem repairRetained_relation_row_1 : ∀ j : Fin 24,
    6*(4*(if (1 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairRetainedBasis 1 k*repairRetainedSelector k j)=
      ∑ k,repairRetainedRelation 1 k*repairRetainedMatrix k j := by
  decide +kernel

theorem repairRetained_relation_row_2 : ∀ j : Fin 24,
    6*(4*(if (2 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairRetainedBasis 2 k*repairRetainedSelector k j)=
      ∑ k,repairRetainedRelation 2 k*repairRetainedMatrix k j := by
  decide +kernel

theorem repairRetained_relation_row_3 : ∀ j : Fin 24,
    6*(4*(if (3 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairRetainedBasis 3 k*repairRetainedSelector k j)=
      ∑ k,repairRetainedRelation 3 k*repairRetainedMatrix k j := by
  decide +kernel

theorem repairRetained_relation_row_4 : ∀ j : Fin 24,
    6*(4*(if (4 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairRetainedBasis 4 k*repairRetainedSelector k j)=
      ∑ k,repairRetainedRelation 4 k*repairRetainedMatrix k j := by
  decide +kernel

theorem repairRetained_relation_row_5 : ∀ j : Fin 24,
    6*(4*(if (5 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairRetainedBasis 5 k*repairRetainedSelector k j)=
      ∑ k,repairRetainedRelation 5 k*repairRetainedMatrix k j := by
  decide +kernel

theorem repairRetained_relation_row_6 : ∀ j : Fin 24,
    6*(4*(if (6 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairRetainedBasis 6 k*repairRetainedSelector k j)=
      ∑ k,repairRetainedRelation 6 k*repairRetainedMatrix k j := by
  decide +kernel

theorem repairRetained_relation_row_7 : ∀ j : Fin 24,
    6*(4*(if (7 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairRetainedBasis 7 k*repairRetainedSelector k j)=
      ∑ k,repairRetainedRelation 7 k*repairRetainedMatrix k j := by
  decide +kernel

theorem repairRetained_relation_row_8 : ∀ j : Fin 24,
    6*(4*(if (8 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairRetainedBasis 8 k*repairRetainedSelector k j)=
      ∑ k,repairRetainedRelation 8 k*repairRetainedMatrix k j := by
  decide +kernel

theorem repairRetained_relation_row_9 : ∀ j : Fin 24,
    6*(4*(if (9 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairRetainedBasis 9 k*repairRetainedSelector k j)=
      ∑ k,repairRetainedRelation 9 k*repairRetainedMatrix k j := by
  decide +kernel

theorem repairRetained_relation_row_10 : ∀ j : Fin 24,
    6*(4*(if (10 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairRetainedBasis 10 k*repairRetainedSelector k j)=
      ∑ k,repairRetainedRelation 10 k*repairRetainedMatrix k j := by
  decide +kernel

theorem repairRetained_relation_row_11 : ∀ j : Fin 24,
    6*(4*(if (11 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairRetainedBasis 11 k*repairRetainedSelector k j)=
      ∑ k,repairRetainedRelation 11 k*repairRetainedMatrix k j := by
  decide +kernel

theorem repairRetained_relation_row_12 : ∀ j : Fin 24,
    6*(4*(if (12 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairRetainedBasis 12 k*repairRetainedSelector k j)=
      ∑ k,repairRetainedRelation 12 k*repairRetainedMatrix k j := by
  decide +kernel

theorem repairRetained_relation_row_13 : ∀ j : Fin 24,
    6*(4*(if (13 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairRetainedBasis 13 k*repairRetainedSelector k j)=
      ∑ k,repairRetainedRelation 13 k*repairRetainedMatrix k j := by
  decide +kernel

theorem repairRetained_relation_row_14 : ∀ j : Fin 24,
    6*(4*(if (14 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairRetainedBasis 14 k*repairRetainedSelector k j)=
      ∑ k,repairRetainedRelation 14 k*repairRetainedMatrix k j := by
  decide +kernel

theorem repairRetained_relation_row_15 : ∀ j : Fin 24,
    6*(4*(if (15 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairRetainedBasis 15 k*repairRetainedSelector k j)=
      ∑ k,repairRetainedRelation 15 k*repairRetainedMatrix k j := by
  decide +kernel

theorem repairRetained_relation_row_16 : ∀ j : Fin 24,
    6*(4*(if (16 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairRetainedBasis 16 k*repairRetainedSelector k j)=
      ∑ k,repairRetainedRelation 16 k*repairRetainedMatrix k j := by
  decide +kernel

theorem repairRetained_relation_row_17 : ∀ j : Fin 24,
    6*(4*(if (17 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairRetainedBasis 17 k*repairRetainedSelector k j)=
      ∑ k,repairRetainedRelation 17 k*repairRetainedMatrix k j := by
  decide +kernel

theorem repairRetained_relation_row_18 : ∀ j : Fin 24,
    6*(4*(if (18 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairRetainedBasis 18 k*repairRetainedSelector k j)=
      ∑ k,repairRetainedRelation 18 k*repairRetainedMatrix k j := by
  decide +kernel

theorem repairRetained_relation_row_19 : ∀ j : Fin 24,
    6*(4*(if (19 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairRetainedBasis 19 k*repairRetainedSelector k j)=
      ∑ k,repairRetainedRelation 19 k*repairRetainedMatrix k j := by
  decide +kernel

theorem repairRetained_relation_row_20 : ∀ j : Fin 24,
    6*(4*(if (20 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairRetainedBasis 20 k*repairRetainedSelector k j)=
      ∑ k,repairRetainedRelation 20 k*repairRetainedMatrix k j := by
  decide +kernel

theorem repairRetained_relation_row_21 : ∀ j : Fin 24,
    6*(4*(if (21 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairRetainedBasis 21 k*repairRetainedSelector k j)=
      ∑ k,repairRetainedRelation 21 k*repairRetainedMatrix k j := by
  decide +kernel

theorem repairRetained_relation_row_22 : ∀ j : Fin 24,
    6*(4*(if (22 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairRetainedBasis 22 k*repairRetainedSelector k j)=
      ∑ k,repairRetainedRelation 22 k*repairRetainedMatrix k j := by
  decide +kernel

theorem repairRetained_relation_row_23 : ∀ j : Fin 24,
    6*(4*(if (23 : Fin 24)=j then (1 : ℤ) else 0)-
      ∑ k,repairRetainedBasis 23 k*repairRetainedSelector k j)=
      ∑ k,repairRetainedRelation 23 k*repairRetainedMatrix k j := by
  decide +kernel

theorem repairRetained_relation_entries : ∀ i j : Fin 24,
    6*(4*(if i=j then (1 : ℤ) else 0)-
      ∑ k,repairRetainedBasis i k*repairRetainedSelector k j)=
      ∑ k,repairRetainedRelation i k*repairRetainedMatrix k j := by
  intro i
  fin_cases i
  · exact repairRetained_relation_row_0
  · exact repairRetained_relation_row_1
  · exact repairRetained_relation_row_2
  · exact repairRetained_relation_row_3
  · exact repairRetained_relation_row_4
  · exact repairRetained_relation_row_5
  · exact repairRetained_relation_row_6
  · exact repairRetained_relation_row_7
  · exact repairRetained_relation_row_8
  · exact repairRetained_relation_row_9
  · exact repairRetained_relation_row_10
  · exact repairRetained_relation_row_11
  · exact repairRetained_relation_row_12
  · exact repairRetained_relation_row_13
  · exact repairRetained_relation_row_14
  · exact repairRetained_relation_row_15
  · exact repairRetained_relation_row_16
  · exact repairRetained_relation_row_17
  · exact repairRetained_relation_row_18
  · exact repairRetained_relation_row_19
  · exact repairRetained_relation_row_20
  · exact repairRetained_relation_row_21
  · exact repairRetained_relation_row_22
  · exact repairRetained_relation_row_23

theorem repairRetained_matrix_relation :
    (6 : ℤ) • ((4 : ℤ) • (1 : Matrix (Fin 24) (Fin 24) ℤ)-
      repairRetainedBasis*repairRetainedSelector)=repairRetainedRelation*repairRetainedMatrix := by
  apply Matrix.ext
  intro i j
  change 6*(4*(if i=j then (1 : ℤ) else 0)-
    ∑ k,repairRetainedBasis i k*repairRetainedSelector k j)=
    ∑ k,repairRetainedRelation i k*repairRetainedMatrix k j
  exact repairRetained_relation_entries i j

theorem repairRetainedSelector_mulVec (z : Fin 24 → ℤ) :
    repairRetainedSelector.mulVec z=fun k => z (repairRetainedPosition k) := by
  funext k
  simp [Matrix.mulVec,dotProduct,repairRetainedSelector,ite_mul]

theorem repairRetained_reconstruct (z : Fin 24 → ℤ) (hker : repairRetainedMatrix.mulVec z=0) :
    ∀ i,4*z i=repairRetainedBasis.mulVec (fun k => z (repairRetainedPosition k)) i := by
  have hh := congrArg (fun M : Matrix (Fin 24) (Fin 24) ℤ => M.mulVec z)
    repairRetained_matrix_relation
  simp only [Matrix.smul_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec,hker,Matrix.mulVec_zero] at hh
  rw [repairRetainedSelector_mulVec] at hh
  intro i
  have hi := congrFun hh i
  change 6*(4*z i-repairRetainedBasis.mulVec (fun k => z (repairRetainedPosition k)) i)=0 at hi
  omega

theorem repairRetained_boolean_row (b : Nat) (i : Fin 24) :
    repairRetainedBasis.mulVec (fun j => repairCoverU b j.val) i=repairCoverRow b i.val := by
  fin_cases i <;>
    simp [repairRetainedBasis,repairCoverRow,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring
end CompletionTheory
