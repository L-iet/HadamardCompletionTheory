/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionRepair.RepairBatchesComplete
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
@[expose] public section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
namespace CompletionTheory
def repairKernelNumerators : Matrix (Fin 24) (Fin 12) ℤ :=
![
  ![4,-8,4,-8,-12,4,-4,8,-4,4,8,8],
  ![-8,0,0,2,2,0,-4,-8,-4,-2,0,2],
  ![-4,-4,-4,-4,4,-4,-8,-12,0,-8,-8,-8],
  ![6,4,2,3,-3,2,10,12,4,7,6,3],
  ![0,0,-4,2,2,-4,4,0,0,2,-4,-2],
  ![2,8,2,5,7,2,6,4,8,1,2,1],
  ![0,-4,4,-2,-6,0,-4,4,-4,2,4,2],
  ![-8,12,-4,10,10,-4,8,-4,0,6,0,2],
  ![-2,-4,-2,-5,1,-2,-6,-8,0,-9,-10,-9],
  ![-4,12,-4,12,12,0,8,-4,4,0,0,0],
  ![10,-16,6,-15,-17,6,-10,8,-4,-3,2,1],
  ![4,0,0,0,0,0,0,0,0,0,0,0],
  ![0,-4,-4,-4,-4,-4,-4,-4,-4,-4,-4,-4],
  ![0,4,0,0,0,0,0,0,0,0,0,0],
  ![0,0,4,0,0,0,0,0,0,0,0,0],
  ![0,0,0,4,0,0,0,0,0,0,0,0],
  ![0,0,0,0,4,0,0,0,0,0,0,0],
  ![0,0,0,0,0,4,0,0,0,0,0,0],
  ![0,0,0,0,0,0,4,0,0,0,0,0],
  ![0,0,0,0,0,0,0,4,0,0,0,0],
  ![0,0,0,0,0,0,0,0,4,0,0,0],
  ![0,0,0,0,0,0,0,0,0,4,0,0],
  ![0,0,0,0,0,0,0,0,0,0,4,0],
  ![0,0,0,0,0,0,0,0,0,0,0,4]
]

def repairShortFreeVector (e : Fin 13) (b : Fin 2048) (j : Fin 12) : ℤ :=
  let sign : ℤ := if j.val=0 then 1 else if b.val.testBit (j.val-1) then -1 else 1
  if e.val=j.val+1 then 3*sign else sign

def repairShortNumerators (e : Fin 13) (b : Fin 2048) : Fin 24 → ℤ :=
  repairKernelNumerators.mulVec (repairShortFreeVector e b)


theorem repairShortNumerators_eq_boolean (e : Fin 13) (b : Fin 2048) (i : Fin 24) :
    repairShortNumerators e b i=repairBooleanRow e.val b.val i.val := by
  fin_cases i <;>
    simp [repairShortNumerators,repairKernelNumerators,repairShortFreeVector,
      repairBooleanRow,repairBooleanU,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem repairShortNumerators_odd_energy_floor :
    ∀ (e : Fin 13) (b : Fin 2048),
      (∀ i,(repairShortNumerators e b i)%8=4) →
      640≤∑ i,(repairShortNumerators e b i)^2 := by
  intro e b hmod
  simp_rw [repairShortNumerators_eq_boolean] at hmod ⊢
  have hm0 : repairBooleanRow e.val b.val 0%8=4 := hmod (0 : Fin 24)
  have hm1 : repairBooleanRow e.val b.val 1%8=4 := hmod (1 : Fin 24)
  have hm2 : repairBooleanRow e.val b.val 2%8=4 := hmod (2 : Fin 24)
  have hm3 : repairBooleanRow e.val b.val 3%8=4 := hmod (3 : Fin 24)
  have hm4 : repairBooleanRow e.val b.val 4%8=4 := hmod (4 : Fin 24)
  have hm5 : repairBooleanRow e.val b.val 5%8=4 := hmod (5 : Fin 24)
  have hm6 : repairBooleanRow e.val b.val 6%8=4 := hmod (6 : Fin 24)
  have hm7 : repairBooleanRow e.val b.val 7%8=4 := hmod (7 : Fin 24)
  have hm8 : repairBooleanRow e.val b.val 8%8=4 := hmod (8 : Fin 24)
  have hm9 : repairBooleanRow e.val b.val 9%8=4 := hmod (9 : Fin 24)
  have hm10 : repairBooleanRow e.val b.val 10%8=4 := hmod (10 : Fin 24)
  have hm11 : repairBooleanRow e.val b.val 11%8=4 := hmod (11 : Fin 24)
  have hm12 : repairBooleanRow e.val b.val 12%8=4 := hmod (12 : Fin 24)
  have hm13 : repairBooleanRow e.val b.val 13%8=4 := hmod (13 : Fin 24)
  have hm14 : repairBooleanRow e.val b.val 14%8=4 := hmod (14 : Fin 24)
  have hm15 : repairBooleanRow e.val b.val 15%8=4 := hmod (15 : Fin 24)
  have hm16 : repairBooleanRow e.val b.val 16%8=4 := hmod (16 : Fin 24)
  have hm17 : repairBooleanRow e.val b.val 17%8=4 := hmod (17 : Fin 24)
  have hm18 : repairBooleanRow e.val b.val 18%8=4 := hmod (18 : Fin 24)
  have hm19 : repairBooleanRow e.val b.val 19%8=4 := hmod (19 : Fin 24)
  have hm20 : repairBooleanRow e.val b.val 20%8=4 := hmod (20 : Fin 24)
  have hm21 : repairBooleanRow e.val b.val 21%8=4 := hmod (21 : Fin 24)
  have hm22 : repairBooleanRow e.val b.val 22%8=4 := hmod (22 : Fin 24)
  have hm23 : repairBooleanRow e.val b.val 23%8=4 := hmod (23 : Fin 24)
  have henergy : (640 : ℤ)≤repairBooleanRow e.val b.val 0*repairBooleanRow e.val b.val 0 + repairBooleanRow e.val b.val 1*repairBooleanRow e.val b.val 1 + repairBooleanRow e.val b.val 2*repairBooleanRow e.val b.val 2 + repairBooleanRow e.val b.val 3*repairBooleanRow e.val b.val 3 + repairBooleanRow e.val b.val 4*repairBooleanRow e.val b.val 4 + repairBooleanRow e.val b.val 5*repairBooleanRow e.val b.val 5 + repairBooleanRow e.val b.val 6*repairBooleanRow e.val b.val 6 + repairBooleanRow e.val b.val 7*repairBooleanRow e.val b.val 7 + repairBooleanRow e.val b.val 8*repairBooleanRow e.val b.val 8 + repairBooleanRow e.val b.val 9*repairBooleanRow e.val b.val 9 + repairBooleanRow e.val b.val 10*repairBooleanRow e.val b.val 10 + repairBooleanRow e.val b.val 11*repairBooleanRow e.val b.val 11 + repairBooleanRow e.val b.val 12*repairBooleanRow e.val b.val 12 + repairBooleanRow e.val b.val 13*repairBooleanRow e.val b.val 13 + repairBooleanRow e.val b.val 14*repairBooleanRow e.val b.val 14 + repairBooleanRow e.val b.val 15*repairBooleanRow e.val b.val 15 + repairBooleanRow e.val b.val 16*repairBooleanRow e.val b.val 16 + repairBooleanRow e.val b.val 17*repairBooleanRow e.val b.val 17 + repairBooleanRow e.val b.val 18*repairBooleanRow e.val b.val 18 + repairBooleanRow e.val b.val 19*repairBooleanRow e.val b.val 19 + repairBooleanRow e.val b.val 20*repairBooleanRow e.val b.val 20 + repairBooleanRow e.val b.val 21*repairBooleanRow e.val b.val 21 + repairBooleanRow e.val b.val 22*repairBooleanRow e.val b.val 22 + repairBooleanRow e.val b.val 23*repairBooleanRow e.val b.val 23 := by
    simpa [repairBooleanOne,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14,hm15,hm16,hm17,hm18,hm19,hm20,hm21,hm22,hm23] using repair_boolean_all e b
  simpa [Fin.sum_univ_succ,pow_two,add_assoc] using henergy

end CompletionTheory
