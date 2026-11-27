/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapDeletionData
@[expose] public section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace CompletionTheory
theorem codeTrapRowEval_10_0 (b : Nat) :
    (codeTrapDeletionBasis 10).mulVec (fun j => codeTrapDeletionSign b j.val) 0=
      codeTrapDeletionRow 10 b 0 := by
  change (∑ j : Fin 9,(![-18,6,0,-6,-12,12,12,-12,-6] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-18)*codeTrapDeletionSign b 0 + (6)*codeTrapDeletionSign b 1 + (-6)*codeTrapDeletionSign b 3 + (-12)*codeTrapDeletionSign b 4 + (12)*codeTrapDeletionSign b 5 + (12)*codeTrapDeletionSign b 6 + (-12)*codeTrapDeletionSign b 7 + (-6)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_10_1 (b : Nat) :
    (codeTrapDeletionBasis 10).mulVec (fun j => codeTrapDeletionSign b j.val) 1=
      codeTrapDeletionRow 10 b 1 := by
  change (∑ j : Fin 9,(![-3,-5,2,-9,2,-2,2,0,7] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-3)*codeTrapDeletionSign b 0 + (-5)*codeTrapDeletionSign b 1 + (2)*codeTrapDeletionSign b 2 + (-9)*codeTrapDeletionSign b 3 + (2)*codeTrapDeletionSign b 4 + (-2)*codeTrapDeletionSign b 5 + (2)*codeTrapDeletionSign b 6 + (7)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_10_2 (b : Nat) :
    (codeTrapDeletionBasis 10).mulVec (fun j => codeTrapDeletionSign b j.val) 2=
      codeTrapDeletionRow 10 b 2 := by
  change (∑ j : Fin 9,(![-12,4,-4,-12,-16,-8,8,-12,-8] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-12)*codeTrapDeletionSign b 0 + (4)*codeTrapDeletionSign b 1 + (-4)*codeTrapDeletionSign b 2 + (-12)*codeTrapDeletionSign b 3 + (-16)*codeTrapDeletionSign b 4 + (-8)*codeTrapDeletionSign b 5 + (8)*codeTrapDeletionSign b 6 + (-12)*codeTrapDeletionSign b 7 + (-8)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_10_3 (b : Nat) :
    (codeTrapDeletionBasis 10).mulVec (fun j => codeTrapDeletionSign b j.val) 3=
      codeTrapDeletionRow 10 b 3 := by
  change (∑ j : Fin 9,(![-9,-3,-18,9,-6,-6,-6,0,-3] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-9)*codeTrapDeletionSign b 0 + (-3)*codeTrapDeletionSign b 1 + (-18)*codeTrapDeletionSign b 2 + (9)*codeTrapDeletionSign b 3 + (-6)*codeTrapDeletionSign b 4 + (-6)*codeTrapDeletionSign b 5 + (-6)*codeTrapDeletionSign b 6 + (-3)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_10_4 (b : Nat) :
    (codeTrapDeletionBasis 10).mulVec (fun j => codeTrapDeletionSign b j.val) 4=
      codeTrapDeletionRow 10 b 4 := by
  change (∑ j : Fin 9,(![-12,0,0,-12,-12,0,0,-12,-12] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-12)*codeTrapDeletionSign b 0 + (-12)*codeTrapDeletionSign b 3 + (-12)*codeTrapDeletionSign b 4 + (-12)*codeTrapDeletionSign b 7 + (-12)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_10_5 (b : Nat) :
    (codeTrapDeletionBasis 10).mulVec (fun j => codeTrapDeletionSign b j.val) 5=
      codeTrapDeletionRow 10 b 5 := by
  change (∑ j : Fin 9,(![9,-1,-2,15,10,2,-14,12,11] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(9)*codeTrapDeletionSign b 0 + (-1)*codeTrapDeletionSign b 1 + (-2)*codeTrapDeletionSign b 2 + (15)*codeTrapDeletionSign b 3 + (10)*codeTrapDeletionSign b 4 + (2)*codeTrapDeletionSign b 5 + (-14)*codeTrapDeletionSign b 6 + (12)*codeTrapDeletionSign b 7 + (11)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_10_6 (b : Nat) :
    (codeTrapDeletionBasis 10).mulVec (fun j => codeTrapDeletionSign b j.val) 6=
      codeTrapDeletionRow 10 b 6 := by
  change (∑ j : Fin 9,(![0,0,12,-12,0,0,0,-12,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(12)*codeTrapDeletionSign b 2 + (-12)*codeTrapDeletionSign b 3 + (-12)*codeTrapDeletionSign b 7
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_10_7 (b : Nat) :
    (codeTrapDeletionBasis 10).mulVec (fun j => codeTrapDeletionSign b j.val) 7=
      codeTrapDeletionRow 10 b 7 := by
  change (∑ j : Fin 9,(![21,-9,6,3,18,-6,-6,12,3] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(21)*codeTrapDeletionSign b 0 + (-9)*codeTrapDeletionSign b 1 + (6)*codeTrapDeletionSign b 2 + (3)*codeTrapDeletionSign b 3 + (18)*codeTrapDeletionSign b 4 + (-6)*codeTrapDeletionSign b 5 + (-6)*codeTrapDeletionSign b 6 + (12)*codeTrapDeletionSign b 7 + (3)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_10_8 (b : Nat) :
    (codeTrapDeletionBasis 10).mulVec (fun j => codeTrapDeletionSign b j.val) 8=
      codeTrapDeletionRow 10 b 8 := by
  change (∑ j : Fin 9,(![-18,-2,-16,6,-4,4,-4,-12,-2] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-18)*codeTrapDeletionSign b 0 + (-2)*codeTrapDeletionSign b 1 + (-16)*codeTrapDeletionSign b 2 + (6)*codeTrapDeletionSign b 3 + (-4)*codeTrapDeletionSign b 4 + (4)*codeTrapDeletionSign b 5 + (-4)*codeTrapDeletionSign b 6 + (-12)*codeTrapDeletionSign b 7 + (-2)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_10_9 (b : Nat) :
    (codeTrapDeletionBasis 10).mulVec (fun j => codeTrapDeletionSign b j.val) 9=
      codeTrapDeletionRow 10 b 9 := by
  change (∑ j : Fin 9,(![12,8,4,0,4,-4,4,12,-4] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(12)*codeTrapDeletionSign b 0 + (8)*codeTrapDeletionSign b 1 + (4)*codeTrapDeletionSign b 2 + (4)*codeTrapDeletionSign b 4 + (-4)*codeTrapDeletionSign b 5 + (4)*codeTrapDeletionSign b 6 + (12)*codeTrapDeletionSign b 7 + (-4)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_10_10 (b : Nat) :
    (codeTrapDeletionBasis 10).mulVec (fun j => codeTrapDeletionSign b j.val) 10=
      codeTrapDeletionRow 10 b 10 := by
  change (∑ j : Fin 9,(![18,-10,4,6,4,-4,-8,12,2] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(18)*codeTrapDeletionSign b 0 + (-10)*codeTrapDeletionSign b 1 + (4)*codeTrapDeletionSign b 2 + (6)*codeTrapDeletionSign b 3 + (4)*codeTrapDeletionSign b 4 + (-4)*codeTrapDeletionSign b 5 + (-8)*codeTrapDeletionSign b 6 + (12)*codeTrapDeletionSign b 7 + (2)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_10_11 (b : Nat) :
    (codeTrapDeletionBasis 10).mulVec (fun j => codeTrapDeletionSign b j.val) 11=
      codeTrapDeletionRow 10 b 11 := by
  change (∑ j : Fin 9,(![12,0,0,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(12)*codeTrapDeletionSign b 0
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_10_12 (b : Nat) :
    (codeTrapDeletionBasis 10).mulVec (fun j => codeTrapDeletionSign b j.val) 12=
      codeTrapDeletionRow 10 b 12 := by
  change (∑ j : Fin 9,(![0,12,0,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(12)*codeTrapDeletionSign b 1
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_10_13 (b : Nat) :
    (codeTrapDeletionBasis 10).mulVec (fun j => codeTrapDeletionSign b j.val) 13=
      codeTrapDeletionRow 10 b 13 := by
  change (∑ j : Fin 9,(![0,0,12,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(12)*codeTrapDeletionSign b 2
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_10_14 (b : Nat) :
    (codeTrapDeletionBasis 10).mulVec (fun j => codeTrapDeletionSign b j.val) 14=
      codeTrapDeletionRow 10 b 14 := by
  change (∑ j : Fin 9,(![0,0,0,12,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(12)*codeTrapDeletionSign b 3
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_10_15 (b : Nat) :
    (codeTrapDeletionBasis 10).mulVec (fun j => codeTrapDeletionSign b j.val) 15=
      codeTrapDeletionRow 10 b 15 := by
  change (∑ j : Fin 9,(![0,0,0,0,12,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(12)*codeTrapDeletionSign b 4
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_10_16 (b : Nat) :
    (codeTrapDeletionBasis 10).mulVec (fun j => codeTrapDeletionSign b j.val) 16=
      codeTrapDeletionRow 10 b 16 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,12,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(12)*codeTrapDeletionSign b 5
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_10_17 (b : Nat) :
    (codeTrapDeletionBasis 10).mulVec (fun j => codeTrapDeletionSign b j.val) 17=
      codeTrapDeletionRow 10 b 17 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,12,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(12)*codeTrapDeletionSign b 6
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_10_18 (b : Nat) :
    (codeTrapDeletionBasis 10).mulVec (fun j => codeTrapDeletionSign b j.val) 18=
      codeTrapDeletionRow 10 b 18 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,0,12,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(12)*codeTrapDeletionSign b 7
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_10_19 (b : Nat) :
    (codeTrapDeletionBasis 10).mulVec (fun j => codeTrapDeletionSign b j.val) 19=
      codeTrapDeletionRow 10 b 19 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,0,0,12] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(12)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

end CompletionTheory
