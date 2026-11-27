/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapDeletionData
@[expose] public section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace CompletionTheory
theorem codeTrapRowEval_4_0 (b : Nat) :
    (codeTrapDeletionBasis 4).mulVec (fun j => codeTrapDeletionSign b j.val) 0=
      codeTrapDeletionRow 4 b 0 := by
  change (∑ j : Fin 9,(![-18,-18,-6,24,-12,12,-18,12,-6] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-18)*codeTrapDeletionSign b 0 + (-18)*codeTrapDeletionSign b 1 + (-6)*codeTrapDeletionSign b 2 + (24)*codeTrapDeletionSign b 3 + (-12)*codeTrapDeletionSign b 4 + (12)*codeTrapDeletionSign b 5 + (-18)*codeTrapDeletionSign b 6 + (12)*codeTrapDeletionSign b 7 + (-6)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_4_1 (b : Nat) :
    (codeTrapDeletionBasis 4).mulVec (fun j => codeTrapDeletionSign b j.val) 1=
      codeTrapDeletionRow 4 b 1 := by
  change (∑ j : Fin 9,(![-9,-14,-4,12,-4,4,-13,9,1] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-9)*codeTrapDeletionSign b 0 + (-14)*codeTrapDeletionSign b 1 + (-4)*codeTrapDeletionSign b 2 + (12)*codeTrapDeletionSign b 3 + (-4)*codeTrapDeletionSign b 4 + (4)*codeTrapDeletionSign b 5 + (-13)*codeTrapDeletionSign b 6 + (9)*codeTrapDeletionSign b 7 + (1)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_4_2 (b : Nat) :
    (codeTrapDeletionBasis 4).mulVec (fun j => codeTrapDeletionSign b j.val) 2=
      codeTrapDeletionRow 4 b 2 := by
  change (∑ j : Fin 9,(![-6,-4,-2,0,-8,-4,-2,0,-4] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-6)*codeTrapDeletionSign b 0 + (-4)*codeTrapDeletionSign b 1 + (-2)*codeTrapDeletionSign b 2 + (-8)*codeTrapDeletionSign b 4 + (-4)*codeTrapDeletionSign b 5 + (-2)*codeTrapDeletionSign b 6 + (-4)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_4_3 (b : Nat) :
    (codeTrapDeletionBasis 4).mulVec (fun j => codeTrapDeletionSign b j.val) 3=
      codeTrapDeletionRow 4 b 3 := by
  change (∑ j : Fin 9,(![3,4,-4,-6,2,-8,5,-3,1] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(3)*codeTrapDeletionSign b 0 + (4)*codeTrapDeletionSign b 1 + (-4)*codeTrapDeletionSign b 2 + (-6)*codeTrapDeletionSign b 3 + (2)*codeTrapDeletionSign b 4 + (-8)*codeTrapDeletionSign b 5 + (5)*codeTrapDeletionSign b 6 + (-3)*codeTrapDeletionSign b 7 + (1)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_4_4 (b : Nat) :
    (codeTrapDeletionBasis 4).mulVec (fun j => codeTrapDeletionSign b j.val) 4=
      codeTrapDeletionRow 4 b 4 := by
  change (∑ j : Fin 9,(![-6,-6,0,0,-6,0,-6,0,-6] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-6)*codeTrapDeletionSign b 0 + (-6)*codeTrapDeletionSign b 1 + (-6)*codeTrapDeletionSign b 4 + (-6)*codeTrapDeletionSign b 6 + (-6)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_4_5 (b : Nat) :
    (codeTrapDeletionBasis 4).mulVec (fun j => codeTrapDeletionSign b j.val) 5=
      codeTrapDeletionRow 4 b 5 := by
  change (∑ j : Fin 9,(![15,18,6,-18,12,-6,15,-9,9] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(15)*codeTrapDeletionSign b 0 + (18)*codeTrapDeletionSign b 1 + (6)*codeTrapDeletionSign b 2 + (-18)*codeTrapDeletionSign b 3 + (12)*codeTrapDeletionSign b 4 + (-6)*codeTrapDeletionSign b 5 + (15)*codeTrapDeletionSign b 6 + (-9)*codeTrapDeletionSign b 7 + (9)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_4_6 (b : Nat) :
    (codeTrapDeletionBasis 4).mulVec (fun j => codeTrapDeletionSign b j.val) 6=
      codeTrapDeletionRow 4 b 6 := by
  change (∑ j : Fin 9,(![-12,-16,-2,18,-8,8,-20,6,-4] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-12)*codeTrapDeletionSign b 0 + (-16)*codeTrapDeletionSign b 1 + (-2)*codeTrapDeletionSign b 2 + (18)*codeTrapDeletionSign b 3 + (-8)*codeTrapDeletionSign b 4 + (8)*codeTrapDeletionSign b 5 + (-20)*codeTrapDeletionSign b 6 + (6)*codeTrapDeletionSign b 7 + (-4)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_4_7 (b : Nat) :
    (codeTrapDeletionBasis 4).mulVec (fun j => codeTrapDeletionSign b j.val) 7=
      codeTrapDeletionRow 4 b 7 := by
  change (∑ j : Fin 9,(![15,12,6,-18,12,-6,15,-9,3] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(15)*codeTrapDeletionSign b 0 + (12)*codeTrapDeletionSign b 1 + (6)*codeTrapDeletionSign b 2 + (-18)*codeTrapDeletionSign b 3 + (12)*codeTrapDeletionSign b 4 + (-6)*codeTrapDeletionSign b 5 + (15)*codeTrapDeletionSign b 6 + (-9)*codeTrapDeletionSign b 7 + (3)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_4_8 (b : Nat) :
    (codeTrapDeletionBasis 4).mulVec (fun j => codeTrapDeletionSign b j.val) 8=
      codeTrapDeletionRow 4 b 8 := by
  change (∑ j : Fin 9,(![0,2,-2,-6,4,-4,4,-6,2] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(2)*codeTrapDeletionSign b 1 + (-2)*codeTrapDeletionSign b 2 + (-6)*codeTrapDeletionSign b 3 + (4)*codeTrapDeletionSign b 4 + (-4)*codeTrapDeletionSign b 5 + (4)*codeTrapDeletionSign b 6 + (-6)*codeTrapDeletionSign b 7 + (2)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_4_9 (b : Nat) :
    (codeTrapDeletionBasis 4).mulVec (fun j => codeTrapDeletionSign b j.val) 9=
      codeTrapDeletionRow 4 b 9 := by
  change (∑ j : Fin 9,(![12,18,6,-18,6,-6,18,-6,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(12)*codeTrapDeletionSign b 0 + (18)*codeTrapDeletionSign b 1 + (6)*codeTrapDeletionSign b 2 + (-18)*codeTrapDeletionSign b 3 + (6)*codeTrapDeletionSign b 4 + (-6)*codeTrapDeletionSign b 5 + (18)*codeTrapDeletionSign b 6 + (-6)*codeTrapDeletionSign b 7
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_4_10 (b : Nat) :
    (codeTrapDeletionBasis 4).mulVec (fun j => codeTrapDeletionSign b j.val) 10=
      codeTrapDeletionRow 4 b 10 := by
  change (∑ j : Fin 9,(![6,0,0,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 0
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_4_11 (b : Nat) :
    (codeTrapDeletionBasis 4).mulVec (fun j => codeTrapDeletionSign b j.val) 11=
      codeTrapDeletionRow 4 b 11 := by
  change (∑ j : Fin 9,(![0,-2,-4,6,-4,4,-4,0,-2] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-2)*codeTrapDeletionSign b 1 + (-4)*codeTrapDeletionSign b 2 + (6)*codeTrapDeletionSign b 3 + (-4)*codeTrapDeletionSign b 4 + (4)*codeTrapDeletionSign b 5 + (-4)*codeTrapDeletionSign b 6 + (-2)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_4_12 (b : Nat) :
    (codeTrapDeletionBasis 4).mulVec (fun j => codeTrapDeletionSign b j.val) 12=
      codeTrapDeletionRow 4 b 12 := by
  change (∑ j : Fin 9,(![0,6,0,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 1
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_4_13 (b : Nat) :
    (codeTrapDeletionBasis 4).mulVec (fun j => codeTrapDeletionSign b j.val) 13=
      codeTrapDeletionRow 4 b 13 := by
  change (∑ j : Fin 9,(![0,0,6,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 2
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_4_14 (b : Nat) :
    (codeTrapDeletionBasis 4).mulVec (fun j => codeTrapDeletionSign b j.val) 14=
      codeTrapDeletionRow 4 b 14 := by
  change (∑ j : Fin 9,(![0,0,0,6,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 3
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_4_15 (b : Nat) :
    (codeTrapDeletionBasis 4).mulVec (fun j => codeTrapDeletionSign b j.val) 15=
      codeTrapDeletionRow 4 b 15 := by
  change (∑ j : Fin 9,(![0,0,0,0,6,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 4
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_4_16 (b : Nat) :
    (codeTrapDeletionBasis 4).mulVec (fun j => codeTrapDeletionSign b j.val) 16=
      codeTrapDeletionRow 4 b 16 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,6,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 5
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_4_17 (b : Nat) :
    (codeTrapDeletionBasis 4).mulVec (fun j => codeTrapDeletionSign b j.val) 17=
      codeTrapDeletionRow 4 b 17 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,6,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 6
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_4_18 (b : Nat) :
    (codeTrapDeletionBasis 4).mulVec (fun j => codeTrapDeletionSign b j.val) 18=
      codeTrapDeletionRow 4 b 18 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,0,6,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 7
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_4_19 (b : Nat) :
    (codeTrapDeletionBasis 4).mulVec (fun j => codeTrapDeletionSign b j.val) 19=
      codeTrapDeletionRow 4 b 19 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,0,0,6] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

end CompletionTheory
