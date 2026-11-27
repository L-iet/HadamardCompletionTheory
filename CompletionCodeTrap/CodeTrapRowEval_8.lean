/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapDeletionData
@[expose] public section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace CompletionTheory
theorem codeTrapRowEval_8_0 (b : Nat) :
    (codeTrapDeletionBasis 8).mulVec (fun j => codeTrapDeletionSign b j.val) 0=
      codeTrapDeletionRow 8 b 0 := by
  change (∑ j : Fin 9,(![-6,4,8,-12,-4,4,14,-6,-2] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-6)*codeTrapDeletionSign b 0 + (4)*codeTrapDeletionSign b 1 + (8)*codeTrapDeletionSign b 2 + (-12)*codeTrapDeletionSign b 3 + (-4)*codeTrapDeletionSign b 4 + (4)*codeTrapDeletionSign b 5 + (14)*codeTrapDeletionSign b 6 + (-6)*codeTrapDeletionSign b 7 + (-2)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_8_1 (b : Nat) :
    (codeTrapDeletionBasis 8).mulVec (fun j => codeTrapDeletionSign b j.val) 1=
      codeTrapDeletionRow 8 b 1 := by
  change (∑ j : Fin 9,(![-3,-8,2,-6,2,-2,-1,3,7] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-3)*codeTrapDeletionSign b 0 + (-8)*codeTrapDeletionSign b 1 + (2)*codeTrapDeletionSign b 2 + (-6)*codeTrapDeletionSign b 3 + (2)*codeTrapDeletionSign b 4 + (-2)*codeTrapDeletionSign b 5 + (-1)*codeTrapDeletionSign b 6 + (3)*codeTrapDeletionSign b 7 + (7)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_8_2 (b : Nat) :
    (codeTrapDeletionBasis 8).mulVec (fun j => codeTrapDeletionSign b j.val) 2=
      codeTrapDeletionRow 8 b 2 := by
  change (∑ j : Fin 9,(![-12,-8,-4,0,-16,-8,-4,0,-8] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-12)*codeTrapDeletionSign b 0 + (-8)*codeTrapDeletionSign b 1 + (-4)*codeTrapDeletionSign b 2 + (-16)*codeTrapDeletionSign b 4 + (-8)*codeTrapDeletionSign b 5 + (-4)*codeTrapDeletionSign b 6 + (-8)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_8_3 (b : Nat) :
    (codeTrapDeletionBasis 8).mulVec (fun j => codeTrapDeletionSign b j.val) 3=
      codeTrapDeletionRow 8 b 3 := by
  change (∑ j : Fin 9,(![-9,-12,-18,18,-6,-6,-15,9,-3] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-9)*codeTrapDeletionSign b 0 + (-12)*codeTrapDeletionSign b 1 + (-18)*codeTrapDeletionSign b 2 + (18)*codeTrapDeletionSign b 3 + (-6)*codeTrapDeletionSign b 4 + (-6)*codeTrapDeletionSign b 5 + (-15)*codeTrapDeletionSign b 6 + (9)*codeTrapDeletionSign b 7 + (-3)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_8_4 (b : Nat) :
    (codeTrapDeletionBasis 8).mulVec (fun j => codeTrapDeletionSign b j.val) 4=
      codeTrapDeletionRow 8 b 4 := by
  change (∑ j : Fin 9,(![-12,-12,0,0,-12,0,-12,0,-12] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-12)*codeTrapDeletionSign b 0 + (-12)*codeTrapDeletionSign b 1 + (-12)*codeTrapDeletionSign b 4 + (-12)*codeTrapDeletionSign b 6 + (-12)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_8_5 (b : Nat) :
    (codeTrapDeletionBasis 8).mulVec (fun j => codeTrapDeletionSign b j.val) 5=
      codeTrapDeletionRow 8 b 5 := by
  change (∑ j : Fin 9,(![15,16,2,-6,14,-2,5,-3,13] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(15)*codeTrapDeletionSign b 0 + (16)*codeTrapDeletionSign b 1 + (2)*codeTrapDeletionSign b 2 + (-6)*codeTrapDeletionSign b 3 + (14)*codeTrapDeletionSign b 4 + (-2)*codeTrapDeletionSign b 5 + (5)*codeTrapDeletionSign b 6 + (-3)*codeTrapDeletionSign b 7 + (13)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_8_6 (b : Nat) :
    (codeTrapDeletionBasis 8).mulVec (fun j => codeTrapDeletionSign b j.val) 6=
      codeTrapDeletionRow 8 b 6 := by
  change (∑ j : Fin 9,(![6,8,16,-24,4,-4,10,-18,2] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 0 + (8)*codeTrapDeletionSign b 1 + (16)*codeTrapDeletionSign b 2 + (-24)*codeTrapDeletionSign b 3 + (4)*codeTrapDeletionSign b 4 + (-4)*codeTrapDeletionSign b 5 + (10)*codeTrapDeletionSign b 6 + (-18)*codeTrapDeletionSign b 7 + (2)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_8_7 (b : Nat) :
    (codeTrapDeletionBasis 8).mulVec (fun j => codeTrapDeletionSign b j.val) 7=
      codeTrapDeletionRow 8 b 7 := by
  change (∑ j : Fin 9,(![15,4,2,-6,14,-2,5,-3,1] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(15)*codeTrapDeletionSign b 0 + (4)*codeTrapDeletionSign b 1 + (2)*codeTrapDeletionSign b 2 + (-6)*codeTrapDeletionSign b 3 + (14)*codeTrapDeletionSign b 4 + (-2)*codeTrapDeletionSign b 5 + (5)*codeTrapDeletionSign b 6 + (-3)*codeTrapDeletionSign b 7 + (1)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_8_8 (b : Nat) :
    (codeTrapDeletionBasis 8).mulVec (fun j => codeTrapDeletionSign b j.val) 8=
      codeTrapDeletionRow 8 b 8 := by
  change (∑ j : Fin 9,(![0,4,-4,-12,8,-8,8,-12,4] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(4)*codeTrapDeletionSign b 1 + (-4)*codeTrapDeletionSign b 2 + (-12)*codeTrapDeletionSign b 3 + (8)*codeTrapDeletionSign b 4 + (-8)*codeTrapDeletionSign b 5 + (8)*codeTrapDeletionSign b 6 + (-12)*codeTrapDeletionSign b 7 + (4)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_8_9 (b : Nat) :
    (codeTrapDeletionBasis 8).mulVec (fun j => codeTrapDeletionSign b j.val) 9=
      codeTrapDeletionRow 8 b 9 := by
  change (∑ j : Fin 9,(![-6,-4,-8,24,-8,8,-14,18,-10] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-6)*codeTrapDeletionSign b 0 + (-4)*codeTrapDeletionSign b 1 + (-8)*codeTrapDeletionSign b 2 + (24)*codeTrapDeletionSign b 3 + (-8)*codeTrapDeletionSign b 4 + (8)*codeTrapDeletionSign b 5 + (-14)*codeTrapDeletionSign b 6 + (18)*codeTrapDeletionSign b 7 + (-10)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_8_10 (b : Nat) :
    (codeTrapDeletionBasis 8).mulVec (fun j => codeTrapDeletionSign b j.val) 10=
      codeTrapDeletionRow 8 b 10 := by
  change (∑ j : Fin 9,(![12,0,0,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(12)*codeTrapDeletionSign b 0
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_8_11 (b : Nat) :
    (codeTrapDeletionBasis 8).mulVec (fun j => codeTrapDeletionSign b j.val) 11=
      codeTrapDeletionRow 8 b 11 := by
  change (∑ j : Fin 9,(![0,-4,-8,12,-8,8,-8,0,-4] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-4)*codeTrapDeletionSign b 1 + (-8)*codeTrapDeletionSign b 2 + (12)*codeTrapDeletionSign b 3 + (-8)*codeTrapDeletionSign b 4 + (8)*codeTrapDeletionSign b 5 + (-8)*codeTrapDeletionSign b 6 + (-4)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_8_12 (b : Nat) :
    (codeTrapDeletionBasis 8).mulVec (fun j => codeTrapDeletionSign b j.val) 12=
      codeTrapDeletionRow 8 b 12 := by
  change (∑ j : Fin 9,(![0,12,0,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(12)*codeTrapDeletionSign b 1
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_8_13 (b : Nat) :
    (codeTrapDeletionBasis 8).mulVec (fun j => codeTrapDeletionSign b j.val) 13=
      codeTrapDeletionRow 8 b 13 := by
  change (∑ j : Fin 9,(![0,0,12,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(12)*codeTrapDeletionSign b 2
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_8_14 (b : Nat) :
    (codeTrapDeletionBasis 8).mulVec (fun j => codeTrapDeletionSign b j.val) 14=
      codeTrapDeletionRow 8 b 14 := by
  change (∑ j : Fin 9,(![0,0,0,12,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(12)*codeTrapDeletionSign b 3
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_8_15 (b : Nat) :
    (codeTrapDeletionBasis 8).mulVec (fun j => codeTrapDeletionSign b j.val) 15=
      codeTrapDeletionRow 8 b 15 := by
  change (∑ j : Fin 9,(![0,0,0,0,12,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(12)*codeTrapDeletionSign b 4
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_8_16 (b : Nat) :
    (codeTrapDeletionBasis 8).mulVec (fun j => codeTrapDeletionSign b j.val) 16=
      codeTrapDeletionRow 8 b 16 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,12,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(12)*codeTrapDeletionSign b 5
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_8_17 (b : Nat) :
    (codeTrapDeletionBasis 8).mulVec (fun j => codeTrapDeletionSign b j.val) 17=
      codeTrapDeletionRow 8 b 17 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,12,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(12)*codeTrapDeletionSign b 6
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_8_18 (b : Nat) :
    (codeTrapDeletionBasis 8).mulVec (fun j => codeTrapDeletionSign b j.val) 18=
      codeTrapDeletionRow 8 b 18 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,0,12,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(12)*codeTrapDeletionSign b 7
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_8_19 (b : Nat) :
    (codeTrapDeletionBasis 8).mulVec (fun j => codeTrapDeletionSign b j.val) 19=
      codeTrapDeletionRow 8 b 19 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,0,0,12] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(12)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

end CompletionTheory
