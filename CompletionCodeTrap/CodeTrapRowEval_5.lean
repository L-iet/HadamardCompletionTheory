/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapDeletionData
@[expose] public section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace CompletionTheory
theorem codeTrapRowEval_5_0 (b : Nat) :
    (codeTrapDeletionBasis 5).mulVec (fun j => codeTrapDeletionSign b j.val) 0=
      codeTrapDeletionRow 5 b 0 := by
  change (∑ j : Fin 9,(![-12,4,0,-4,-8,8,8,-8,-4] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-12)*codeTrapDeletionSign b 0 + (4)*codeTrapDeletionSign b 1 + (-4)*codeTrapDeletionSign b 3 + (-8)*codeTrapDeletionSign b 4 + (8)*codeTrapDeletionSign b 5 + (8)*codeTrapDeletionSign b 6 + (-8)*codeTrapDeletionSign b 7 + (-4)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_5_1 (b : Nat) :
    (codeTrapDeletionBasis 5).mulVec (fun j => codeTrapDeletionSign b j.val) 1=
      codeTrapDeletionRow 5 b 1 := by
  change (∑ j : Fin 9,(![-7,-5,-2,-1,-2,2,-2,0,3] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-7)*codeTrapDeletionSign b 0 + (-5)*codeTrapDeletionSign b 1 + (-2)*codeTrapDeletionSign b 2 + (-1)*codeTrapDeletionSign b 3 + (-2)*codeTrapDeletionSign b 4 + (2)*codeTrapDeletionSign b 5 + (-2)*codeTrapDeletionSign b 6 + (3)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_5_2 (b : Nat) :
    (codeTrapDeletionBasis 5).mulVec (fun j => codeTrapDeletionSign b j.val) 2=
      codeTrapDeletionRow 5 b 2 := by
  change (∑ j : Fin 9,(![2,6,4,-18,-4,-12,12,-8,-2] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(2)*codeTrapDeletionSign b 0 + (6)*codeTrapDeletionSign b 1 + (4)*codeTrapDeletionSign b 2 + (-18)*codeTrapDeletionSign b 3 + (-4)*codeTrapDeletionSign b 4 + (-12)*codeTrapDeletionSign b 5 + (12)*codeTrapDeletionSign b 6 + (-8)*codeTrapDeletionSign b 7 + (-2)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_5_3 (b : Nat) :
    (codeTrapDeletionBasis 5).mulVec (fun j => codeTrapDeletionSign b j.val) 3=
      codeTrapDeletionRow 5 b 3 := by
  change (∑ j : Fin 9,(![9,3,-2,-9,6,-14,6,0,3] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(9)*codeTrapDeletionSign b 0 + (3)*codeTrapDeletionSign b 1 + (-2)*codeTrapDeletionSign b 2 + (-9)*codeTrapDeletionSign b 3 + (6)*codeTrapDeletionSign b 4 + (-14)*codeTrapDeletionSign b 5 + (6)*codeTrapDeletionSign b 6 + (3)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_5_4 (b : Nat) :
    (codeTrapDeletionBasis 5).mulVec (fun j => codeTrapDeletionSign b j.val) 4=
      codeTrapDeletionRow 5 b 4 := by
  change (∑ j : Fin 9,(![-8,0,0,-8,-8,0,0,-8,-8] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-8)*codeTrapDeletionSign b 0 + (-8)*codeTrapDeletionSign b 3 + (-8)*codeTrapDeletionSign b 4 + (-8)*codeTrapDeletionSign b 7 + (-8)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_5_5 (b : Nat) :
    (codeTrapDeletionBasis 5).mulVec (fun j => codeTrapDeletionSign b j.val) 5=
      codeTrapDeletionRow 5 b 5 := by
  change (∑ j : Fin 9,(![11,1,2,5,10,-2,-6,8,9] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(11)*codeTrapDeletionSign b 0 + (1)*codeTrapDeletionSign b 1 + (2)*codeTrapDeletionSign b 2 + (5)*codeTrapDeletionSign b 3 + (10)*codeTrapDeletionSign b 4 + (-2)*codeTrapDeletionSign b 5 + (-6)*codeTrapDeletionSign b 6 + (8)*codeTrapDeletionSign b 7 + (9)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_5_6 (b : Nat) :
    (codeTrapDeletionBasis 5).mulVec (fun j => codeTrapDeletionSign b j.val) 6=
      codeTrapDeletionRow 5 b 6 := by
  change (∑ j : Fin 9,(![0,0,8,-8,0,0,0,-8,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(8)*codeTrapDeletionSign b 2 + (-8)*codeTrapDeletionSign b 3 + (-8)*codeTrapDeletionSign b 7
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_5_7 (b : Nat) :
    (codeTrapDeletionBasis 5).mulVec (fun j => codeTrapDeletionSign b j.val) 7=
      codeTrapDeletionRow 5 b 7 := by
  change (∑ j : Fin 9,(![-1,-11,-6,17,2,6,-14,8,-3] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-1)*codeTrapDeletionSign b 0 + (-11)*codeTrapDeletionSign b 1 + (-6)*codeTrapDeletionSign b 2 + (17)*codeTrapDeletionSign b 3 + (2)*codeTrapDeletionSign b 4 + (6)*codeTrapDeletionSign b 5 + (-14)*codeTrapDeletionSign b 6 + (8)*codeTrapDeletionSign b 7 + (-3)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_5_8 (b : Nat) :
    (codeTrapDeletionBasis 5).mulVec (fun j => codeTrapDeletionSign b j.val) 8=
      codeTrapDeletionRow 5 b 8 := by
  change (∑ j : Fin 9,(![-2,2,-4,-6,4,-4,4,-8,2] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-2)*codeTrapDeletionSign b 0 + (2)*codeTrapDeletionSign b 1 + (-4)*codeTrapDeletionSign b 2 + (-6)*codeTrapDeletionSign b 3 + (4)*codeTrapDeletionSign b 4 + (-4)*codeTrapDeletionSign b 5 + (4)*codeTrapDeletionSign b 6 + (-8)*codeTrapDeletionSign b 7 + (2)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_5_9 (b : Nat) :
    (codeTrapDeletionBasis 5).mulVec (fun j => codeTrapDeletionSign b j.val) 9=
      codeTrapDeletionRow 5 b 9 := by
  change (∑ j : Fin 9,(![-2,2,-4,10,-4,4,-4,8,-6] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-2)*codeTrapDeletionSign b 0 + (2)*codeTrapDeletionSign b 1 + (-4)*codeTrapDeletionSign b 2 + (10)*codeTrapDeletionSign b 3 + (-4)*codeTrapDeletionSign b 4 + (4)*codeTrapDeletionSign b 5 + (-4)*codeTrapDeletionSign b 6 + (8)*codeTrapDeletionSign b 7 + (-6)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_5_10 (b : Nat) :
    (codeTrapDeletionBasis 5).mulVec (fun j => codeTrapDeletionSign b j.val) 10=
      codeTrapDeletionRow 5 b 10 := by
  change (∑ j : Fin 9,(![2,-10,-4,14,-4,4,-12,8,-2] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(2)*codeTrapDeletionSign b 0 + (-10)*codeTrapDeletionSign b 1 + (-4)*codeTrapDeletionSign b 2 + (14)*codeTrapDeletionSign b 3 + (-4)*codeTrapDeletionSign b 4 + (4)*codeTrapDeletionSign b 5 + (-12)*codeTrapDeletionSign b 6 + (8)*codeTrapDeletionSign b 7 + (-2)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_5_11 (b : Nat) :
    (codeTrapDeletionBasis 5).mulVec (fun j => codeTrapDeletionSign b j.val) 11=
      codeTrapDeletionRow 5 b 11 := by
  change (∑ j : Fin 9,(![8,0,0,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(8)*codeTrapDeletionSign b 0
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_5_12 (b : Nat) :
    (codeTrapDeletionBasis 5).mulVec (fun j => codeTrapDeletionSign b j.val) 12=
      codeTrapDeletionRow 5 b 12 := by
  change (∑ j : Fin 9,(![0,8,0,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(8)*codeTrapDeletionSign b 1
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_5_13 (b : Nat) :
    (codeTrapDeletionBasis 5).mulVec (fun j => codeTrapDeletionSign b j.val) 13=
      codeTrapDeletionRow 5 b 13 := by
  change (∑ j : Fin 9,(![0,0,8,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(8)*codeTrapDeletionSign b 2
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_5_14 (b : Nat) :
    (codeTrapDeletionBasis 5).mulVec (fun j => codeTrapDeletionSign b j.val) 14=
      codeTrapDeletionRow 5 b 14 := by
  change (∑ j : Fin 9,(![0,0,0,8,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(8)*codeTrapDeletionSign b 3
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_5_15 (b : Nat) :
    (codeTrapDeletionBasis 5).mulVec (fun j => codeTrapDeletionSign b j.val) 15=
      codeTrapDeletionRow 5 b 15 := by
  change (∑ j : Fin 9,(![0,0,0,0,8,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(8)*codeTrapDeletionSign b 4
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_5_16 (b : Nat) :
    (codeTrapDeletionBasis 5).mulVec (fun j => codeTrapDeletionSign b j.val) 16=
      codeTrapDeletionRow 5 b 16 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,8,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(8)*codeTrapDeletionSign b 5
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_5_17 (b : Nat) :
    (codeTrapDeletionBasis 5).mulVec (fun j => codeTrapDeletionSign b j.val) 17=
      codeTrapDeletionRow 5 b 17 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,8,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(8)*codeTrapDeletionSign b 6
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_5_18 (b : Nat) :
    (codeTrapDeletionBasis 5).mulVec (fun j => codeTrapDeletionSign b j.val) 18=
      codeTrapDeletionRow 5 b 18 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,0,8,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(8)*codeTrapDeletionSign b 7
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_5_19 (b : Nat) :
    (codeTrapDeletionBasis 5).mulVec (fun j => codeTrapDeletionSign b j.val) 19=
      codeTrapDeletionRow 5 b 19 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,0,0,8] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(8)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

end CompletionTheory
