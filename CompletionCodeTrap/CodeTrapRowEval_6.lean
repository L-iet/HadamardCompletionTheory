/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapDeletionData
@[expose] public section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace CompletionTheory
theorem codeTrapRowEval_6_0 (b : Nat) :
    (codeTrapDeletionBasis 6).mulVec (fun j => codeTrapDeletionSign b j.val) 0=
      codeTrapDeletionRow 6 b 0 := by
  change (∑ j : Fin 9,(![-6,0,-2,2,-4,4,0,-2,-2] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-6)*codeTrapDeletionSign b 0 + (-2)*codeTrapDeletionSign b 2 + (2)*codeTrapDeletionSign b 3 + (-4)*codeTrapDeletionSign b 4 + (4)*codeTrapDeletionSign b 5 + (-2)*codeTrapDeletionSign b 7 + (-2)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_6_1 (b : Nat) :
    (codeTrapDeletionBasis 6).mulVec (fun j => codeTrapDeletionSign b j.val) 1=
      codeTrapDeletionRow 6 b 1 := by
  change (∑ j : Fin 9,(![-7,-3,-4,5,-4,4,-4,0,-1] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-7)*codeTrapDeletionSign b 0 + (-3)*codeTrapDeletionSign b 1 + (-4)*codeTrapDeletionSign b 2 + (5)*codeTrapDeletionSign b 3 + (-4)*codeTrapDeletionSign b 4 + (4)*codeTrapDeletionSign b 5 + (-4)*codeTrapDeletionSign b 6 + (-1)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_6_2 (b : Nat) :
    (codeTrapDeletionBasis 6).mulVec (fun j => codeTrapDeletionSign b j.val) 2=
      codeTrapDeletionRow 6 b 2 := by
  change (∑ j : Fin 9,(![2,2,2,-6,0,-4,4,-2,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(2)*codeTrapDeletionSign b 0 + (2)*codeTrapDeletionSign b 1 + (2)*codeTrapDeletionSign b 2 + (-6)*codeTrapDeletionSign b 3 + (-4)*codeTrapDeletionSign b 5 + (4)*codeTrapDeletionSign b 6 + (-2)*codeTrapDeletionSign b 7
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_6_3 (b : Nat) :
    (codeTrapDeletionBasis 6).mulVec (fun j => codeTrapDeletionSign b j.val) 3=
      codeTrapDeletionRow 6 b 3 := by
  change (∑ j : Fin 9,(![9,3,4,-9,6,-8,6,0,3] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(9)*codeTrapDeletionSign b 0 + (3)*codeTrapDeletionSign b 1 + (4)*codeTrapDeletionSign b 2 + (-9)*codeTrapDeletionSign b 3 + (6)*codeTrapDeletionSign b 4 + (-8)*codeTrapDeletionSign b 5 + (6)*codeTrapDeletionSign b 6 + (3)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_6_4 (b : Nat) :
    (codeTrapDeletionBasis 6).mulVec (fun j => codeTrapDeletionSign b j.val) 4=
      codeTrapDeletionRow 6 b 4 := by
  change (∑ j : Fin 9,(![-8,-2,-4,4,-6,4,-4,-2,-4] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-8)*codeTrapDeletionSign b 0 + (-2)*codeTrapDeletionSign b 1 + (-4)*codeTrapDeletionSign b 2 + (4)*codeTrapDeletionSign b 3 + (-6)*codeTrapDeletionSign b 4 + (4)*codeTrapDeletionSign b 5 + (-4)*codeTrapDeletionSign b 6 + (-2)*codeTrapDeletionSign b 7 + (-4)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_6_5 (b : Nat) :
    (codeTrapDeletionBasis 6).mulVec (fun j => codeTrapDeletionSign b j.val) 5=
      codeTrapDeletionRow 6 b 5 := by
  change (∑ j : Fin 9,(![-1,-1,-2,5,0,2,-4,2,1] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-1)*codeTrapDeletionSign b 0 + (-1)*codeTrapDeletionSign b 1 + (-2)*codeTrapDeletionSign b 2 + (5)*codeTrapDeletionSign b 3 + (2)*codeTrapDeletionSign b 5 + (-4)*codeTrapDeletionSign b 6 + (2)*codeTrapDeletionSign b 7 + (1)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_6_6 (b : Nat) :
    (codeTrapDeletionBasis 6).mulVec (fun j => codeTrapDeletionSign b j.val) 6=
      codeTrapDeletionRow 6 b 6 := by
  change (∑ j : Fin 9,(![-12,-4,-6,10,-8,8,-8,-2,-4] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-12)*codeTrapDeletionSign b 0 + (-4)*codeTrapDeletionSign b 1 + (-6)*codeTrapDeletionSign b 2 + (10)*codeTrapDeletionSign b 3 + (-8)*codeTrapDeletionSign b 4 + (8)*codeTrapDeletionSign b 5 + (-8)*codeTrapDeletionSign b 6 + (-2)*codeTrapDeletionSign b 7 + (-4)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_6_7 (b : Nat) :
    (codeTrapDeletionBasis 6).mulVec (fun j => codeTrapDeletionSign b j.val) 7=
      codeTrapDeletionRow 6 b 7 := by
  change (∑ j : Fin 9,(![11,1,6,-7,8,-6,4,2,3] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(11)*codeTrapDeletionSign b 0 + (1)*codeTrapDeletionSign b 1 + (6)*codeTrapDeletionSign b 2 + (-7)*codeTrapDeletionSign b 3 + (8)*codeTrapDeletionSign b 4 + (-6)*codeTrapDeletionSign b 5 + (4)*codeTrapDeletionSign b 6 + (2)*codeTrapDeletionSign b 7 + (3)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_6_8 (b : Nat) :
    (codeTrapDeletionBasis 6).mulVec (fun j => codeTrapDeletionSign b j.val) 8=
      codeTrapDeletionRow 6 b 8 := by
  change (∑ j : Fin 9,(![-8,-2,-6,6,-4,4,-4,-2,-2] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-8)*codeTrapDeletionSign b 0 + (-2)*codeTrapDeletionSign b 1 + (-6)*codeTrapDeletionSign b 2 + (6)*codeTrapDeletionSign b 3 + (-4)*codeTrapDeletionSign b 4 + (4)*codeTrapDeletionSign b 5 + (-4)*codeTrapDeletionSign b 6 + (-2)*codeTrapDeletionSign b 7 + (-2)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_6_9 (b : Nat) :
    (codeTrapDeletionBasis 6).mulVec (fun j => codeTrapDeletionSign b j.val) 9=
      codeTrapDeletionRow 6 b 9 := by
  change (∑ j : Fin 9,(![4,2,2,-2,2,-2,2,2,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(4)*codeTrapDeletionSign b 0 + (2)*codeTrapDeletionSign b 1 + (2)*codeTrapDeletionSign b 2 + (-2)*codeTrapDeletionSign b 3 + (2)*codeTrapDeletionSign b 4 + (-2)*codeTrapDeletionSign b 5 + (2)*codeTrapDeletionSign b 6 + (2)*codeTrapDeletionSign b 7
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_6_10 (b : Nat) :
    (codeTrapDeletionBasis 6).mulVec (fun j => codeTrapDeletionSign b j.val) 10=
      codeTrapDeletionRow 6 b 10 := by
  change (∑ j : Fin 9,(![14,2,8,-10,8,-8,6,2,4] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(14)*codeTrapDeletionSign b 0 + (2)*codeTrapDeletionSign b 1 + (8)*codeTrapDeletionSign b 2 + (-10)*codeTrapDeletionSign b 3 + (8)*codeTrapDeletionSign b 4 + (-8)*codeTrapDeletionSign b 5 + (6)*codeTrapDeletionSign b 6 + (2)*codeTrapDeletionSign b 7 + (4)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_6_11 (b : Nat) :
    (codeTrapDeletionBasis 6).mulVec (fun j => codeTrapDeletionSign b j.val) 11=
      codeTrapDeletionRow 6 b 11 := by
  change (∑ j : Fin 9,(![2,0,0,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(2)*codeTrapDeletionSign b 0
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_6_12 (b : Nat) :
    (codeTrapDeletionBasis 6).mulVec (fun j => codeTrapDeletionSign b j.val) 12=
      codeTrapDeletionRow 6 b 12 := by
  change (∑ j : Fin 9,(![0,2,0,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(2)*codeTrapDeletionSign b 1
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_6_13 (b : Nat) :
    (codeTrapDeletionBasis 6).mulVec (fun j => codeTrapDeletionSign b j.val) 13=
      codeTrapDeletionRow 6 b 13 := by
  change (∑ j : Fin 9,(![0,0,2,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(2)*codeTrapDeletionSign b 2
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_6_14 (b : Nat) :
    (codeTrapDeletionBasis 6).mulVec (fun j => codeTrapDeletionSign b j.val) 14=
      codeTrapDeletionRow 6 b 14 := by
  change (∑ j : Fin 9,(![0,0,0,2,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(2)*codeTrapDeletionSign b 3
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_6_15 (b : Nat) :
    (codeTrapDeletionBasis 6).mulVec (fun j => codeTrapDeletionSign b j.val) 15=
      codeTrapDeletionRow 6 b 15 := by
  change (∑ j : Fin 9,(![0,0,0,0,2,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(2)*codeTrapDeletionSign b 4
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_6_16 (b : Nat) :
    (codeTrapDeletionBasis 6).mulVec (fun j => codeTrapDeletionSign b j.val) 16=
      codeTrapDeletionRow 6 b 16 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,2,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(2)*codeTrapDeletionSign b 5
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_6_17 (b : Nat) :
    (codeTrapDeletionBasis 6).mulVec (fun j => codeTrapDeletionSign b j.val) 17=
      codeTrapDeletionRow 6 b 17 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,2,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(2)*codeTrapDeletionSign b 6
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_6_18 (b : Nat) :
    (codeTrapDeletionBasis 6).mulVec (fun j => codeTrapDeletionSign b j.val) 18=
      codeTrapDeletionRow 6 b 18 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,0,2,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(2)*codeTrapDeletionSign b 7
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_6_19 (b : Nat) :
    (codeTrapDeletionBasis 6).mulVec (fun j => codeTrapDeletionSign b j.val) 19=
      codeTrapDeletionRow 6 b 19 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,0,0,2] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(2)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

end CompletionTheory
