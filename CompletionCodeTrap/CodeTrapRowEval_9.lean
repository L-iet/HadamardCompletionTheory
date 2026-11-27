/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapDeletionData
@[expose] public section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace CompletionTheory
theorem codeTrapRowEval_9_0 (b : Nat) :
    (codeTrapDeletionBasis 9).mulVec (fun j => codeTrapDeletionSign b j.val) 0=
      codeTrapDeletionRow 9 b 0 := by
  change (∑ j : Fin 9,(![-6,2,0,-2,-4,4,4,-4,-2] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-6)*codeTrapDeletionSign b 0 + (2)*codeTrapDeletionSign b 1 + (-2)*codeTrapDeletionSign b 3 + (-4)*codeTrapDeletionSign b 4 + (4)*codeTrapDeletionSign b 5 + (4)*codeTrapDeletionSign b 6 + (-4)*codeTrapDeletionSign b 7 + (-2)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_9_1 (b : Nat) :
    (codeTrapDeletionBasis 9).mulVec (fun j => codeTrapDeletionSign b j.val) 1=
      codeTrapDeletionRow 9 b 1 := by
  change (∑ j : Fin 9,(![-11,-5,-6,7,-6,6,-6,0,-1] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-11)*codeTrapDeletionSign b 0 + (-5)*codeTrapDeletionSign b 1 + (-6)*codeTrapDeletionSign b 2 + (7)*codeTrapDeletionSign b 3 + (-6)*codeTrapDeletionSign b 4 + (6)*codeTrapDeletionSign b 5 + (-6)*codeTrapDeletionSign b 6 + (-1)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_9_2 (b : Nat) :
    (codeTrapDeletionBasis 9).mulVec (fun j => codeTrapDeletionSign b j.val) 2=
      codeTrapDeletionRow 9 b 2 := by
  change (∑ j : Fin 9,(![-14,-2,-8,6,-12,4,-4,-4,-6] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-14)*codeTrapDeletionSign b 0 + (-2)*codeTrapDeletionSign b 1 + (-8)*codeTrapDeletionSign b 2 + (6)*codeTrapDeletionSign b 3 + (-12)*codeTrapDeletionSign b 4 + (4)*codeTrapDeletionSign b 5 + (-4)*codeTrapDeletionSign b 6 + (-4)*codeTrapDeletionSign b 7 + (-6)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_9_3 (b : Nat) :
    (codeTrapDeletionBasis 9).mulVec (fun j => codeTrapDeletionSign b j.val) 3=
      codeTrapDeletionRow 9 b 3 := by
  change (∑ j : Fin 9,(![-3,-1,-6,3,-2,-2,-2,0,-1] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-3)*codeTrapDeletionSign b 0 + (-1)*codeTrapDeletionSign b 1 + (-6)*codeTrapDeletionSign b 2 + (3)*codeTrapDeletionSign b 3 + (-2)*codeTrapDeletionSign b 4 + (-2)*codeTrapDeletionSign b 5 + (-2)*codeTrapDeletionSign b 6 + (-1)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_9_4 (b : Nat) :
    (codeTrapDeletionBasis 9).mulVec (fun j => codeTrapDeletionSign b j.val) 4=
      codeTrapDeletionRow 9 b 4 := by
  change (∑ j : Fin 9,(![-4,0,0,-4,-4,0,0,-4,-4] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-4)*codeTrapDeletionSign b 0 + (-4)*codeTrapDeletionSign b 3 + (-4)*codeTrapDeletionSign b 4 + (-4)*codeTrapDeletionSign b 7 + (-4)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_9_5 (b : Nat) :
    (codeTrapDeletionBasis 9).mulVec (fun j => codeTrapDeletionSign b j.val) 5=
      codeTrapDeletionRow 9 b 5 := by
  change (∑ j : Fin 9,(![13,3,6,-5,10,-6,2,4,7] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(13)*codeTrapDeletionSign b 0 + (3)*codeTrapDeletionSign b 1 + (6)*codeTrapDeletionSign b 2 + (-5)*codeTrapDeletionSign b 3 + (10)*codeTrapDeletionSign b 4 + (-6)*codeTrapDeletionSign b 5 + (2)*codeTrapDeletionSign b 6 + (4)*codeTrapDeletionSign b 7 + (7)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_9_6 (b : Nat) :
    (codeTrapDeletionBasis 9).mulVec (fun j => codeTrapDeletionSign b j.val) 6=
      codeTrapDeletionRow 9 b 6 := by
  change (∑ j : Fin 9,(![0,0,4,-4,0,0,0,-4,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(4)*codeTrapDeletionSign b 2 + (-4)*codeTrapDeletionSign b 3 + (-4)*codeTrapDeletionSign b 7
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_9_7 (b : Nat) :
    (codeTrapDeletionBasis 9).mulVec (fun j => codeTrapDeletionSign b j.val) 7=
      codeTrapDeletionRow 9 b 7 := by
  change (∑ j : Fin 9,(![7,-3,2,1,6,-2,-2,4,1] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(7)*codeTrapDeletionSign b 0 + (-3)*codeTrapDeletionSign b 1 + (2)*codeTrapDeletionSign b 2 + (1)*codeTrapDeletionSign b 3 + (6)*codeTrapDeletionSign b 4 + (-2)*codeTrapDeletionSign b 5 + (-2)*codeTrapDeletionSign b 6 + (4)*codeTrapDeletionSign b 7 + (1)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_9_8 (b : Nat) :
    (codeTrapDeletionBasis 9).mulVec (fun j => codeTrapDeletionSign b j.val) 8=
      codeTrapDeletionRow 9 b 8 := by
  change (∑ j : Fin 9,(![-16,-4,-12,12,-8,8,-8,-4,-4] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-16)*codeTrapDeletionSign b 0 + (-4)*codeTrapDeletionSign b 1 + (-12)*codeTrapDeletionSign b 2 + (12)*codeTrapDeletionSign b 3 + (-8)*codeTrapDeletionSign b 4 + (8)*codeTrapDeletionSign b 5 + (-8)*codeTrapDeletionSign b 6 + (-4)*codeTrapDeletionSign b 7 + (-4)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_9_9 (b : Nat) :
    (codeTrapDeletionBasis 9).mulVec (fun j => codeTrapDeletionSign b j.val) 9=
      codeTrapDeletionRow 9 b 9 := by
  change (∑ j : Fin 9,(![14,6,8,-10,8,-8,8,4,2] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(14)*codeTrapDeletionSign b 0 + (6)*codeTrapDeletionSign b 1 + (8)*codeTrapDeletionSign b 2 + (-10)*codeTrapDeletionSign b 3 + (8)*codeTrapDeletionSign b 4 + (-8)*codeTrapDeletionSign b 5 + (8)*codeTrapDeletionSign b 6 + (4)*codeTrapDeletionSign b 7 + (2)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_9_10 (b : Nat) :
    (codeTrapDeletionBasis 9).mulVec (fun j => codeTrapDeletionSign b j.val) 10=
      codeTrapDeletionRow 9 b 10 := by
  change (∑ j : Fin 9,(![16,0,8,-8,8,-8,4,4,4] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(16)*codeTrapDeletionSign b 0 + (8)*codeTrapDeletionSign b 2 + (-8)*codeTrapDeletionSign b 3 + (8)*codeTrapDeletionSign b 4 + (-8)*codeTrapDeletionSign b 5 + (4)*codeTrapDeletionSign b 6 + (4)*codeTrapDeletionSign b 7 + (4)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_9_11 (b : Nat) :
    (codeTrapDeletionBasis 9).mulVec (fun j => codeTrapDeletionSign b j.val) 11=
      codeTrapDeletionRow 9 b 11 := by
  change (∑ j : Fin 9,(![4,0,0,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(4)*codeTrapDeletionSign b 0
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_9_12 (b : Nat) :
    (codeTrapDeletionBasis 9).mulVec (fun j => codeTrapDeletionSign b j.val) 12=
      codeTrapDeletionRow 9 b 12 := by
  change (∑ j : Fin 9,(![0,4,0,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(4)*codeTrapDeletionSign b 1
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_9_13 (b : Nat) :
    (codeTrapDeletionBasis 9).mulVec (fun j => codeTrapDeletionSign b j.val) 13=
      codeTrapDeletionRow 9 b 13 := by
  change (∑ j : Fin 9,(![0,0,4,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(4)*codeTrapDeletionSign b 2
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_9_14 (b : Nat) :
    (codeTrapDeletionBasis 9).mulVec (fun j => codeTrapDeletionSign b j.val) 14=
      codeTrapDeletionRow 9 b 14 := by
  change (∑ j : Fin 9,(![0,0,0,4,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(4)*codeTrapDeletionSign b 3
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_9_15 (b : Nat) :
    (codeTrapDeletionBasis 9).mulVec (fun j => codeTrapDeletionSign b j.val) 15=
      codeTrapDeletionRow 9 b 15 := by
  change (∑ j : Fin 9,(![0,0,0,0,4,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(4)*codeTrapDeletionSign b 4
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_9_16 (b : Nat) :
    (codeTrapDeletionBasis 9).mulVec (fun j => codeTrapDeletionSign b j.val) 16=
      codeTrapDeletionRow 9 b 16 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,4,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(4)*codeTrapDeletionSign b 5
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_9_17 (b : Nat) :
    (codeTrapDeletionBasis 9).mulVec (fun j => codeTrapDeletionSign b j.val) 17=
      codeTrapDeletionRow 9 b 17 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,4,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(4)*codeTrapDeletionSign b 6
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_9_18 (b : Nat) :
    (codeTrapDeletionBasis 9).mulVec (fun j => codeTrapDeletionSign b j.val) 18=
      codeTrapDeletionRow 9 b 18 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,0,4,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(4)*codeTrapDeletionSign b 7
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_9_19 (b : Nat) :
    (codeTrapDeletionBasis 9).mulVec (fun j => codeTrapDeletionSign b j.val) 19=
      codeTrapDeletionRow 9 b 19 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,0,0,4] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(4)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

end CompletionTheory
