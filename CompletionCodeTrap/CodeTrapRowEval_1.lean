/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapDeletionData
@[expose] public section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace CompletionTheory
theorem codeTrapRowEval_1_0 (b : Nat) :
    (codeTrapDeletionBasis 1).mulVec (fun j => codeTrapDeletionSign b j.val) 0=
      codeTrapDeletionRow 1 b 0 := by
  change (∑ j : Fin 9,(![-18,10,4,-14,-12,12,20,-16,-6] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-18)*codeTrapDeletionSign b 0 + (10)*codeTrapDeletionSign b 1 + (4)*codeTrapDeletionSign b 2 + (-14)*codeTrapDeletionSign b 3 + (-12)*codeTrapDeletionSign b 4 + (12)*codeTrapDeletionSign b 5 + (20)*codeTrapDeletionSign b 6 + (-16)*codeTrapDeletionSign b 7 + (-6)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_1_1 (b : Nat) :
    (codeTrapDeletionBasis 1).mulVec (fun j => codeTrapDeletionSign b j.val) 1=
      codeTrapDeletionRow 1 b 1 := by
  change (∑ j : Fin 9,(![-11,-9,-2,-5,-2,2,-2,0,7] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-11)*codeTrapDeletionSign b 0 + (-9)*codeTrapDeletionSign b 1 + (-2)*codeTrapDeletionSign b 2 + (-5)*codeTrapDeletionSign b 3 + (-2)*codeTrapDeletionSign b 4 + (2)*codeTrapDeletionSign b 5 + (-2)*codeTrapDeletionSign b 6 + (7)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_1_2 (b : Nat) :
    (codeTrapDeletionBasis 1).mulVec (fun j => codeTrapDeletionSign b j.val) 2=
      codeTrapDeletionRow 1 b 2 := by
  change (∑ j : Fin 9,(![-14,6,-4,-18,-20,-12,12,-16,-10] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-14)*codeTrapDeletionSign b 0 + (6)*codeTrapDeletionSign b 1 + (-4)*codeTrapDeletionSign b 2 + (-18)*codeTrapDeletionSign b 3 + (-20)*codeTrapDeletionSign b 4 + (-12)*codeTrapDeletionSign b 5 + (12)*codeTrapDeletionSign b 6 + (-16)*codeTrapDeletionSign b 7 + (-10)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_1_3 (b : Nat) :
    (codeTrapDeletionBasis 1).mulVec (fun j => codeTrapDeletionSign b j.val) 3=
      codeTrapDeletionRow 1 b 3 := by
  change (∑ j : Fin 9,(![-3,-1,-18,3,-2,-14,-2,0,-1] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-3)*codeTrapDeletionSign b 0 + (-1)*codeTrapDeletionSign b 1 + (-18)*codeTrapDeletionSign b 2 + (3)*codeTrapDeletionSign b 3 + (-2)*codeTrapDeletionSign b 4 + (-14)*codeTrapDeletionSign b 5 + (-2)*codeTrapDeletionSign b 6 + (-1)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_1_4 (b : Nat) :
    (codeTrapDeletionBasis 1).mulVec (fun j => codeTrapDeletionSign b j.val) 4=
      codeTrapDeletionRow 1 b 4 := by
  change (∑ j : Fin 9,(![-4,4,8,-28,-8,-8,8,-16,-12] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-4)*codeTrapDeletionSign b 0 + (4)*codeTrapDeletionSign b 1 + (8)*codeTrapDeletionSign b 2 + (-28)*codeTrapDeletionSign b 3 + (-8)*codeTrapDeletionSign b 4 + (-8)*codeTrapDeletionSign b 5 + (8)*codeTrapDeletionSign b 6 + (-16)*codeTrapDeletionSign b 7 + (-12)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_1_5 (b : Nat) :
    (codeTrapDeletionBasis 1).mulVec (fun j => codeTrapDeletionSign b j.val) 5=
      codeTrapDeletionRow 1 b 5 := by
  change (∑ j : Fin 9,(![7,-3,-6,25,10,6,-22,16,13] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(7)*codeTrapDeletionSign b 0 + (-3)*codeTrapDeletionSign b 1 + (-6)*codeTrapDeletionSign b 2 + (25)*codeTrapDeletionSign b 3 + (10)*codeTrapDeletionSign b 4 + (6)*codeTrapDeletionSign b 5 + (-22)*codeTrapDeletionSign b 6 + (16)*codeTrapDeletionSign b 7 + (13)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_1_6 (b : Nat) :
    (codeTrapDeletionBasis 1).mulVec (fun j => codeTrapDeletionSign b j.val) 6=
      codeTrapDeletionRow 1 b 6 := by
  change (∑ j : Fin 9,(![-6,-2,12,-10,-4,4,-4,-16,-2] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-6)*codeTrapDeletionSign b 0 + (-2)*codeTrapDeletionSign b 1 + (12)*codeTrapDeletionSign b 2 + (-10)*codeTrapDeletionSign b 3 + (-4)*codeTrapDeletionSign b 4 + (4)*codeTrapDeletionSign b 5 + (-4)*codeTrapDeletionSign b 6 + (-16)*codeTrapDeletionSign b 7 + (-2)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_1_7 (b : Nat) :
    (codeTrapDeletionBasis 1).mulVec (fun j => codeTrapDeletionSign b j.val) 7=
      codeTrapDeletionRow 1 b 7 := by
  change (∑ j : Fin 9,(![13,-17,-2,19,14,2,-18,16,-1] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(13)*codeTrapDeletionSign b 0 + (-17)*codeTrapDeletionSign b 1 + (-2)*codeTrapDeletionSign b 2 + (19)*codeTrapDeletionSign b 3 + (14)*codeTrapDeletionSign b 4 + (2)*codeTrapDeletionSign b 5 + (-18)*codeTrapDeletionSign b 6 + (16)*codeTrapDeletionSign b 7 + (-1)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_1_8 (b : Nat) :
    (codeTrapDeletionBasis 1).mulVec (fun j => codeTrapDeletionSign b j.val) 8=
      codeTrapDeletionRow 1 b 8 := by
  change (∑ j : Fin 9,(![-4,4,-8,-12,8,-8,8,-16,4] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-4)*codeTrapDeletionSign b 0 + (4)*codeTrapDeletionSign b 1 + (-8)*codeTrapDeletionSign b 2 + (-12)*codeTrapDeletionSign b 3 + (8)*codeTrapDeletionSign b 4 + (-8)*codeTrapDeletionSign b 5 + (8)*codeTrapDeletionSign b 6 + (-16)*codeTrapDeletionSign b 7 + (4)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_1_9 (b : Nat) :
    (codeTrapDeletionBasis 1).mulVec (fun j => codeTrapDeletionSign b j.val) 9=
      codeTrapDeletionRow 1 b 9 := by
  change (∑ j : Fin 9,(![2,6,-4,14,-4,4,-4,16,-10] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(2)*codeTrapDeletionSign b 0 + (6)*codeTrapDeletionSign b 1 + (-4)*codeTrapDeletionSign b 2 + (14)*codeTrapDeletionSign b 3 + (-4)*codeTrapDeletionSign b 4 + (4)*codeTrapDeletionSign b 5 + (-4)*codeTrapDeletionSign b 6 + (16)*codeTrapDeletionSign b 7 + (-10)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_1_10 (b : Nat) :
    (codeTrapDeletionBasis 1).mulVec (fun j => codeTrapDeletionSign b j.val) 10=
      codeTrapDeletionRow 1 b 10 := by
  change (∑ j : Fin 9,(![22,-14,4,10,4,-4,-12,16,2] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(22)*codeTrapDeletionSign b 0 + (-14)*codeTrapDeletionSign b 1 + (4)*codeTrapDeletionSign b 2 + (10)*codeTrapDeletionSign b 3 + (4)*codeTrapDeletionSign b 4 + (-4)*codeTrapDeletionSign b 5 + (-12)*codeTrapDeletionSign b 6 + (16)*codeTrapDeletionSign b 7 + (2)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_1_11 (b : Nat) :
    (codeTrapDeletionBasis 1).mulVec (fun j => codeTrapDeletionSign b j.val) 11=
      codeTrapDeletionRow 1 b 11 := by
  change (∑ j : Fin 9,(![16,0,0,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(16)*codeTrapDeletionSign b 0
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_1_12 (b : Nat) :
    (codeTrapDeletionBasis 1).mulVec (fun j => codeTrapDeletionSign b j.val) 12=
      codeTrapDeletionRow 1 b 12 := by
  change (∑ j : Fin 9,(![0,16,0,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(16)*codeTrapDeletionSign b 1
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_1_13 (b : Nat) :
    (codeTrapDeletionBasis 1).mulVec (fun j => codeTrapDeletionSign b j.val) 13=
      codeTrapDeletionRow 1 b 13 := by
  change (∑ j : Fin 9,(![0,0,16,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(16)*codeTrapDeletionSign b 2
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_1_14 (b : Nat) :
    (codeTrapDeletionBasis 1).mulVec (fun j => codeTrapDeletionSign b j.val) 14=
      codeTrapDeletionRow 1 b 14 := by
  change (∑ j : Fin 9,(![0,0,0,16,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(16)*codeTrapDeletionSign b 3
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_1_15 (b : Nat) :
    (codeTrapDeletionBasis 1).mulVec (fun j => codeTrapDeletionSign b j.val) 15=
      codeTrapDeletionRow 1 b 15 := by
  change (∑ j : Fin 9,(![0,0,0,0,16,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(16)*codeTrapDeletionSign b 4
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_1_16 (b : Nat) :
    (codeTrapDeletionBasis 1).mulVec (fun j => codeTrapDeletionSign b j.val) 16=
      codeTrapDeletionRow 1 b 16 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,16,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(16)*codeTrapDeletionSign b 5
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_1_17 (b : Nat) :
    (codeTrapDeletionBasis 1).mulVec (fun j => codeTrapDeletionSign b j.val) 17=
      codeTrapDeletionRow 1 b 17 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,16,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(16)*codeTrapDeletionSign b 6
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_1_18 (b : Nat) :
    (codeTrapDeletionBasis 1).mulVec (fun j => codeTrapDeletionSign b j.val) 18=
      codeTrapDeletionRow 1 b 18 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,0,16,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(16)*codeTrapDeletionSign b 7
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_1_19 (b : Nat) :
    (codeTrapDeletionBasis 1).mulVec (fun j => codeTrapDeletionSign b j.val) 19=
      codeTrapDeletionRow 1 b 19 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,0,0,16] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(16)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

end CompletionTheory
