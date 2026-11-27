/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapDeletionData
@[expose] public section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace CompletionTheory
theorem codeTrapRowEval_7_0 (b : Nat) :
    (codeTrapDeletionBasis 7).mulVec (fun j => codeTrapDeletionSign b j.val) 0=
      codeTrapDeletionRow 7 b 0 := by
  change (∑ j : Fin 9,(![-24,-14,2,12,-16,16,-4,6,-8] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-24)*codeTrapDeletionSign b 0 + (-14)*codeTrapDeletionSign b 1 + (2)*codeTrapDeletionSign b 2 + (12)*codeTrapDeletionSign b 3 + (-16)*codeTrapDeletionSign b 4 + (16)*codeTrapDeletionSign b 5 + (-4)*codeTrapDeletionSign b 6 + (6)*codeTrapDeletionSign b 7 + (-8)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_7_1 (b : Nat) :
    (codeTrapDeletionBasis 7).mulVec (fun j => codeTrapDeletionSign b j.val) 1=
      codeTrapDeletionRow 7 b 1 := by
  change (∑ j : Fin 9,(![3,-2,8,-24,8,-8,11,-3,13] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(3)*codeTrapDeletionSign b 0 + (-2)*codeTrapDeletionSign b 1 + (8)*codeTrapDeletionSign b 2 + (-24)*codeTrapDeletionSign b 3 + (8)*codeTrapDeletionSign b 4 + (-8)*codeTrapDeletionSign b 5 + (11)*codeTrapDeletionSign b 6 + (-3)*codeTrapDeletionSign b 7 + (13)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_7_2 (b : Nat) :
    (codeTrapDeletionBasis 7).mulVec (fun j => codeTrapDeletionSign b j.val) 2=
      codeTrapDeletionRow 7 b 2 := by
  change (∑ j : Fin 9,(![-18,-12,-6,0,-24,-12,-6,0,-12] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-18)*codeTrapDeletionSign b 0 + (-12)*codeTrapDeletionSign b 1 + (-6)*codeTrapDeletionSign b 2 + (-24)*codeTrapDeletionSign b 4 + (-12)*codeTrapDeletionSign b 5 + (-6)*codeTrapDeletionSign b 6 + (-12)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_7_3 (b : Nat) :
    (codeTrapDeletionBasis 7).mulVec (fun j => codeTrapDeletionSign b j.val) 3=
      codeTrapDeletionRow 7 b 3 := by
  change (∑ j : Fin 9,(![9,12,-12,-18,6,-24,15,-9,3] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(9)*codeTrapDeletionSign b 0 + (12)*codeTrapDeletionSign b 1 + (-12)*codeTrapDeletionSign b 2 + (-18)*codeTrapDeletionSign b 3 + (6)*codeTrapDeletionSign b 4 + (-24)*codeTrapDeletionSign b 5 + (15)*codeTrapDeletionSign b 6 + (-9)*codeTrapDeletionSign b 7 + (3)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_7_4 (b : Nat) :
    (codeTrapDeletionBasis 7).mulVec (fun j => codeTrapDeletionSign b j.val) 4=
      codeTrapDeletionRow 7 b 4 := by
  change (∑ j : Fin 9,(![-18,-18,0,0,-18,0,-18,0,-18] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-18)*codeTrapDeletionSign b 0 + (-18)*codeTrapDeletionSign b 1 + (-18)*codeTrapDeletionSign b 4 + (-18)*codeTrapDeletionSign b 6 + (-18)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_7_5 (b : Nat) :
    (codeTrapDeletionBasis 7).mulVec (fun j => codeTrapDeletionSign b j.val) 5=
      codeTrapDeletionRow 7 b 5 := by
  change (∑ j : Fin 9,(![15,14,-2,6,16,2,-5,3,17] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(15)*codeTrapDeletionSign b 0 + (14)*codeTrapDeletionSign b 1 + (-2)*codeTrapDeletionSign b 2 + (6)*codeTrapDeletionSign b 3 + (16)*codeTrapDeletionSign b 4 + (2)*codeTrapDeletionSign b 5 + (-5)*codeTrapDeletionSign b 6 + (3)*codeTrapDeletionSign b 7 + (17)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_7_6 (b : Nat) :
    (codeTrapDeletionBasis 7).mulVec (fun j => codeTrapDeletionSign b j.val) 6=
      codeTrapDeletionRow 7 b 6 := by
  change (∑ j : Fin 9,(![-6,-8,14,-6,-4,4,-10,-12,-2] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-6)*codeTrapDeletionSign b 0 + (-8)*codeTrapDeletionSign b 1 + (14)*codeTrapDeletionSign b 2 + (-6)*codeTrapDeletionSign b 3 + (-4)*codeTrapDeletionSign b 4 + (4)*codeTrapDeletionSign b 5 + (-10)*codeTrapDeletionSign b 6 + (-12)*codeTrapDeletionSign b 7 + (-2)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_7_7 (b : Nat) :
    (codeTrapDeletionBasis 7).mulVec (fun j => codeTrapDeletionSign b j.val) 7=
      codeTrapDeletionRow 7 b 7 := by
  change (∑ j : Fin 9,(![15,-4,-2,6,16,2,-5,3,-1] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(15)*codeTrapDeletionSign b 0 + (-4)*codeTrapDeletionSign b 1 + (-2)*codeTrapDeletionSign b 2 + (6)*codeTrapDeletionSign b 3 + (16)*codeTrapDeletionSign b 4 + (2)*codeTrapDeletionSign b 5 + (-5)*codeTrapDeletionSign b 6 + (3)*codeTrapDeletionSign b 7 + (-1)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_7_8 (b : Nat) :
    (codeTrapDeletionBasis 7).mulVec (fun j => codeTrapDeletionSign b j.val) 8=
      codeTrapDeletionRow 7 b 8 := by
  change (∑ j : Fin 9,(![0,6,-6,-18,12,-12,12,-18,6] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 1 + (-6)*codeTrapDeletionSign b 2 + (-18)*codeTrapDeletionSign b 3 + (12)*codeTrapDeletionSign b 4 + (-12)*codeTrapDeletionSign b 5 + (12)*codeTrapDeletionSign b 6 + (-18)*codeTrapDeletionSign b 7 + (6)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_7_9 (b : Nat) :
    (codeTrapDeletionBasis 7).mulVec (fun j => codeTrapDeletionSign b j.val) 9=
      codeTrapDeletionRow 7 b 9 := by
  change (∑ j : Fin 9,(![6,14,-2,6,-2,2,4,12,-10] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 0 + (14)*codeTrapDeletionSign b 1 + (-2)*codeTrapDeletionSign b 2 + (6)*codeTrapDeletionSign b 3 + (-2)*codeTrapDeletionSign b 4 + (2)*codeTrapDeletionSign b 5 + (4)*codeTrapDeletionSign b 6 + (12)*codeTrapDeletionSign b 7 + (-10)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_7_10 (b : Nat) :
    (codeTrapDeletionBasis 7).mulVec (fun j => codeTrapDeletionSign b j.val) 10=
      codeTrapDeletionRow 7 b 10 := by
  change (∑ j : Fin 9,(![18,0,0,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(18)*codeTrapDeletionSign b 0
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_7_11 (b : Nat) :
    (codeTrapDeletionBasis 7).mulVec (fun j => codeTrapDeletionSign b j.val) 11=
      codeTrapDeletionRow 7 b 11 := by
  change (∑ j : Fin 9,(![0,-6,-12,18,-12,12,-12,0,-6] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-6)*codeTrapDeletionSign b 1 + (-12)*codeTrapDeletionSign b 2 + (18)*codeTrapDeletionSign b 3 + (-12)*codeTrapDeletionSign b 4 + (12)*codeTrapDeletionSign b 5 + (-12)*codeTrapDeletionSign b 6 + (-6)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_7_12 (b : Nat) :
    (codeTrapDeletionBasis 7).mulVec (fun j => codeTrapDeletionSign b j.val) 12=
      codeTrapDeletionRow 7 b 12 := by
  change (∑ j : Fin 9,(![0,18,0,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(18)*codeTrapDeletionSign b 1
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_7_13 (b : Nat) :
    (codeTrapDeletionBasis 7).mulVec (fun j => codeTrapDeletionSign b j.val) 13=
      codeTrapDeletionRow 7 b 13 := by
  change (∑ j : Fin 9,(![0,0,18,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(18)*codeTrapDeletionSign b 2
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_7_14 (b : Nat) :
    (codeTrapDeletionBasis 7).mulVec (fun j => codeTrapDeletionSign b j.val) 14=
      codeTrapDeletionRow 7 b 14 := by
  change (∑ j : Fin 9,(![0,0,0,18,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(18)*codeTrapDeletionSign b 3
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_7_15 (b : Nat) :
    (codeTrapDeletionBasis 7).mulVec (fun j => codeTrapDeletionSign b j.val) 15=
      codeTrapDeletionRow 7 b 15 := by
  change (∑ j : Fin 9,(![0,0,0,0,18,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(18)*codeTrapDeletionSign b 4
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_7_16 (b : Nat) :
    (codeTrapDeletionBasis 7).mulVec (fun j => codeTrapDeletionSign b j.val) 16=
      codeTrapDeletionRow 7 b 16 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,18,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(18)*codeTrapDeletionSign b 5
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_7_17 (b : Nat) :
    (codeTrapDeletionBasis 7).mulVec (fun j => codeTrapDeletionSign b j.val) 17=
      codeTrapDeletionRow 7 b 17 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,18,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(18)*codeTrapDeletionSign b 6
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_7_18 (b : Nat) :
    (codeTrapDeletionBasis 7).mulVec (fun j => codeTrapDeletionSign b j.val) 18=
      codeTrapDeletionRow 7 b 18 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,0,18,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(18)*codeTrapDeletionSign b 7
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_7_19 (b : Nat) :
    (codeTrapDeletionBasis 7).mulVec (fun j => codeTrapDeletionSign b j.val) 19=
      codeTrapDeletionRow 7 b 19 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,0,0,18] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(18)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

end CompletionTheory
