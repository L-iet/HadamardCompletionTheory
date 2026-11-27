/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapDeletionData
@[expose] public section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace CompletionTheory
theorem codeTrapRowEval_0_0 (b : Nat) :
    (codeTrapDeletionBasis 0).mulVec (fun j => codeTrapDeletionSign b j.val) 0=
      codeTrapDeletionRow 0 b 0 := by
  change (∑ j : Fin 9,(![0,6,6,-12,0,0,12,-6,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 1 + (6)*codeTrapDeletionSign b 2 + (-12)*codeTrapDeletionSign b 3 + (12)*codeTrapDeletionSign b 6 + (-6)*codeTrapDeletionSign b 7
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_0_1 (b : Nat) :
    (codeTrapDeletionBasis 0).mulVec (fun j => codeTrapDeletionSign b j.val) 1=
      codeTrapDeletionRow 0 b 1 := by
  change (∑ j : Fin 9,(![3,-1,4,-9,4,-4,4,0,5] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(3)*codeTrapDeletionSign b 0 + (-1)*codeTrapDeletionSign b 1 + (4)*codeTrapDeletionSign b 2 + (-9)*codeTrapDeletionSign b 3 + (4)*codeTrapDeletionSign b 4 + (-4)*codeTrapDeletionSign b 5 + (4)*codeTrapDeletionSign b 6 + (5)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_0_2 (b : Nat) :
    (codeTrapDeletionBasis 0).mulVec (fun j => codeTrapDeletionSign b j.val) 2=
      codeTrapDeletionRow 0 b 2 := by
  change (∑ j : Fin 9,(![12,8,10,-24,4,-16,16,-6,2] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(12)*codeTrapDeletionSign b 0 + (8)*codeTrapDeletionSign b 1 + (10)*codeTrapDeletionSign b 2 + (-24)*codeTrapDeletionSign b 3 + (4)*codeTrapDeletionSign b 4 + (-16)*codeTrapDeletionSign b 5 + (16)*codeTrapDeletionSign b 6 + (-6)*codeTrapDeletionSign b 7 + (2)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_0_3 (b : Nat) :
    (codeTrapDeletionBasis 0).mulVec (fun j => codeTrapDeletionSign b j.val) 3=
      codeTrapDeletionRow 0 b 3 := by
  change (∑ j : Fin 9,(![9,3,0,-9,6,-12,6,0,3] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(9)*codeTrapDeletionSign b 0 + (3)*codeTrapDeletionSign b 1 + (-9)*codeTrapDeletionSign b 3 + (6)*codeTrapDeletionSign b 4 + (-12)*codeTrapDeletionSign b 5 + (6)*codeTrapDeletionSign b 6 + (3)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_0_4 (b : Nat) :
    (codeTrapDeletionBasis 0).mulVec (fun j => codeTrapDeletionSign b j.val) 4=
      codeTrapDeletionRow 0 b 4 := by
  change (∑ j : Fin 9,(![12,6,12,-24,6,-12,12,-6,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(12)*codeTrapDeletionSign b 0 + (6)*codeTrapDeletionSign b 1 + (12)*codeTrapDeletionSign b 2 + (-24)*codeTrapDeletionSign b 3 + (6)*codeTrapDeletionSign b 4 + (-12)*codeTrapDeletionSign b 5 + (12)*codeTrapDeletionSign b 6 + (-6)*codeTrapDeletionSign b 7
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_0_5 (b : Nat) :
    (codeTrapDeletionBasis 0).mulVec (fun j => codeTrapDeletionSign b j.val) 5=
      codeTrapDeletionRow 0 b 5 := by
  change (∑ j : Fin 9,(![-3,-3,-6,15,0,6,-12,6,3] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-3)*codeTrapDeletionSign b 0 + (-3)*codeTrapDeletionSign b 1 + (-6)*codeTrapDeletionSign b 2 + (15)*codeTrapDeletionSign b 3 + (6)*codeTrapDeletionSign b 5 + (-12)*codeTrapDeletionSign b 6 + (6)*codeTrapDeletionSign b 7 + (3)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_0_6 (b : Nat) :
    (codeTrapDeletionBasis 0).mulVec (fun j => codeTrapDeletionSign b j.val) 6=
      codeTrapDeletionRow 0 b 6 := by
  change (∑ j : Fin 9,(![6,2,10,-12,4,-4,4,-6,2] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 0 + (2)*codeTrapDeletionSign b 1 + (10)*codeTrapDeletionSign b 2 + (-12)*codeTrapDeletionSign b 3 + (4)*codeTrapDeletionSign b 4 + (-4)*codeTrapDeletionSign b 5 + (4)*codeTrapDeletionSign b 6 + (-6)*codeTrapDeletionSign b 7 + (2)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_0_7 (b : Nat) :
    (codeTrapDeletionBasis 0).mulVec (fun j => codeTrapDeletionSign b j.val) 7=
      codeTrapDeletionRow 0 b 7 := by
  change (∑ j : Fin 9,(![3,-7,-2,9,4,2,-8,6,-1] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(3)*codeTrapDeletionSign b 0 + (-7)*codeTrapDeletionSign b 1 + (-2)*codeTrapDeletionSign b 2 + (9)*codeTrapDeletionSign b 3 + (4)*codeTrapDeletionSign b 4 + (2)*codeTrapDeletionSign b 5 + (-8)*codeTrapDeletionSign b 6 + (6)*codeTrapDeletionSign b 7 + (-1)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_0_8 (b : Nat) :
    (codeTrapDeletionBasis 0).mulVec (fun j => codeTrapDeletionSign b j.val) 8=
      codeTrapDeletionRow 0 b 8 := by
  change (∑ j : Fin 9,(![6,4,2,-12,8,-8,8,-6,4] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 0 + (4)*codeTrapDeletionSign b 1 + (2)*codeTrapDeletionSign b 2 + (-12)*codeTrapDeletionSign b 3 + (8)*codeTrapDeletionSign b 4 + (-8)*codeTrapDeletionSign b 5 + (8)*codeTrapDeletionSign b 6 + (-6)*codeTrapDeletionSign b 7 + (4)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_0_9 (b : Nat) :
    (codeTrapDeletionBasis 0).mulVec (fun j => codeTrapDeletionSign b j.val) 9=
      codeTrapDeletionRow 0 b 9 := by
  change (∑ j : Fin 9,(![0,2,-2,6,-2,2,-2,6,-4] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(2)*codeTrapDeletionSign b 1 + (-2)*codeTrapDeletionSign b 2 + (6)*codeTrapDeletionSign b 3 + (-2)*codeTrapDeletionSign b 4 + (2)*codeTrapDeletionSign b 5 + (-2)*codeTrapDeletionSign b 6 + (6)*codeTrapDeletionSign b 7 + (-4)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_0_10 (b : Nat) :
    (codeTrapDeletionBasis 0).mulVec (fun j => codeTrapDeletionSign b j.val) 10=
      codeTrapDeletionRow 0 b 10 := by
  change (∑ j : Fin 9,(![6,-6,0,6,0,0,-6,6,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 0 + (-6)*codeTrapDeletionSign b 1 + (6)*codeTrapDeletionSign b 3 + (-6)*codeTrapDeletionSign b 6 + (6)*codeTrapDeletionSign b 7
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_0_11 (b : Nat) :
    (codeTrapDeletionBasis 0).mulVec (fun j => codeTrapDeletionSign b j.val) 11=
      codeTrapDeletionRow 0 b 11 := by
  change (∑ j : Fin 9,(![6,0,0,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 0
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_0_12 (b : Nat) :
    (codeTrapDeletionBasis 0).mulVec (fun j => codeTrapDeletionSign b j.val) 12=
      codeTrapDeletionRow 0 b 12 := by
  change (∑ j : Fin 9,(![0,6,0,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 1
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_0_13 (b : Nat) :
    (codeTrapDeletionBasis 0).mulVec (fun j => codeTrapDeletionSign b j.val) 13=
      codeTrapDeletionRow 0 b 13 := by
  change (∑ j : Fin 9,(![0,0,6,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 2
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_0_14 (b : Nat) :
    (codeTrapDeletionBasis 0).mulVec (fun j => codeTrapDeletionSign b j.val) 14=
      codeTrapDeletionRow 0 b 14 := by
  change (∑ j : Fin 9,(![0,0,0,6,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 3
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_0_15 (b : Nat) :
    (codeTrapDeletionBasis 0).mulVec (fun j => codeTrapDeletionSign b j.val) 15=
      codeTrapDeletionRow 0 b 15 := by
  change (∑ j : Fin 9,(![0,0,0,0,6,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 4
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_0_16 (b : Nat) :
    (codeTrapDeletionBasis 0).mulVec (fun j => codeTrapDeletionSign b j.val) 16=
      codeTrapDeletionRow 0 b 16 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,6,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 5
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_0_17 (b : Nat) :
    (codeTrapDeletionBasis 0).mulVec (fun j => codeTrapDeletionSign b j.val) 17=
      codeTrapDeletionRow 0 b 17 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,6,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 6
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_0_18 (b : Nat) :
    (codeTrapDeletionBasis 0).mulVec (fun j => codeTrapDeletionSign b j.val) 18=
      codeTrapDeletionRow 0 b 18 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,0,6,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 7
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_0_19 (b : Nat) :
    (codeTrapDeletionBasis 0).mulVec (fun j => codeTrapDeletionSign b j.val) 19=
      codeTrapDeletionRow 0 b 19 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,0,0,6] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

end CompletionTheory
