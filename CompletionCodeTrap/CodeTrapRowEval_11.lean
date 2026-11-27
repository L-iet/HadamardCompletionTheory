/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapDeletionData
@[expose] public section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace CompletionTheory
theorem codeTrapRowEval_11_0 (b : Nat) :
    (codeTrapDeletionBasis 11).mulVec (fun j => codeTrapDeletionSign b j.val) 0=
      codeTrapDeletionRow 11 b 0 := by
  change (∑ j : Fin 9,(![6,8,10,-18,4,-4,16,-6,2] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 0 + (8)*codeTrapDeletionSign b 1 + (10)*codeTrapDeletionSign b 2 + (-18)*codeTrapDeletionSign b 3 + (4)*codeTrapDeletionSign b 4 + (-4)*codeTrapDeletionSign b 5 + (16)*codeTrapDeletionSign b 6 + (-6)*codeTrapDeletionSign b 7 + (2)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_11_1 (b : Nat) :
    (codeTrapDeletionBasis 11).mulVec (fun j => codeTrapDeletionSign b j.val) 1=
      codeTrapDeletionRow 11 b 1 := by
  change (∑ j : Fin 9,(![-9,-5,-4,3,-4,4,-4,0,1] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-9)*codeTrapDeletionSign b 0 + (-5)*codeTrapDeletionSign b 1 + (-4)*codeTrapDeletionSign b 2 + (3)*codeTrapDeletionSign b 3 + (-4)*codeTrapDeletionSign b 4 + (4)*codeTrapDeletionSign b 5 + (-4)*codeTrapDeletionSign b 6 + (1)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_11_2 (b : Nat) :
    (codeTrapDeletionBasis 11).mulVec (fun j => codeTrapDeletionSign b j.val) 2=
      codeTrapDeletionRow 11 b 2 := by
  change (∑ j : Fin 9,(![-6,2,-2,-6,-8,-4,4,-6,-4] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-6)*codeTrapDeletionSign b 0 + (2)*codeTrapDeletionSign b 1 + (-2)*codeTrapDeletionSign b 2 + (-6)*codeTrapDeletionSign b 3 + (-8)*codeTrapDeletionSign b 4 + (-4)*codeTrapDeletionSign b 5 + (4)*codeTrapDeletionSign b 6 + (-6)*codeTrapDeletionSign b 7 + (-4)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_11_3 (b : Nat) :
    (codeTrapDeletionBasis 11).mulVec (fun j => codeTrapDeletionSign b j.val) 3=
      codeTrapDeletionRow 11 b 3 := by
  change (∑ j : Fin 9,(![3,1,-4,-3,2,-8,2,0,1] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(3)*codeTrapDeletionSign b 0 + (1)*codeTrapDeletionSign b 1 + (-4)*codeTrapDeletionSign b 2 + (-3)*codeTrapDeletionSign b 3 + (2)*codeTrapDeletionSign b 4 + (-8)*codeTrapDeletionSign b 5 + (2)*codeTrapDeletionSign b 6 + (1)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_11_4 (b : Nat) :
    (codeTrapDeletionBasis 11).mulVec (fun j => codeTrapDeletionSign b j.val) 4=
      codeTrapDeletionRow 11 b 4 := by
  change (∑ j : Fin 9,(![-6,0,0,-6,-6,0,0,-6,-6] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-6)*codeTrapDeletionSign b 0 + (-6)*codeTrapDeletionSign b 3 + (-6)*codeTrapDeletionSign b 4 + (-6)*codeTrapDeletionSign b 7 + (-6)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_11_5 (b : Nat) :
    (codeTrapDeletionBasis 11).mulVec (fun j => codeTrapDeletionSign b j.val) 5=
      codeTrapDeletionRow 11 b 5 := by
  change (∑ j : Fin 9,(![-3,-3,-6,15,0,6,-12,6,3] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-3)*codeTrapDeletionSign b 0 + (-3)*codeTrapDeletionSign b 1 + (-6)*codeTrapDeletionSign b 2 + (15)*codeTrapDeletionSign b 3 + (6)*codeTrapDeletionSign b 5 + (-12)*codeTrapDeletionSign b 6 + (6)*codeTrapDeletionSign b 7 + (3)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_11_6 (b : Nat) :
    (codeTrapDeletionBasis 11).mulVec (fun j => codeTrapDeletionSign b j.val) 6=
      codeTrapDeletionRow 11 b 6 := by
  change (∑ j : Fin 9,(![0,0,6,-6,0,0,0,-6,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 2 + (-6)*codeTrapDeletionSign b 3 + (-6)*codeTrapDeletionSign b 7
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_11_7 (b : Nat) :
    (codeTrapDeletionBasis 11).mulVec (fun j => codeTrapDeletionSign b j.val) 7=
      codeTrapDeletionRow 11 b 7 := by
  change (∑ j : Fin 9,(![3,-7,-2,9,4,2,-8,6,-1] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(3)*codeTrapDeletionSign b 0 + (-7)*codeTrapDeletionSign b 1 + (-2)*codeTrapDeletionSign b 2 + (9)*codeTrapDeletionSign b 3 + (4)*codeTrapDeletionSign b 4 + (2)*codeTrapDeletionSign b 5 + (-8)*codeTrapDeletionSign b 6 + (6)*codeTrapDeletionSign b 7 + (-1)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_11_8 (b : Nat) :
    (codeTrapDeletionBasis 11).mulVec (fun j => codeTrapDeletionSign b j.val) 8=
      codeTrapDeletionRow 11 b 8 := by
  change (∑ j : Fin 9,(![6,4,2,-12,8,-8,8,-6,4] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 0 + (4)*codeTrapDeletionSign b 1 + (2)*codeTrapDeletionSign b 2 + (-12)*codeTrapDeletionSign b 3 + (8)*codeTrapDeletionSign b 4 + (-8)*codeTrapDeletionSign b 5 + (8)*codeTrapDeletionSign b 6 + (-6)*codeTrapDeletionSign b 7 + (4)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_11_9 (b : Nat) :
    (codeTrapDeletionBasis 11).mulVec (fun j => codeTrapDeletionSign b j.val) 9=
      codeTrapDeletionRow 11 b 9 := by
  change (∑ j : Fin 9,(![6,4,2,0,2,-2,2,6,-2] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 0 + (4)*codeTrapDeletionSign b 1 + (2)*codeTrapDeletionSign b 2 + (2)*codeTrapDeletionSign b 4 + (-2)*codeTrapDeletionSign b 5 + (2)*codeTrapDeletionSign b 6 + (6)*codeTrapDeletionSign b 7 + (-2)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_11_10 (b : Nat) :
    (codeTrapDeletionBasis 11).mulVec (fun j => codeTrapDeletionSign b j.val) 10=
      codeTrapDeletionRow 11 b 10 := by
  change (∑ j : Fin 9,(![-6,-10,-8,18,-8,8,-14,6,-4] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-6)*codeTrapDeletionSign b 0 + (-10)*codeTrapDeletionSign b 1 + (-8)*codeTrapDeletionSign b 2 + (18)*codeTrapDeletionSign b 3 + (-8)*codeTrapDeletionSign b 4 + (8)*codeTrapDeletionSign b 5 + (-14)*codeTrapDeletionSign b 6 + (6)*codeTrapDeletionSign b 7 + (-4)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_11_11 (b : Nat) :
    (codeTrapDeletionBasis 11).mulVec (fun j => codeTrapDeletionSign b j.val) 11=
      codeTrapDeletionRow 11 b 11 := by
  change (∑ j : Fin 9,(![6,0,0,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 0
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_11_12 (b : Nat) :
    (codeTrapDeletionBasis 11).mulVec (fun j => codeTrapDeletionSign b j.val) 12=
      codeTrapDeletionRow 11 b 12 := by
  change (∑ j : Fin 9,(![0,6,0,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 1
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_11_13 (b : Nat) :
    (codeTrapDeletionBasis 11).mulVec (fun j => codeTrapDeletionSign b j.val) 13=
      codeTrapDeletionRow 11 b 13 := by
  change (∑ j : Fin 9,(![0,0,6,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 2
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_11_14 (b : Nat) :
    (codeTrapDeletionBasis 11).mulVec (fun j => codeTrapDeletionSign b j.val) 14=
      codeTrapDeletionRow 11 b 14 := by
  change (∑ j : Fin 9,(![0,0,0,6,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 3
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_11_15 (b : Nat) :
    (codeTrapDeletionBasis 11).mulVec (fun j => codeTrapDeletionSign b j.val) 15=
      codeTrapDeletionRow 11 b 15 := by
  change (∑ j : Fin 9,(![0,0,0,0,6,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 4
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_11_16 (b : Nat) :
    (codeTrapDeletionBasis 11).mulVec (fun j => codeTrapDeletionSign b j.val) 16=
      codeTrapDeletionRow 11 b 16 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,6,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 5
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_11_17 (b : Nat) :
    (codeTrapDeletionBasis 11).mulVec (fun j => codeTrapDeletionSign b j.val) 17=
      codeTrapDeletionRow 11 b 17 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,6,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 6
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_11_18 (b : Nat) :
    (codeTrapDeletionBasis 11).mulVec (fun j => codeTrapDeletionSign b j.val) 18=
      codeTrapDeletionRow 11 b 18 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,0,6,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 7
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_11_19 (b : Nat) :
    (codeTrapDeletionBasis 11).mulVec (fun j => codeTrapDeletionSign b j.val) 19=
      codeTrapDeletionRow 11 b 19 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,0,0,6] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(6)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

end CompletionTheory
