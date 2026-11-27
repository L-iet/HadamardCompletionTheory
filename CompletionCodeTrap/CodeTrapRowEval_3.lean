/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapDeletionData
@[expose] public section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace CompletionTheory
theorem codeTrapRowEval_3_0 (b : Nat) :
    (codeTrapDeletionBasis 3).mulVec (fun j => codeTrapDeletionSign b j.val) 0=
      codeTrapDeletionRow 3 b 0 := by
  change (∑ j : Fin 9,(![-18,4,-2,-2,-12,12,8,-10,-6] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-18)*codeTrapDeletionSign b 0 + (4)*codeTrapDeletionSign b 1 + (-2)*codeTrapDeletionSign b 2 + (-2)*codeTrapDeletionSign b 3 + (-12)*codeTrapDeletionSign b 4 + (12)*codeTrapDeletionSign b 5 + (8)*codeTrapDeletionSign b 6 + (-10)*codeTrapDeletionSign b 7 + (-6)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_3_1 (b : Nat) :
    (codeTrapDeletionBasis 3).mulVec (fun j => codeTrapDeletionSign b j.val) 1=
      codeTrapDeletionRow 3 b 1 := by
  change (∑ j : Fin 9,(![1,-3,4,-11,4,-4,4,0,7] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(1)*codeTrapDeletionSign b 0 + (-3)*codeTrapDeletionSign b 1 + (4)*codeTrapDeletionSign b 2 + (-11)*codeTrapDeletionSign b 3 + (4)*codeTrapDeletionSign b 4 + (-4)*codeTrapDeletionSign b 5 + (4)*codeTrapDeletionSign b 6 + (7)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_3_2 (b : Nat) :
    (codeTrapDeletionBasis 3).mulVec (fun j => codeTrapDeletionSign b j.val) 2=
      codeTrapDeletionRow 3 b 2 := by
  change (∑ j : Fin 9,(![-26,-2,-14,6,-24,4,-4,-10,-12] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-26)*codeTrapDeletionSign b 0 + (-2)*codeTrapDeletionSign b 1 + (-14)*codeTrapDeletionSign b 2 + (6)*codeTrapDeletionSign b 3 + (-24)*codeTrapDeletionSign b 4 + (4)*codeTrapDeletionSign b 5 + (-4)*codeTrapDeletionSign b 6 + (-10)*codeTrapDeletionSign b 7 + (-12)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_3_3 (b : Nat) :
    (codeTrapDeletionBasis 3).mulVec (fun j => codeTrapDeletionSign b j.val) 3=
      codeTrapDeletionRow 3 b 3 := by
  change (∑ j : Fin 9,(![3,1,-8,-3,2,-12,2,0,1] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(3)*codeTrapDeletionSign b 0 + (1)*codeTrapDeletionSign b 1 + (-8)*codeTrapDeletionSign b 2 + (-3)*codeTrapDeletionSign b 3 + (2)*codeTrapDeletionSign b 4 + (-12)*codeTrapDeletionSign b 5 + (2)*codeTrapDeletionSign b 6 + (1)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_3_4 (b : Nat) :
    (codeTrapDeletionBasis 3).mulVec (fun j => codeTrapDeletionSign b j.val) 4=
      codeTrapDeletionRow 3 b 4 := by
  change (∑ j : Fin 9,(![-16,-2,-4,-4,-14,4,-4,-10,-12] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-16)*codeTrapDeletionSign b 0 + (-2)*codeTrapDeletionSign b 1 + (-4)*codeTrapDeletionSign b 2 + (-4)*codeTrapDeletionSign b 3 + (-14)*codeTrapDeletionSign b 4 + (4)*codeTrapDeletionSign b 5 + (-4)*codeTrapDeletionSign b 6 + (-10)*codeTrapDeletionSign b 7 + (-12)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_3_5 (b : Nat) :
    (codeTrapDeletionBasis 3).mulVec (fun j => codeTrapDeletionSign b j.val) 5=
      codeTrapDeletionRow 3 b 5 := by
  change (∑ j : Fin 9,(![25,5,10,-5,20,-10,0,10,15] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(25)*codeTrapDeletionSign b 0 + (5)*codeTrapDeletionSign b 1 + (10)*codeTrapDeletionSign b 2 + (-5)*codeTrapDeletionSign b 3 + (20)*codeTrapDeletionSign b 4 + (-10)*codeTrapDeletionSign b 5 + (10)*codeTrapDeletionSign b 7 + (15)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_3_6 (b : Nat) :
    (codeTrapDeletionBasis 3).mulVec (fun j => codeTrapDeletionSign b j.val) 6=
      codeTrapDeletionRow 3 b 6 := by
  change (∑ j : Fin 9,(![-12,-4,2,2,-8,8,-8,-10,-4] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-12)*codeTrapDeletionSign b 0 + (-4)*codeTrapDeletionSign b 1 + (2)*codeTrapDeletionSign b 2 + (2)*codeTrapDeletionSign b 3 + (-8)*codeTrapDeletionSign b 4 + (8)*codeTrapDeletionSign b 5 + (-8)*codeTrapDeletionSign b 6 + (-10)*codeTrapDeletionSign b 7 + (-4)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_3_7 (b : Nat) :
    (codeTrapDeletionBasis 3).mulVec (fun j => codeTrapDeletionSign b j.val) 7=
      codeTrapDeletionRow 3 b 7 := by
  change (∑ j : Fin 9,(![25,-5,10,-5,20,-10,0,10,5] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(25)*codeTrapDeletionSign b 0 + (-5)*codeTrapDeletionSign b 1 + (10)*codeTrapDeletionSign b 2 + (-5)*codeTrapDeletionSign b 3 + (20)*codeTrapDeletionSign b 4 + (-10)*codeTrapDeletionSign b 5 + (10)*codeTrapDeletionSign b 7 + (5)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_3_8 (b : Nat) :
    (codeTrapDeletionBasis 3).mulVec (fun j => codeTrapDeletionSign b j.val) 8=
      codeTrapDeletionRow 3 b 8 := by
  change (∑ j : Fin 9,(![-10,0,-10,0,0,0,0,-10,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-10)*codeTrapDeletionSign b 0 + (-10)*codeTrapDeletionSign b 2 + (-10)*codeTrapDeletionSign b 7
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_3_9 (b : Nat) :
    (codeTrapDeletionBasis 3).mulVec (fun j => codeTrapDeletionSign b j.val) 9=
      codeTrapDeletionRow 3 b 9 := by
  change (∑ j : Fin 9,(![2,4,-2,8,-2,2,-2,10,-6] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(2)*codeTrapDeletionSign b 0 + (4)*codeTrapDeletionSign b 1 + (-2)*codeTrapDeletionSign b 2 + (8)*codeTrapDeletionSign b 3 + (-2)*codeTrapDeletionSign b 4 + (2)*codeTrapDeletionSign b 5 + (-2)*codeTrapDeletionSign b 6 + (10)*codeTrapDeletionSign b 7 + (-6)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_3_10 (b : Nat) :
    (codeTrapDeletionBasis 3).mulVec (fun j => codeTrapDeletionSign b j.val) 10=
      codeTrapDeletionRow 3 b 10 := by
  change (∑ j : Fin 9,(![16,-8,4,4,4,-4,-6,10,2] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(16)*codeTrapDeletionSign b 0 + (-8)*codeTrapDeletionSign b 1 + (4)*codeTrapDeletionSign b 2 + (4)*codeTrapDeletionSign b 3 + (4)*codeTrapDeletionSign b 4 + (-4)*codeTrapDeletionSign b 5 + (-6)*codeTrapDeletionSign b 6 + (10)*codeTrapDeletionSign b 7 + (2)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_3_11 (b : Nat) :
    (codeTrapDeletionBasis 3).mulVec (fun j => codeTrapDeletionSign b j.val) 11=
      codeTrapDeletionRow 3 b 11 := by
  change (∑ j : Fin 9,(![10,0,0,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(10)*codeTrapDeletionSign b 0
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_3_12 (b : Nat) :
    (codeTrapDeletionBasis 3).mulVec (fun j => codeTrapDeletionSign b j.val) 12=
      codeTrapDeletionRow 3 b 12 := by
  change (∑ j : Fin 9,(![0,10,0,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(10)*codeTrapDeletionSign b 1
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_3_13 (b : Nat) :
    (codeTrapDeletionBasis 3).mulVec (fun j => codeTrapDeletionSign b j.val) 13=
      codeTrapDeletionRow 3 b 13 := by
  change (∑ j : Fin 9,(![0,0,10,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(10)*codeTrapDeletionSign b 2
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_3_14 (b : Nat) :
    (codeTrapDeletionBasis 3).mulVec (fun j => codeTrapDeletionSign b j.val) 14=
      codeTrapDeletionRow 3 b 14 := by
  change (∑ j : Fin 9,(![0,0,0,10,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(10)*codeTrapDeletionSign b 3
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_3_15 (b : Nat) :
    (codeTrapDeletionBasis 3).mulVec (fun j => codeTrapDeletionSign b j.val) 15=
      codeTrapDeletionRow 3 b 15 := by
  change (∑ j : Fin 9,(![0,0,0,0,10,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(10)*codeTrapDeletionSign b 4
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_3_16 (b : Nat) :
    (codeTrapDeletionBasis 3).mulVec (fun j => codeTrapDeletionSign b j.val) 16=
      codeTrapDeletionRow 3 b 16 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,10,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(10)*codeTrapDeletionSign b 5
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_3_17 (b : Nat) :
    (codeTrapDeletionBasis 3).mulVec (fun j => codeTrapDeletionSign b j.val) 17=
      codeTrapDeletionRow 3 b 17 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,10,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(10)*codeTrapDeletionSign b 6
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_3_18 (b : Nat) :
    (codeTrapDeletionBasis 3).mulVec (fun j => codeTrapDeletionSign b j.val) 18=
      codeTrapDeletionRow 3 b 18 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,0,10,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(10)*codeTrapDeletionSign b 7
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_3_19 (b : Nat) :
    (codeTrapDeletionBasis 3).mulVec (fun j => codeTrapDeletionSign b j.val) 19=
      codeTrapDeletionRow 3 b 19 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,0,0,10] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(10)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

end CompletionTheory
