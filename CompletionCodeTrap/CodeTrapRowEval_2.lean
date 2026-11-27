/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapDeletionData
@[expose] public section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace CompletionTheory
theorem codeTrapRowEval_2_0 (b : Nat) :
    (codeTrapDeletionBasis 2).mulVec (fun j => codeTrapDeletionSign b j.val) 0=
      codeTrapDeletionRow 2 b 0 := by
  change (∑ j : Fin 9,(![0,8,8,-16,0,0,16,-8,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(8)*codeTrapDeletionSign b 1 + (8)*codeTrapDeletionSign b 2 + (-16)*codeTrapDeletionSign b 3 + (16)*codeTrapDeletionSign b 6 + (-8)*codeTrapDeletionSign b 7
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_2_1 (b : Nat) :
    (codeTrapDeletionBasis 2).mulVec (fun j => codeTrapDeletionSign b j.val) 1=
      codeTrapDeletionRow 2 b 1 := by
  change (∑ j : Fin 9,(![-1,-3,2,-7,2,-2,2,0,5] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-1)*codeTrapDeletionSign b 0 + (-3)*codeTrapDeletionSign b 1 + (2)*codeTrapDeletionSign b 2 + (-7)*codeTrapDeletionSign b 3 + (2)*codeTrapDeletionSign b 4 + (-2)*codeTrapDeletionSign b 5 + (2)*codeTrapDeletionSign b 6 + (5)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_2_2 (b : Nat) :
    (codeTrapDeletionBasis 2).mulVec (fun j => codeTrapDeletionSign b j.val) 2=
      codeTrapDeletionRow 2 b 2 := by
  change (∑ j : Fin 9,(![-4,4,0,-12,-8,-8,8,-8,-4] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-4)*codeTrapDeletionSign b 0 + (4)*codeTrapDeletionSign b 1 + (-12)*codeTrapDeletionSign b 3 + (-8)*codeTrapDeletionSign b 4 + (-8)*codeTrapDeletionSign b 5 + (8)*codeTrapDeletionSign b 6 + (-8)*codeTrapDeletionSign b 7 + (-4)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_2_3 (b : Nat) :
    (codeTrapDeletionBasis 2).mulVec (fun j => codeTrapDeletionSign b j.val) 3=
      codeTrapDeletionRow 2 b 3 := by
  change (∑ j : Fin 9,(![-3,-1,-10,3,-2,-6,-2,0,-1] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-3)*codeTrapDeletionSign b 0 + (-1)*codeTrapDeletionSign b 1 + (-10)*codeTrapDeletionSign b 2 + (3)*codeTrapDeletionSign b 3 + (-2)*codeTrapDeletionSign b 4 + (-6)*codeTrapDeletionSign b 5 + (-2)*codeTrapDeletionSign b 6 + (-1)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_2_4 (b : Nat) :
    (codeTrapDeletionBasis 2).mulVec (fun j => codeTrapDeletionSign b j.val) 4=
      codeTrapDeletionRow 2 b 4 := by
  change (∑ j : Fin 9,(![-14,-2,-4,-2,-12,4,-4,-8,-10] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-14)*codeTrapDeletionSign b 0 + (-2)*codeTrapDeletionSign b 1 + (-4)*codeTrapDeletionSign b 2 + (-2)*codeTrapDeletionSign b 3 + (-12)*codeTrapDeletionSign b 4 + (4)*codeTrapDeletionSign b 5 + (-4)*codeTrapDeletionSign b 6 + (-8)*codeTrapDeletionSign b 7 + (-10)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_2_5 (b : Nat) :
    (codeTrapDeletionBasis 2).mulVec (fun j => codeTrapDeletionSign b j.val) 5=
      codeTrapDeletionRow 2 b 5 := by
  change (∑ j : Fin 9,(![11,1,2,5,10,-2,-6,8,9] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(11)*codeTrapDeletionSign b 0 + (1)*codeTrapDeletionSign b 1 + (2)*codeTrapDeletionSign b 2 + (5)*codeTrapDeletionSign b 3 + (10)*codeTrapDeletionSign b 4 + (-2)*codeTrapDeletionSign b 5 + (-6)*codeTrapDeletionSign b 6 + (8)*codeTrapDeletionSign b 7 + (9)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_2_6 (b : Nat) :
    (codeTrapDeletionBasis 2).mulVec (fun j => codeTrapDeletionSign b j.val) 6=
      codeTrapDeletionRow 2 b 6 := by
  change (∑ j : Fin 9,(![-12,-4,0,4,-8,8,-8,-8,-4] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-12)*codeTrapDeletionSign b 0 + (-4)*codeTrapDeletionSign b 1 + (4)*codeTrapDeletionSign b 3 + (-8)*codeTrapDeletionSign b 4 + (8)*codeTrapDeletionSign b 5 + (-8)*codeTrapDeletionSign b 6 + (-8)*codeTrapDeletionSign b 7 + (-4)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_2_7 (b : Nat) :
    (codeTrapDeletionBasis 2).mulVec (fun j => codeTrapDeletionSign b j.val) 7=
      codeTrapDeletionRow 2 b 7 := by
  change (∑ j : Fin 9,(![-1,-11,-6,17,2,6,-14,8,-3] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-1)*codeTrapDeletionSign b 0 + (-11)*codeTrapDeletionSign b 1 + (-6)*codeTrapDeletionSign b 2 + (17)*codeTrapDeletionSign b 3 + (2)*codeTrapDeletionSign b 4 + (6)*codeTrapDeletionSign b 5 + (-14)*codeTrapDeletionSign b 6 + (8)*codeTrapDeletionSign b 7 + (-3)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_2_8 (b : Nat) :
    (codeTrapDeletionBasis 2).mulVec (fun j => codeTrapDeletionSign b j.val) 8=
      codeTrapDeletionRow 2 b 8 := by
  change (∑ j : Fin 9,(![-2,2,-4,-6,4,-4,4,-8,2] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(-2)*codeTrapDeletionSign b 0 + (2)*codeTrapDeletionSign b 1 + (-4)*codeTrapDeletionSign b 2 + (-6)*codeTrapDeletionSign b 3 + (4)*codeTrapDeletionSign b 4 + (-4)*codeTrapDeletionSign b 5 + (4)*codeTrapDeletionSign b 6 + (-8)*codeTrapDeletionSign b 7 + (2)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_2_9 (b : Nat) :
    (codeTrapDeletionBasis 2).mulVec (fun j => codeTrapDeletionSign b j.val) 9=
      codeTrapDeletionRow 2 b 9 := by
  change (∑ j : Fin 9,(![10,6,4,-2,4,-4,4,8,-2] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(10)*codeTrapDeletionSign b 0 + (6)*codeTrapDeletionSign b 1 + (4)*codeTrapDeletionSign b 2 + (-2)*codeTrapDeletionSign b 3 + (4)*codeTrapDeletionSign b 4 + (-4)*codeTrapDeletionSign b 5 + (4)*codeTrapDeletionSign b 6 + (8)*codeTrapDeletionSign b 7 + (-2)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_2_10 (b : Nat) :
    (codeTrapDeletionBasis 2).mulVec (fun j => codeTrapDeletionSign b j.val) 10=
      codeTrapDeletionRow 2 b 10 := by
  change (∑ j : Fin 9,(![8,-8,0,8,0,0,-8,8,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(8)*codeTrapDeletionSign b 0 + (-8)*codeTrapDeletionSign b 1 + (8)*codeTrapDeletionSign b 3 + (-8)*codeTrapDeletionSign b 6 + (8)*codeTrapDeletionSign b 7
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_2_11 (b : Nat) :
    (codeTrapDeletionBasis 2).mulVec (fun j => codeTrapDeletionSign b j.val) 11=
      codeTrapDeletionRow 2 b 11 := by
  change (∑ j : Fin 9,(![8,0,0,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(8)*codeTrapDeletionSign b 0
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_2_12 (b : Nat) :
    (codeTrapDeletionBasis 2).mulVec (fun j => codeTrapDeletionSign b j.val) 12=
      codeTrapDeletionRow 2 b 12 := by
  change (∑ j : Fin 9,(![0,8,0,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(8)*codeTrapDeletionSign b 1
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_2_13 (b : Nat) :
    (codeTrapDeletionBasis 2).mulVec (fun j => codeTrapDeletionSign b j.val) 13=
      codeTrapDeletionRow 2 b 13 := by
  change (∑ j : Fin 9,(![0,0,8,0,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(8)*codeTrapDeletionSign b 2
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_2_14 (b : Nat) :
    (codeTrapDeletionBasis 2).mulVec (fun j => codeTrapDeletionSign b j.val) 14=
      codeTrapDeletionRow 2 b 14 := by
  change (∑ j : Fin 9,(![0,0,0,8,0,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(8)*codeTrapDeletionSign b 3
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_2_15 (b : Nat) :
    (codeTrapDeletionBasis 2).mulVec (fun j => codeTrapDeletionSign b j.val) 15=
      codeTrapDeletionRow 2 b 15 := by
  change (∑ j : Fin 9,(![0,0,0,0,8,0,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(8)*codeTrapDeletionSign b 4
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_2_16 (b : Nat) :
    (codeTrapDeletionBasis 2).mulVec (fun j => codeTrapDeletionSign b j.val) 16=
      codeTrapDeletionRow 2 b 16 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,8,0,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(8)*codeTrapDeletionSign b 5
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_2_17 (b : Nat) :
    (codeTrapDeletionBasis 2).mulVec (fun j => codeTrapDeletionSign b j.val) 17=
      codeTrapDeletionRow 2 b 17 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,8,0,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(8)*codeTrapDeletionSign b 6
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_2_18 (b : Nat) :
    (codeTrapDeletionBasis 2).mulVec (fun j => codeTrapDeletionSign b j.val) 18=
      codeTrapDeletionRow 2 b 18 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,0,8,0] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(8)*codeTrapDeletionSign b 7
  simp [Fin.sum_univ_succ]
  <;> ring

theorem codeTrapRowEval_2_19 (b : Nat) :
    (codeTrapDeletionBasis 2).mulVec (fun j => codeTrapDeletionSign b j.val) 19=
      codeTrapDeletionRow 2 b 19 := by
  change (∑ j : Fin 9,(![0,0,0,0,0,0,0,0,8] : Fin 9 → ℤ) j*codeTrapDeletionSign b j.val)=(8)*codeTrapDeletionSign b 8
  simp [Fin.sum_univ_succ]
  <;> ring

end CompletionTheory
