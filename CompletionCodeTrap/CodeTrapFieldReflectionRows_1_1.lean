/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapFieldReflectionBase
@[expose] public section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory
theorem trapFieldReflection_1_10 (b : Nat) :
    (trapCodewordEntry 1 b 10 : ZMod 5)=trapNewSeedVector b 10 := by
  change ((((2)*trapCodeDigitSign b 0 + (3)*trapCodeDigitSign b 1 + (4)*trapCodeDigitSign b 3 + (4)*trapCodeDigitSign b 4 + (4)*trapCodeDigitSign b 5 + (2)*trapCodeDigitSign b 6 + (2)*trapCodeDigitSign b 8)%5 : ℤ) : ZMod 5)=
    ∑ j : Fin 10,(![2,3,0,4,4,4,2,0,2,0] : Fin 10 → ZMod 5) j*trapNormalizedCoefficient b j
  have hm : ((((2)*trapCodeDigitSign b 0 + (3)*trapCodeDigitSign b 1 + (4)*trapCodeDigitSign b 3 + (4)*trapCodeDigitSign b 4 + (4)*trapCodeDigitSign b 5 + (2)*trapCodeDigitSign b 6 + (2)*trapCodeDigitSign b 8)%5 : ℤ) : ZMod 5)=(((2)*trapCodeDigitSign b 0 + (3)*trapCodeDigitSign b 1 + (4)*trapCodeDigitSign b 3 + (4)*trapCodeDigitSign b 4 + (4)*trapCodeDigitSign b 5 + (2)*trapCodeDigitSign b 6 + (2)*trapCodeDigitSign b 8 : ℤ) : ZMod 5) := ZMod.intCast_mod _ 5
  rw [hm]
  simp only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,trapCodeDigitSign_cast]
  simp [Fin.sum_univ_succ,trapNormalizedCoefficient]
  <;> ring

theorem trapFieldReflection_1_11 (b : Nat) :
    (trapCodewordEntry 1 b 11 : ZMod 5)=trapNewSeedVector b 11 := by
  change ((((1)*trapCodeDigitSign b 9)%5 : ℤ) : ZMod 5)=
    ∑ j : Fin 10,(![0,0,0,0,0,0,0,0,0,1] : Fin 10 → ZMod 5) j*trapNormalizedCoefficient b j
  have hm : ((((1)*trapCodeDigitSign b 9)%5 : ℤ) : ZMod 5)=(((1)*trapCodeDigitSign b 9 : ℤ) : ZMod 5) := ZMod.intCast_mod _ 5
  rw [hm]
  simp only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,trapCodeDigitSign_cast]
  simp [Fin.sum_univ_succ,trapNormalizedCoefficient]
  <;> ring

theorem trapFieldReflection_1_12 (b : Nat) :
    (trapCodewordEntry 1 b 12 : ZMod 5)=trapNewSeedVector b 12 := by
  change ((((3)*trapCodeDigitSign b 0 + (2)*trapCodeDigitSign b 1 + (4)*trapCodeDigitSign b 2 + (2)*trapCodeDigitSign b 6 + (4)*trapCodeDigitSign b 7 + (2)*trapCodeDigitSign b 8 + (4)*trapCodeDigitSign b 9)%5 : ℤ) : ZMod 5)=
    ∑ j : Fin 10,(![3,2,4,0,0,0,2,4,2,4] : Fin 10 → ZMod 5) j*trapNormalizedCoefficient b j
  have hm : ((((3)*trapCodeDigitSign b 0 + (2)*trapCodeDigitSign b 1 + (4)*trapCodeDigitSign b 2 + (2)*trapCodeDigitSign b 6 + (4)*trapCodeDigitSign b 7 + (2)*trapCodeDigitSign b 8 + (4)*trapCodeDigitSign b 9)%5 : ℤ) : ZMod 5)=(((3)*trapCodeDigitSign b 0 + (2)*trapCodeDigitSign b 1 + (4)*trapCodeDigitSign b 2 + (2)*trapCodeDigitSign b 6 + (4)*trapCodeDigitSign b 7 + (2)*trapCodeDigitSign b 8 + (4)*trapCodeDigitSign b 9 : ℤ) : ZMod 5) := ZMod.intCast_mod _ 5
  rw [hm]
  simp only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,trapCodeDigitSign_cast]
  simp [Fin.sum_univ_succ,trapNormalizedCoefficient]
  <;> ring

theorem trapFieldReflection_1_13 (b : Nat) :
    (trapCodewordEntry 1 b 13 : ZMod 5)=trapNewSeedVector b 13 := by
  change ((((1)*trapCodeDigitSign b 0 + (2)*trapCodeDigitSign b 2 + (2)*trapCodeDigitSign b 3 + (3)*trapCodeDigitSign b 4 + (4)*trapCodeDigitSign b 6 + (1)*trapCodeDigitSign b 7 + (3)*trapCodeDigitSign b 9)%5 : ℤ) : ZMod 5)=
    ∑ j : Fin 10,(![1,0,2,2,3,0,4,1,0,3] : Fin 10 → ZMod 5) j*trapNormalizedCoefficient b j
  have hm : ((((1)*trapCodeDigitSign b 0 + (2)*trapCodeDigitSign b 2 + (2)*trapCodeDigitSign b 3 + (3)*trapCodeDigitSign b 4 + (4)*trapCodeDigitSign b 6 + (1)*trapCodeDigitSign b 7 + (3)*trapCodeDigitSign b 9)%5 : ℤ) : ZMod 5)=(((1)*trapCodeDigitSign b 0 + (2)*trapCodeDigitSign b 2 + (2)*trapCodeDigitSign b 3 + (3)*trapCodeDigitSign b 4 + (4)*trapCodeDigitSign b 6 + (1)*trapCodeDigitSign b 7 + (3)*trapCodeDigitSign b 9 : ℤ) : ZMod 5) := ZMod.intCast_mod _ 5
  rw [hm]
  simp only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,trapCodeDigitSign_cast]
  simp [Fin.sum_univ_succ,trapNormalizedCoefficient]
  <;> ring

theorem trapFieldReflection_1_14 (b : Nat) :
    (trapCodewordEntry 1 b 14 : ZMod 5)=trapNewSeedVector b 14 := by
  change ((((1)*trapCodeDigitSign b 0 + (2)*trapCodeDigitSign b 3 + (1)*trapCodeDigitSign b 4 + (1)*trapCodeDigitSign b 6 + (2)*trapCodeDigitSign b 7 + (2)*trapCodeDigitSign b 8 + (2)*trapCodeDigitSign b 9)%5 : ℤ) : ZMod 5)=
    ∑ j : Fin 10,(![1,0,0,2,1,0,1,2,2,2] : Fin 10 → ZMod 5) j*trapNormalizedCoefficient b j
  have hm : ((((1)*trapCodeDigitSign b 0 + (2)*trapCodeDigitSign b 3 + (1)*trapCodeDigitSign b 4 + (1)*trapCodeDigitSign b 6 + (2)*trapCodeDigitSign b 7 + (2)*trapCodeDigitSign b 8 + (2)*trapCodeDigitSign b 9)%5 : ℤ) : ZMod 5)=(((1)*trapCodeDigitSign b 0 + (2)*trapCodeDigitSign b 3 + (1)*trapCodeDigitSign b 4 + (1)*trapCodeDigitSign b 6 + (2)*trapCodeDigitSign b 7 + (2)*trapCodeDigitSign b 8 + (2)*trapCodeDigitSign b 9 : ℤ) : ZMod 5) := ZMod.intCast_mod _ 5
  rw [hm]
  simp only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,trapCodeDigitSign_cast]
  simp [Fin.sum_univ_succ,trapNormalizedCoefficient]
  <;> ring

theorem trapFieldReflection_1_15 (b : Nat) :
    (trapCodewordEntry 1 b 15 : ZMod 5)=trapNewSeedVector b 15 := by
  change ((((3)*trapCodeDigitSign b 0 + (3)*trapCodeDigitSign b 1 + (4)*trapCodeDigitSign b 2 + (2)*trapCodeDigitSign b 4 + (2)*trapCodeDigitSign b 5 + (4)*trapCodeDigitSign b 6 + (4)*trapCodeDigitSign b 7 + (3)*trapCodeDigitSign b 8 + (1)*trapCodeDigitSign b 9)%5 : ℤ) : ZMod 5)=
    ∑ j : Fin 10,(![3,3,4,0,2,2,4,4,3,1] : Fin 10 → ZMod 5) j*trapNormalizedCoefficient b j
  have hm : ((((3)*trapCodeDigitSign b 0 + (3)*trapCodeDigitSign b 1 + (4)*trapCodeDigitSign b 2 + (2)*trapCodeDigitSign b 4 + (2)*trapCodeDigitSign b 5 + (4)*trapCodeDigitSign b 6 + (4)*trapCodeDigitSign b 7 + (3)*trapCodeDigitSign b 8 + (1)*trapCodeDigitSign b 9)%5 : ℤ) : ZMod 5)=(((3)*trapCodeDigitSign b 0 + (3)*trapCodeDigitSign b 1 + (4)*trapCodeDigitSign b 2 + (2)*trapCodeDigitSign b 4 + (2)*trapCodeDigitSign b 5 + (4)*trapCodeDigitSign b 6 + (4)*trapCodeDigitSign b 7 + (3)*trapCodeDigitSign b 8 + (1)*trapCodeDigitSign b 9 : ℤ) : ZMod 5) := ZMod.intCast_mod _ 5
  rw [hm]
  simp only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,trapCodeDigitSign_cast]
  simp [Fin.sum_univ_succ,trapNormalizedCoefficient]
  <;> ring

theorem trapFieldReflection_1_16 (b : Nat) :
    (trapCodewordEntry 1 b 16 : ZMod 5)=trapNewSeedVector b 16 := by
  change ((((1)*trapCodeDigitSign b 1 + (1)*trapCodeDigitSign b 2 + (3)*trapCodeDigitSign b 3 + (3)*trapCodeDigitSign b 4 + (1)*trapCodeDigitSign b 5 + (3)*trapCodeDigitSign b 6 + (2)*trapCodeDigitSign b 7 + (4)*trapCodeDigitSign b 8 + (3)*trapCodeDigitSign b 9)%5 : ℤ) : ZMod 5)=
    ∑ j : Fin 10,(![0,1,1,3,3,1,3,2,4,3] : Fin 10 → ZMod 5) j*trapNormalizedCoefficient b j
  have hm : ((((1)*trapCodeDigitSign b 1 + (1)*trapCodeDigitSign b 2 + (3)*trapCodeDigitSign b 3 + (3)*trapCodeDigitSign b 4 + (1)*trapCodeDigitSign b 5 + (3)*trapCodeDigitSign b 6 + (2)*trapCodeDigitSign b 7 + (4)*trapCodeDigitSign b 8 + (3)*trapCodeDigitSign b 9)%5 : ℤ) : ZMod 5)=(((1)*trapCodeDigitSign b 1 + (1)*trapCodeDigitSign b 2 + (3)*trapCodeDigitSign b 3 + (3)*trapCodeDigitSign b 4 + (1)*trapCodeDigitSign b 5 + (3)*trapCodeDigitSign b 6 + (2)*trapCodeDigitSign b 7 + (4)*trapCodeDigitSign b 8 + (3)*trapCodeDigitSign b 9 : ℤ) : ZMod 5) := ZMod.intCast_mod _ 5
  rw [hm]
  simp only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,trapCodeDigitSign_cast]
  simp [Fin.sum_univ_succ,trapNormalizedCoefficient]
  <;> ring

theorem trapFieldReflection_1_17 (b : Nat) :
    (trapCodewordEntry 1 b 17 : ZMod 5)=trapNewSeedVector b 17 := by
  change ((((1)*trapCodeDigitSign b 0 + (1)*trapCodeDigitSign b 3 + (4)*trapCodeDigitSign b 4 + (2)*trapCodeDigitSign b 5 + (3)*trapCodeDigitSign b 6 + (3)*trapCodeDigitSign b 7 + (2)*trapCodeDigitSign b 8)%5 : ℤ) : ZMod 5)=
    ∑ j : Fin 10,(![1,0,0,1,4,2,3,3,2,0] : Fin 10 → ZMod 5) j*trapNormalizedCoefficient b j
  have hm : ((((1)*trapCodeDigitSign b 0 + (1)*trapCodeDigitSign b 3 + (4)*trapCodeDigitSign b 4 + (2)*trapCodeDigitSign b 5 + (3)*trapCodeDigitSign b 6 + (3)*trapCodeDigitSign b 7 + (2)*trapCodeDigitSign b 8)%5 : ℤ) : ZMod 5)=(((1)*trapCodeDigitSign b 0 + (1)*trapCodeDigitSign b 3 + (4)*trapCodeDigitSign b 4 + (2)*trapCodeDigitSign b 5 + (3)*trapCodeDigitSign b 6 + (3)*trapCodeDigitSign b 7 + (2)*trapCodeDigitSign b 8 : ℤ) : ZMod 5) := ZMod.intCast_mod _ 5
  rw [hm]
  simp only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,trapCodeDigitSign_cast]
  simp [Fin.sum_univ_succ,trapNormalizedCoefficient]
  <;> ring

theorem trapFieldReflection_1_18 (b : Nat) :
    (trapCodewordEntry 1 b 18 : ZMod 5)=trapNewSeedVector b 18 := by
  change ((((1)*trapCodeDigitSign b 1 + (2)*trapCodeDigitSign b 2 + (3)*trapCodeDigitSign b 3 + (3)*trapCodeDigitSign b 4 + (4)*trapCodeDigitSign b 5 + (1)*trapCodeDigitSign b 8 + (2)*trapCodeDigitSign b 9)%5 : ℤ) : ZMod 5)=
    ∑ j : Fin 10,(![0,1,2,3,3,4,0,0,1,2] : Fin 10 → ZMod 5) j*trapNormalizedCoefficient b j
  have hm : ((((1)*trapCodeDigitSign b 1 + (2)*trapCodeDigitSign b 2 + (3)*trapCodeDigitSign b 3 + (3)*trapCodeDigitSign b 4 + (4)*trapCodeDigitSign b 5 + (1)*trapCodeDigitSign b 8 + (2)*trapCodeDigitSign b 9)%5 : ℤ) : ZMod 5)=(((1)*trapCodeDigitSign b 1 + (2)*trapCodeDigitSign b 2 + (3)*trapCodeDigitSign b 3 + (3)*trapCodeDigitSign b 4 + (4)*trapCodeDigitSign b 5 + (1)*trapCodeDigitSign b 8 + (2)*trapCodeDigitSign b 9 : ℤ) : ZMod 5) := ZMod.intCast_mod _ 5
  rw [hm]
  simp only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,trapCodeDigitSign_cast]
  simp [Fin.sum_univ_succ,trapNormalizedCoefficient]
  <;> ring

theorem trapFieldReflection_1_19 (b : Nat) :
    (trapCodewordEntry 1 b 19 : ZMod 5)=trapNewSeedVector b 19 := by
  change ((((1)*trapCodeDigitSign b 1 + (3)*trapCodeDigitSign b 2 + (3)*trapCodeDigitSign b 4 + (3)*trapCodeDigitSign b 5 + (3)*trapCodeDigitSign b 7 + (4)*trapCodeDigitSign b 8 + (4)*trapCodeDigitSign b 9)%5 : ℤ) : ZMod 5)=
    ∑ j : Fin 10,(![0,1,3,0,3,3,0,3,4,4] : Fin 10 → ZMod 5) j*trapNormalizedCoefficient b j
  have hm : ((((1)*trapCodeDigitSign b 1 + (3)*trapCodeDigitSign b 2 + (3)*trapCodeDigitSign b 4 + (3)*trapCodeDigitSign b 5 + (3)*trapCodeDigitSign b 7 + (4)*trapCodeDigitSign b 8 + (4)*trapCodeDigitSign b 9)%5 : ℤ) : ZMod 5)=(((1)*trapCodeDigitSign b 1 + (3)*trapCodeDigitSign b 2 + (3)*trapCodeDigitSign b 4 + (3)*trapCodeDigitSign b 5 + (3)*trapCodeDigitSign b 7 + (4)*trapCodeDigitSign b 8 + (4)*trapCodeDigitSign b 9 : ℤ) : ZMod 5) := ZMod.intCast_mod _ 5
  rw [hm]
  simp only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,trapCodeDigitSign_cast]
  simp [Fin.sum_univ_succ,trapNormalizedCoefficient]
  <;> ring

end CompletionTheory
