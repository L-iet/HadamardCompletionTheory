/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapFieldReflectionBase
@[expose] public section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory
theorem trapFieldReflection_1_0 (b : Nat) :
    (trapCodewordEntry 1 b 0 : ZMod 5)=trapNewSeedVector b 0 := by
  change ((((1)*trapCodeDigitSign b 0)%5 : ℤ) : ZMod 5)=
    ∑ j : Fin 10,(![1,0,0,0,0,0,0,0,0,0] : Fin 10 → ZMod 5) j*trapNormalizedCoefficient b j
  have hm : ((((1)*trapCodeDigitSign b 0)%5 : ℤ) : ZMod 5)=(((1)*trapCodeDigitSign b 0 : ℤ) : ZMod 5) := ZMod.intCast_mod _ 5
  rw [hm]
  simp only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,trapCodeDigitSign_cast]
  simp [Fin.sum_univ_succ,trapNormalizedCoefficient]
  <;> ring

theorem trapFieldReflection_1_1 (b : Nat) :
    (trapCodewordEntry 1 b 1 : ZMod 5)=trapNewSeedVector b 1 := by
  change ((((1)*trapCodeDigitSign b 1)%5 : ℤ) : ZMod 5)=
    ∑ j : Fin 10,(![0,1,0,0,0,0,0,0,0,0] : Fin 10 → ZMod 5) j*trapNormalizedCoefficient b j
  have hm : ((((1)*trapCodeDigitSign b 1)%5 : ℤ) : ZMod 5)=(((1)*trapCodeDigitSign b 1 : ℤ) : ZMod 5) := ZMod.intCast_mod _ 5
  rw [hm]
  simp only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,trapCodeDigitSign_cast]
  simp [Fin.sum_univ_succ,trapNormalizedCoefficient]
  <;> ring

theorem trapFieldReflection_1_2 (b : Nat) :
    (trapCodewordEntry 1 b 2 : ZMod 5)=trapNewSeedVector b 2 := by
  change ((((1)*trapCodeDigitSign b 2)%5 : ℤ) : ZMod 5)=
    ∑ j : Fin 10,(![0,0,1,0,0,0,0,0,0,0] : Fin 10 → ZMod 5) j*trapNormalizedCoefficient b j
  have hm : ((((1)*trapCodeDigitSign b 2)%5 : ℤ) : ZMod 5)=(((1)*trapCodeDigitSign b 2 : ℤ) : ZMod 5) := ZMod.intCast_mod _ 5
  rw [hm]
  simp only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,trapCodeDigitSign_cast]
  simp [Fin.sum_univ_succ,trapNormalizedCoefficient]
  <;> ring

theorem trapFieldReflection_1_3 (b : Nat) :
    (trapCodewordEntry 1 b 3 : ZMod 5)=trapNewSeedVector b 3 := by
  change ((((1)*trapCodeDigitSign b 3)%5 : ℤ) : ZMod 5)=
    ∑ j : Fin 10,(![0,0,0,1,0,0,0,0,0,0] : Fin 10 → ZMod 5) j*trapNormalizedCoefficient b j
  have hm : ((((1)*trapCodeDigitSign b 3)%5 : ℤ) : ZMod 5)=(((1)*trapCodeDigitSign b 3 : ℤ) : ZMod 5) := ZMod.intCast_mod _ 5
  rw [hm]
  simp only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,trapCodeDigitSign_cast]
  simp [Fin.sum_univ_succ,trapNormalizedCoefficient]
  <;> ring

theorem trapFieldReflection_1_4 (b : Nat) :
    (trapCodewordEntry 1 b 4 : ZMod 5)=trapNewSeedVector b 4 := by
  change ((((1)*trapCodeDigitSign b 4)%5 : ℤ) : ZMod 5)=
    ∑ j : Fin 10,(![0,0,0,0,1,0,0,0,0,0] : Fin 10 → ZMod 5) j*trapNormalizedCoefficient b j
  have hm : ((((1)*trapCodeDigitSign b 4)%5 : ℤ) : ZMod 5)=(((1)*trapCodeDigitSign b 4 : ℤ) : ZMod 5) := ZMod.intCast_mod _ 5
  rw [hm]
  simp only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,trapCodeDigitSign_cast]
  simp [Fin.sum_univ_succ,trapNormalizedCoefficient]
  <;> ring

theorem trapFieldReflection_1_5 (b : Nat) :
    (trapCodewordEntry 1 b 5 : ZMod 5)=trapNewSeedVector b 5 := by
  change ((((1)*trapCodeDigitSign b 5)%5 : ℤ) : ZMod 5)=
    ∑ j : Fin 10,(![0,0,0,0,0,1,0,0,0,0] : Fin 10 → ZMod 5) j*trapNormalizedCoefficient b j
  have hm : ((((1)*trapCodeDigitSign b 5)%5 : ℤ) : ZMod 5)=(((1)*trapCodeDigitSign b 5 : ℤ) : ZMod 5) := ZMod.intCast_mod _ 5
  rw [hm]
  simp only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,trapCodeDigitSign_cast]
  simp [Fin.sum_univ_succ,trapNormalizedCoefficient]
  <;> ring

theorem trapFieldReflection_1_6 (b : Nat) :
    (trapCodewordEntry 1 b 6 : ZMod 5)=trapNewSeedVector b 6 := by
  change ((((1)*trapCodeDigitSign b 6)%5 : ℤ) : ZMod 5)=
    ∑ j : Fin 10,(![0,0,0,0,0,0,1,0,0,0] : Fin 10 → ZMod 5) j*trapNormalizedCoefficient b j
  have hm : ((((1)*trapCodeDigitSign b 6)%5 : ℤ) : ZMod 5)=(((1)*trapCodeDigitSign b 6 : ℤ) : ZMod 5) := ZMod.intCast_mod _ 5
  rw [hm]
  simp only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,trapCodeDigitSign_cast]
  simp [Fin.sum_univ_succ,trapNormalizedCoefficient]
  <;> ring

theorem trapFieldReflection_1_7 (b : Nat) :
    (trapCodewordEntry 1 b 7 : ZMod 5)=trapNewSeedVector b 7 := by
  change ((((1)*trapCodeDigitSign b 7)%5 : ℤ) : ZMod 5)=
    ∑ j : Fin 10,(![0,0,0,0,0,0,0,1,0,0] : Fin 10 → ZMod 5) j*trapNormalizedCoefficient b j
  have hm : ((((1)*trapCodeDigitSign b 7)%5 : ℤ) : ZMod 5)=(((1)*trapCodeDigitSign b 7 : ℤ) : ZMod 5) := ZMod.intCast_mod _ 5
  rw [hm]
  simp only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,trapCodeDigitSign_cast]
  simp [Fin.sum_univ_succ,trapNormalizedCoefficient]
  <;> ring

theorem trapFieldReflection_1_8 (b : Nat) :
    (trapCodewordEntry 1 b 8 : ZMod 5)=trapNewSeedVector b 8 := by
  change ((((1)*trapCodeDigitSign b 8)%5 : ℤ) : ZMod 5)=
    ∑ j : Fin 10,(![0,0,0,0,0,0,0,0,1,0] : Fin 10 → ZMod 5) j*trapNormalizedCoefficient b j
  have hm : ((((1)*trapCodeDigitSign b 8)%5 : ℤ) : ZMod 5)=(((1)*trapCodeDigitSign b 8 : ℤ) : ZMod 5) := ZMod.intCast_mod _ 5
  rw [hm]
  simp only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,trapCodeDigitSign_cast]
  simp [Fin.sum_univ_succ,trapNormalizedCoefficient]
  <;> ring

theorem trapFieldReflection_1_9 (b : Nat) :
    (trapCodewordEntry 1 b 9 : ZMod 5)=trapNewSeedVector b 9 := by
  change ((((3)*trapCodeDigitSign b 0 + (3)*trapCodeDigitSign b 1 + (3)*trapCodeDigitSign b 2 + (4)*trapCodeDigitSign b 3 + (1)*trapCodeDigitSign b 4 + (3)*trapCodeDigitSign b 5 + (4)*trapCodeDigitSign b 8)%5 : ℤ) : ZMod 5)=
    ∑ j : Fin 10,(![3,3,3,4,1,3,0,0,4,0] : Fin 10 → ZMod 5) j*trapNormalizedCoefficient b j
  have hm : ((((3)*trapCodeDigitSign b 0 + (3)*trapCodeDigitSign b 1 + (3)*trapCodeDigitSign b 2 + (4)*trapCodeDigitSign b 3 + (1)*trapCodeDigitSign b 4 + (3)*trapCodeDigitSign b 5 + (4)*trapCodeDigitSign b 8)%5 : ℤ) : ZMod 5)=(((3)*trapCodeDigitSign b 0 + (3)*trapCodeDigitSign b 1 + (3)*trapCodeDigitSign b 2 + (4)*trapCodeDigitSign b 3 + (1)*trapCodeDigitSign b 4 + (3)*trapCodeDigitSign b 5 + (4)*trapCodeDigitSign b 8 : ℤ) : ZMod 5) := ZMod.intCast_mod _ 5
  rw [hm]
  simp only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,trapCodeDigitSign_cast]
  simp [Fin.sum_univ_succ,trapNormalizedCoefficient]
  <;> ring

end CompletionTheory
