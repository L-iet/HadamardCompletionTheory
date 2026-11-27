/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapFieldReflectionRows_0_0
public import CompletionCodeTrap.CodeTrapFieldReflectionRows_0_1
public import CompletionCodeTrap.CodeTrapFieldReflectionRows_1_0
public import CompletionCodeTrap.CodeTrapFieldReflectionRows_1_1
@[expose] public section
namespace CompletionTheory
theorem trapOldSeed_reflection (b : Nat) (i : Fin 20) :
    (trapCodewordEntry 0 b i.val : ZMod 5)=trapOldSeedVector b i := by
  fin_cases i
  · exact trapFieldReflection_0_0 b
  · exact trapFieldReflection_0_1 b
  · exact trapFieldReflection_0_2 b
  · exact trapFieldReflection_0_3 b
  · exact trapFieldReflection_0_4 b
  · exact trapFieldReflection_0_5 b
  · exact trapFieldReflection_0_6 b
  · exact trapFieldReflection_0_7 b
  · exact trapFieldReflection_0_8 b
  · exact trapFieldReflection_0_9 b
  · exact trapFieldReflection_0_10 b
  · exact trapFieldReflection_0_11 b
  · exact trapFieldReflection_0_12 b
  · exact trapFieldReflection_0_13 b
  · exact trapFieldReflection_0_14 b
  · exact trapFieldReflection_0_15 b
  · exact trapFieldReflection_0_16 b
  · exact trapFieldReflection_0_17 b
  · exact trapFieldReflection_0_18 b
  · exact trapFieldReflection_0_19 b

theorem trapNewSeed_reflection (b : Nat) (i : Fin 20) :
    (trapCodewordEntry 1 b i.val : ZMod 5)=trapNewSeedVector b i := by
  fin_cases i
  · exact trapFieldReflection_1_0 b
  · exact trapFieldReflection_1_1 b
  · exact trapFieldReflection_1_2 b
  · exact trapFieldReflection_1_3 b
  · exact trapFieldReflection_1_4 b
  · exact trapFieldReflection_1_5 b
  · exact trapFieldReflection_1_6 b
  · exact trapFieldReflection_1_7 b
  · exact trapFieldReflection_1_8 b
  · exact trapFieldReflection_1_9 b
  · exact trapFieldReflection_1_10 b
  · exact trapFieldReflection_1_11 b
  · exact trapFieldReflection_1_12 b
  · exact trapFieldReflection_1_13 b
  · exact trapFieldReflection_1_14 b
  · exact trapFieldReflection_1_15 b
  · exact trapFieldReflection_1_16 b
  · exact trapFieldReflection_1_17 b
  · exact trapFieldReflection_1_18 b
  · exact trapFieldReflection_1_19 b

end CompletionTheory
