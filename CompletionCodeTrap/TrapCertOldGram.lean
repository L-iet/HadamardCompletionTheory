/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapFiniteFieldData
@[expose] public section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
namespace CompletionTheory
theorem trapOldGram_0 : ∀ j : Fin 10,(∑ k,trapOldBasis 0 k*trapOldBasis j k)=0 := by
  decide +kernel

theorem trapOldGram_1 : ∀ j : Fin 10,(∑ k,trapOldBasis 1 k*trapOldBasis j k)=0 := by
  decide +kernel

theorem trapOldGram_2 : ∀ j : Fin 10,(∑ k,trapOldBasis 2 k*trapOldBasis j k)=0 := by
  decide +kernel

theorem trapOldGram_3 : ∀ j : Fin 10,(∑ k,trapOldBasis 3 k*trapOldBasis j k)=0 := by
  decide +kernel

theorem trapOldGram_4 : ∀ j : Fin 10,(∑ k,trapOldBasis 4 k*trapOldBasis j k)=0 := by
  decide +kernel

theorem trapOldGram_5 : ∀ j : Fin 10,(∑ k,trapOldBasis 5 k*trapOldBasis j k)=0 := by
  decide +kernel

theorem trapOldGram_6 : ∀ j : Fin 10,(∑ k,trapOldBasis 6 k*trapOldBasis j k)=0 := by
  decide +kernel

theorem trapOldGram_7 : ∀ j : Fin 10,(∑ k,trapOldBasis 7 k*trapOldBasis j k)=0 := by
  decide +kernel

theorem trapOldGram_8 : ∀ j : Fin 10,(∑ k,trapOldBasis 8 k*trapOldBasis j k)=0 := by
  decide +kernel

theorem trapOldGram_9 : ∀ j : Fin 10,(∑ k,trapOldBasis 9 k*trapOldBasis j k)=0 := by
  decide +kernel

end CompletionTheory
