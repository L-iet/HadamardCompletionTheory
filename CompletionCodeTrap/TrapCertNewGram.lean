/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapFiniteFieldData
@[expose] public section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
namespace CompletionTheory
theorem trapNewGram_0 : ∀ j : Fin 10,(∑ k,trapNewBasis 0 k*trapNewBasis j k)=0 := by
  decide +kernel

theorem trapNewGram_1 : ∀ j : Fin 10,(∑ k,trapNewBasis 1 k*trapNewBasis j k)=0 := by
  decide +kernel

theorem trapNewGram_2 : ∀ j : Fin 10,(∑ k,trapNewBasis 2 k*trapNewBasis j k)=0 := by
  decide +kernel

theorem trapNewGram_3 : ∀ j : Fin 10,(∑ k,trapNewBasis 3 k*trapNewBasis j k)=0 := by
  decide +kernel

theorem trapNewGram_4 : ∀ j : Fin 10,(∑ k,trapNewBasis 4 k*trapNewBasis j k)=0 := by
  decide +kernel

theorem trapNewGram_5 : ∀ j : Fin 10,(∑ k,trapNewBasis 5 k*trapNewBasis j k)=0 := by
  decide +kernel

theorem trapNewGram_6 : ∀ j : Fin 10,(∑ k,trapNewBasis 6 k*trapNewBasis j k)=0 := by
  decide +kernel

theorem trapNewGram_7 : ∀ j : Fin 10,(∑ k,trapNewBasis 7 k*trapNewBasis j k)=0 := by
  decide +kernel

theorem trapNewGram_8 : ∀ j : Fin 10,(∑ k,trapNewBasis 8 k*trapNewBasis j k)=0 := by
  decide +kernel

theorem trapNewGram_9 : ∀ j : Fin 10,(∑ k,trapNewBasis 9 k*trapNewBasis j k)=0 := by
  decide +kernel

end CompletionTheory
