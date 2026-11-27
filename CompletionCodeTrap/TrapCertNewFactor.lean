/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapFiniteFieldData
@[expose] public section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
namespace CompletionTheory
theorem trapNewFactor_0 : ∀ j : Fin 20,(trapNewBasisFromRows*trapCompletedFieldMatrix) 0 j=trapNewBasis 0 j := by
  decide +kernel

theorem trapNewFactor_1 : ∀ j : Fin 20,(trapNewBasisFromRows*trapCompletedFieldMatrix) 1 j=trapNewBasis 1 j := by
  decide +kernel

theorem trapNewFactor_2 : ∀ j : Fin 20,(trapNewBasisFromRows*trapCompletedFieldMatrix) 2 j=trapNewBasis 2 j := by
  decide +kernel

theorem trapNewFactor_3 : ∀ j : Fin 20,(trapNewBasisFromRows*trapCompletedFieldMatrix) 3 j=trapNewBasis 3 j := by
  decide +kernel

theorem trapNewFactor_4 : ∀ j : Fin 20,(trapNewBasisFromRows*trapCompletedFieldMatrix) 4 j=trapNewBasis 4 j := by
  decide +kernel

theorem trapNewFactor_5 : ∀ j : Fin 20,(trapNewBasisFromRows*trapCompletedFieldMatrix) 5 j=trapNewBasis 5 j := by
  decide +kernel

theorem trapNewFactor_6 : ∀ j : Fin 20,(trapNewBasisFromRows*trapCompletedFieldMatrix) 6 j=trapNewBasis 6 j := by
  decide +kernel

theorem trapNewFactor_7 : ∀ j : Fin 20,(trapNewBasisFromRows*trapCompletedFieldMatrix) 7 j=trapNewBasis 7 j := by
  decide +kernel

theorem trapNewFactor_8 : ∀ j : Fin 20,(trapNewBasisFromRows*trapCompletedFieldMatrix) 8 j=trapNewBasis 8 j := by
  decide +kernel

theorem trapNewFactor_9 : ∀ j : Fin 20,(trapNewBasisFromRows*trapCompletedFieldMatrix) 9 j=trapNewBasis 9 j := by
  decide +kernel

end CompletionTheory
