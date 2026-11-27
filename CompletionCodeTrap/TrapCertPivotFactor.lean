/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapFiniteFieldData
@[expose] public section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
namespace CompletionTheory
theorem trapPivotFactor_0 : ∀ j : Fin 20,(trapNewBasisFromRetainedPivot*trapRetainedPivotMatrix) 0 j=trapNewBasis 0 j := by
  decide +kernel

theorem trapPivotFactor_1 : ∀ j : Fin 20,(trapNewBasisFromRetainedPivot*trapRetainedPivotMatrix) 1 j=trapNewBasis 1 j := by
  decide +kernel

theorem trapPivotFactor_2 : ∀ j : Fin 20,(trapNewBasisFromRetainedPivot*trapRetainedPivotMatrix) 2 j=trapNewBasis 2 j := by
  decide +kernel

theorem trapPivotFactor_3 : ∀ j : Fin 20,(trapNewBasisFromRetainedPivot*trapRetainedPivotMatrix) 3 j=trapNewBasis 3 j := by
  decide +kernel

theorem trapPivotFactor_4 : ∀ j : Fin 20,(trapNewBasisFromRetainedPivot*trapRetainedPivotMatrix) 4 j=trapNewBasis 4 j := by
  decide +kernel

theorem trapPivotFactor_5 : ∀ j : Fin 20,(trapNewBasisFromRetainedPivot*trapRetainedPivotMatrix) 5 j=trapNewBasis 5 j := by
  decide +kernel

theorem trapPivotFactor_6 : ∀ j : Fin 20,(trapNewBasisFromRetainedPivot*trapRetainedPivotMatrix) 6 j=trapNewBasis 6 j := by
  decide +kernel

theorem trapPivotFactor_7 : ∀ j : Fin 20,(trapNewBasisFromRetainedPivot*trapRetainedPivotMatrix) 7 j=trapNewBasis 7 j := by
  decide +kernel

theorem trapPivotFactor_8 : ∀ j : Fin 20,(trapNewBasisFromRetainedPivot*trapRetainedPivotMatrix) 8 j=trapNewBasis 8 j := by
  decide +kernel

theorem trapPivotFactor_9 : ∀ j : Fin 20,(trapNewBasisFromRetainedPivot*trapRetainedPivotMatrix) 9 j=trapNewBasis 9 j := by
  decide +kernel

end CompletionTheory
