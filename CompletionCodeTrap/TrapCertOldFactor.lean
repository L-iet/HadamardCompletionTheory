/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapFiniteFieldData
@[expose] public section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
namespace CompletionTheory
theorem trapOldFactor_0 : ∀ j : Fin 20,(trapOldBasisFromRows*trapOldFieldMatrix) 0 j=trapOldBasis 0 j := by
  decide +kernel

theorem trapOldFactor_1 : ∀ j : Fin 20,(trapOldBasisFromRows*trapOldFieldMatrix) 1 j=trapOldBasis 1 j := by
  decide +kernel

theorem trapOldFactor_2 : ∀ j : Fin 20,(trapOldBasisFromRows*trapOldFieldMatrix) 2 j=trapOldBasis 2 j := by
  decide +kernel

theorem trapOldFactor_3 : ∀ j : Fin 20,(trapOldBasisFromRows*trapOldFieldMatrix) 3 j=trapOldBasis 3 j := by
  decide +kernel

theorem trapOldFactor_4 : ∀ j : Fin 20,(trapOldBasisFromRows*trapOldFieldMatrix) 4 j=trapOldBasis 4 j := by
  decide +kernel

theorem trapOldFactor_5 : ∀ j : Fin 20,(trapOldBasisFromRows*trapOldFieldMatrix) 5 j=trapOldBasis 5 j := by
  decide +kernel

theorem trapOldFactor_6 : ∀ j : Fin 20,(trapOldBasisFromRows*trapOldFieldMatrix) 6 j=trapOldBasis 6 j := by
  decide +kernel

theorem trapOldFactor_7 : ∀ j : Fin 20,(trapOldBasisFromRows*trapOldFieldMatrix) 7 j=trapOldBasis 7 j := by
  decide +kernel

theorem trapOldFactor_8 : ∀ j : Fin 20,(trapOldBasisFromRows*trapOldFieldMatrix) 8 j=trapOldBasis 8 j := by
  decide +kernel

theorem trapOldFactor_9 : ∀ j : Fin 20,(trapOldBasisFromRows*trapOldFieldMatrix) 9 j=trapOldBasis 9 j := by
  decide +kernel

end CompletionTheory
