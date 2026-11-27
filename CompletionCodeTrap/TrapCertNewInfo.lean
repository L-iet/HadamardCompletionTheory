/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapFiniteFieldData
@[expose] public section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
namespace CompletionTheory
theorem trapNewInfo_0 : ∀ j : Fin 10,((trapInformationSelector trapNewInformation)*trapNewBasis.transpose) 0 j=(if (0 : Fin 10)=j then 1 else 0) := by
  decide +kernel

theorem trapNewInfo_1 : ∀ j : Fin 10,((trapInformationSelector trapNewInformation)*trapNewBasis.transpose) 1 j=(if (1 : Fin 10)=j then 1 else 0) := by
  decide +kernel

theorem trapNewInfo_2 : ∀ j : Fin 10,((trapInformationSelector trapNewInformation)*trapNewBasis.transpose) 2 j=(if (2 : Fin 10)=j then 1 else 0) := by
  decide +kernel

theorem trapNewInfo_3 : ∀ j : Fin 10,((trapInformationSelector trapNewInformation)*trapNewBasis.transpose) 3 j=(if (3 : Fin 10)=j then 1 else 0) := by
  decide +kernel

theorem trapNewInfo_4 : ∀ j : Fin 10,((trapInformationSelector trapNewInformation)*trapNewBasis.transpose) 4 j=(if (4 : Fin 10)=j then 1 else 0) := by
  decide +kernel

theorem trapNewInfo_5 : ∀ j : Fin 10,((trapInformationSelector trapNewInformation)*trapNewBasis.transpose) 5 j=(if (5 : Fin 10)=j then 1 else 0) := by
  decide +kernel

theorem trapNewInfo_6 : ∀ j : Fin 10,((trapInformationSelector trapNewInformation)*trapNewBasis.transpose) 6 j=(if (6 : Fin 10)=j then 1 else 0) := by
  decide +kernel

theorem trapNewInfo_7 : ∀ j : Fin 10,((trapInformationSelector trapNewInformation)*trapNewBasis.transpose) 7 j=(if (7 : Fin 10)=j then 1 else 0) := by
  decide +kernel

theorem trapNewInfo_8 : ∀ j : Fin 10,((trapInformationSelector trapNewInformation)*trapNewBasis.transpose) 8 j=(if (8 : Fin 10)=j then 1 else 0) := by
  decide +kernel

theorem trapNewInfo_9 : ∀ j : Fin 10,((trapInformationSelector trapNewInformation)*trapNewBasis.transpose) 9 j=(if (9 : Fin 10)=j then 1 else 0) := by
  decide +kernel

end CompletionTheory
