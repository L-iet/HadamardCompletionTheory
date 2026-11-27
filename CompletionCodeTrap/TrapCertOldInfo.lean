/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapFiniteFieldData
@[expose] public section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
namespace CompletionTheory
theorem trapOldInfo_0 : ∀ j : Fin 10,((trapInformationSelector trapOldInformation)*trapOldBasis.transpose) 0 j=(if (0 : Fin 10)=j then 1 else 0) := by
  decide +kernel

theorem trapOldInfo_1 : ∀ j : Fin 10,((trapInformationSelector trapOldInformation)*trapOldBasis.transpose) 1 j=(if (1 : Fin 10)=j then 1 else 0) := by
  decide +kernel

theorem trapOldInfo_2 : ∀ j : Fin 10,((trapInformationSelector trapOldInformation)*trapOldBasis.transpose) 2 j=(if (2 : Fin 10)=j then 1 else 0) := by
  decide +kernel

theorem trapOldInfo_3 : ∀ j : Fin 10,((trapInformationSelector trapOldInformation)*trapOldBasis.transpose) 3 j=(if (3 : Fin 10)=j then 1 else 0) := by
  decide +kernel

theorem trapOldInfo_4 : ∀ j : Fin 10,((trapInformationSelector trapOldInformation)*trapOldBasis.transpose) 4 j=(if (4 : Fin 10)=j then 1 else 0) := by
  decide +kernel

theorem trapOldInfo_5 : ∀ j : Fin 10,((trapInformationSelector trapOldInformation)*trapOldBasis.transpose) 5 j=(if (5 : Fin 10)=j then 1 else 0) := by
  decide +kernel

theorem trapOldInfo_6 : ∀ j : Fin 10,((trapInformationSelector trapOldInformation)*trapOldBasis.transpose) 6 j=(if (6 : Fin 10)=j then 1 else 0) := by
  decide +kernel

theorem trapOldInfo_7 : ∀ j : Fin 10,((trapInformationSelector trapOldInformation)*trapOldBasis.transpose) 7 j=(if (7 : Fin 10)=j then 1 else 0) := by
  decide +kernel

theorem trapOldInfo_8 : ∀ j : Fin 10,((trapInformationSelector trapOldInformation)*trapOldBasis.transpose) 8 j=(if (8 : Fin 10)=j then 1 else 0) := by
  decide +kernel

theorem trapOldInfo_9 : ∀ j : Fin 10,((trapInformationSelector trapOldInformation)*trapOldBasis.transpose) 9 j=(if (9 : Fin 10)=j then 1 else 0) := by
  decide +kernel

end CompletionTheory
