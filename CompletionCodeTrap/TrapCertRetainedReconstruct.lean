/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapFiniteFieldData
@[expose] public section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
namespace CompletionTheory
theorem trapRetainedReconstruct_0 : ∀ j : Fin 20,trapOldBasis.transpose.mulVec (fun k => trapCompletedFieldMatrix 0 (trapOldInformation k)) j=trapCompletedFieldMatrix 0 j := by
  decide +kernel

theorem trapRetainedReconstruct_1 : ∀ j : Fin 20,trapOldBasis.transpose.mulVec (fun k => trapCompletedFieldMatrix 1 (trapOldInformation k)) j=trapCompletedFieldMatrix 1 j := by
  decide +kernel

theorem trapRetainedReconstruct_2 : ∀ j : Fin 20,trapOldBasis.transpose.mulVec (fun k => trapCompletedFieldMatrix 2 (trapOldInformation k)) j=trapCompletedFieldMatrix 2 j := by
  decide +kernel

theorem trapRetainedReconstruct_3 : ∀ j : Fin 20,trapOldBasis.transpose.mulVec (fun k => trapCompletedFieldMatrix 3 (trapOldInformation k)) j=trapCompletedFieldMatrix 3 j := by
  decide +kernel

theorem trapRetainedReconstruct_4 : ∀ j : Fin 20,trapOldBasis.transpose.mulVec (fun k => trapCompletedFieldMatrix 4 (trapOldInformation k)) j=trapCompletedFieldMatrix 4 j := by
  decide +kernel

theorem trapRetainedReconstruct_5 : ∀ j : Fin 20,trapOldBasis.transpose.mulVec (fun k => trapCompletedFieldMatrix 5 (trapOldInformation k)) j=trapCompletedFieldMatrix 5 j := by
  decide +kernel

theorem trapRetainedReconstruct_6 : ∀ j : Fin 20,trapOldBasis.transpose.mulVec (fun k => trapCompletedFieldMatrix 6 (trapOldInformation k)) j=trapCompletedFieldMatrix 6 j := by
  decide +kernel

theorem trapRetainedReconstruct_7 : ∀ j : Fin 20,trapOldBasis.transpose.mulVec (fun k => trapCompletedFieldMatrix 7 (trapOldInformation k)) j=trapCompletedFieldMatrix 7 j := by
  decide +kernel

theorem trapRetainedReconstruct_8 : ∀ j : Fin 20,trapOldBasis.transpose.mulVec (fun k => trapCompletedFieldMatrix 8 (trapOldInformation k)) j=trapCompletedFieldMatrix 8 j := by
  decide +kernel

theorem trapRetainedReconstruct_9 : ∀ j : Fin 20,trapOldBasis.transpose.mulVec (fun k => trapCompletedFieldMatrix 9 (trapOldInformation k)) j=trapCompletedFieldMatrix 9 j := by
  decide +kernel

end CompletionTheory
