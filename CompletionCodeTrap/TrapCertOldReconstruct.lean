/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapFiniteFieldData
@[expose] public section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
namespace CompletionTheory
theorem trapOldReconstruct_0 : ∀ j : Fin 20,trapOldBasis.transpose.mulVec (fun k => trapOldFieldMatrix 0 (trapOldInformation k)) j=trapOldFieldMatrix 0 j := by
  decide +kernel

theorem trapOldReconstruct_1 : ∀ j : Fin 20,trapOldBasis.transpose.mulVec (fun k => trapOldFieldMatrix 1 (trapOldInformation k)) j=trapOldFieldMatrix 1 j := by
  decide +kernel

theorem trapOldReconstruct_2 : ∀ j : Fin 20,trapOldBasis.transpose.mulVec (fun k => trapOldFieldMatrix 2 (trapOldInformation k)) j=trapOldFieldMatrix 2 j := by
  decide +kernel

theorem trapOldReconstruct_3 : ∀ j : Fin 20,trapOldBasis.transpose.mulVec (fun k => trapOldFieldMatrix 3 (trapOldInformation k)) j=trapOldFieldMatrix 3 j := by
  decide +kernel

theorem trapOldReconstruct_4 : ∀ j : Fin 20,trapOldBasis.transpose.mulVec (fun k => trapOldFieldMatrix 4 (trapOldInformation k)) j=trapOldFieldMatrix 4 j := by
  decide +kernel

theorem trapOldReconstruct_5 : ∀ j : Fin 20,trapOldBasis.transpose.mulVec (fun k => trapOldFieldMatrix 5 (trapOldInformation k)) j=trapOldFieldMatrix 5 j := by
  decide +kernel

theorem trapOldReconstruct_6 : ∀ j : Fin 20,trapOldBasis.transpose.mulVec (fun k => trapOldFieldMatrix 6 (trapOldInformation k)) j=trapOldFieldMatrix 6 j := by
  decide +kernel

theorem trapOldReconstruct_7 : ∀ j : Fin 20,trapOldBasis.transpose.mulVec (fun k => trapOldFieldMatrix 7 (trapOldInformation k)) j=trapOldFieldMatrix 7 j := by
  decide +kernel

theorem trapOldReconstruct_8 : ∀ j : Fin 20,trapOldBasis.transpose.mulVec (fun k => trapOldFieldMatrix 8 (trapOldInformation k)) j=trapOldFieldMatrix 8 j := by
  decide +kernel

theorem trapOldReconstruct_9 : ∀ j : Fin 20,trapOldBasis.transpose.mulVec (fun k => trapOldFieldMatrix 9 (trapOldInformation k)) j=trapOldFieldMatrix 9 j := by
  decide +kernel

theorem trapOldReconstruct_10 : ∀ j : Fin 20,trapOldBasis.transpose.mulVec (fun k => trapOldFieldMatrix 10 (trapOldInformation k)) j=trapOldFieldMatrix 10 j := by
  decide +kernel

theorem trapOldReconstruct_11 : ∀ j : Fin 20,trapOldBasis.transpose.mulVec (fun k => trapOldFieldMatrix 11 (trapOldInformation k)) j=trapOldFieldMatrix 11 j := by
  decide +kernel

end CompletionTheory
