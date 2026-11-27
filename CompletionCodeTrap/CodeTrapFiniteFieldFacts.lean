/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.TrapCertOldGram
public import CompletionCodeTrap.TrapCertNewGram
public import CompletionCodeTrap.TrapCertOldInfo
public import CompletionCodeTrap.TrapCertNewInfo
public import CompletionCodeTrap.TrapCertOldFactor
public import CompletionCodeTrap.TrapCertNewFactor
public import CompletionCodeTrap.TrapCertPivotFactor
public import CompletionCodeTrap.TrapCertOldReconstruct
public import CompletionCodeTrap.TrapCertNewReconstruct
public import CompletionCodeTrap.TrapCertRetainedReconstruct
public import CompletionCodeTrap.TrapCertCompletedGram
@[expose] public section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory
theorem trapOldBasis_gram : trapOldBasis*trapOldBasis.transpose=0 := by
  apply Matrix.ext
  intro i j
  change (∑ k,trapOldBasis i k*trapOldBasis j k)=0
  fin_cases i
  · exact trapOldGram_0 j
  · exact trapOldGram_1 j
  · exact trapOldGram_2 j
  · exact trapOldGram_3 j
  · exact trapOldGram_4 j
  · exact trapOldGram_5 j
  · exact trapOldGram_6 j
  · exact trapOldGram_7 j
  · exact trapOldGram_8 j
  · exact trapOldGram_9 j

theorem trapOldBasis_information : (trapInformationSelector trapOldInformation)*trapOldBasis.transpose=1 := by
  apply Matrix.ext
  intro i j
  change ((trapInformationSelector trapOldInformation)*trapOldBasis.transpose) i j=(if i=j then 1 else 0)
  fin_cases i
  · exact trapOldInfo_0 j
  · exact trapOldInfo_1 j
  · exact trapOldInfo_2 j
  · exact trapOldInfo_3 j
  · exact trapOldInfo_4 j
  · exact trapOldInfo_5 j
  · exact trapOldInfo_6 j
  · exact trapOldInfo_7 j
  · exact trapOldInfo_8 j
  · exact trapOldInfo_9 j

theorem trapNewBasis_gram : trapNewBasis*trapNewBasis.transpose=0 := by
  apply Matrix.ext
  intro i j
  change (∑ k,trapNewBasis i k*trapNewBasis j k)=0
  fin_cases i
  · exact trapNewGram_0 j
  · exact trapNewGram_1 j
  · exact trapNewGram_2 j
  · exact trapNewGram_3 j
  · exact trapNewGram_4 j
  · exact trapNewGram_5 j
  · exact trapNewGram_6 j
  · exact trapNewGram_7 j
  · exact trapNewGram_8 j
  · exact trapNewGram_9 j

theorem trapNewBasis_information : (trapInformationSelector trapNewInformation)*trapNewBasis.transpose=1 := by
  apply Matrix.ext
  intro i j
  change ((trapInformationSelector trapNewInformation)*trapNewBasis.transpose) i j=(if i=j then 1 else 0)
  fin_cases i
  · exact trapNewInfo_0 j
  · exact trapNewInfo_1 j
  · exact trapNewInfo_2 j
  · exact trapNewInfo_3 j
  · exact trapNewInfo_4 j
  · exact trapNewInfo_5 j
  · exact trapNewInfo_6 j
  · exact trapNewInfo_7 j
  · exact trapNewInfo_8 j
  · exact trapNewInfo_9 j

theorem trapOldBasis_factor : trapOldBasisFromRows*trapOldFieldMatrix=trapOldBasis := by
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact trapOldFactor_0 j
  · exact trapOldFactor_1 j
  · exact trapOldFactor_2 j
  · exact trapOldFactor_3 j
  · exact trapOldFactor_4 j
  · exact trapOldFactor_5 j
  · exact trapOldFactor_6 j
  · exact trapOldFactor_7 j
  · exact trapOldFactor_8 j
  · exact trapOldFactor_9 j

theorem trapNewBasis_factor : trapNewBasisFromRows*trapCompletedFieldMatrix=trapNewBasis := by
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact trapNewFactor_0 j
  · exact trapNewFactor_1 j
  · exact trapNewFactor_2 j
  · exact trapNewFactor_3 j
  · exact trapNewFactor_4 j
  · exact trapNewFactor_5 j
  · exact trapNewFactor_6 j
  · exact trapNewFactor_7 j
  · exact trapNewFactor_8 j
  · exact trapNewFactor_9 j

theorem trapNewBasis_pivot_factor : trapNewBasisFromRetainedPivot*trapRetainedPivotMatrix=trapNewBasis := by
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact trapPivotFactor_0 j
  · exact trapPivotFactor_1 j
  · exact trapPivotFactor_2 j
  · exact trapPivotFactor_3 j
  · exact trapPivotFactor_4 j
  · exact trapPivotFactor_5 j
  · exact trapPivotFactor_6 j
  · exact trapPivotFactor_7 j
  · exact trapPivotFactor_8 j
  · exact trapPivotFactor_9 j

theorem trapOldRows_in_code : ∀ i : Fin 12,trapOldFieldMatrix i∈trapOldCode := by
  intro i
  refine ⟨fun k => trapOldFieldMatrix i (trapOldInformation k),?_⟩
  funext j
  change trapOldBasis.transpose.mulVec (fun k => trapOldFieldMatrix i (trapOldInformation k)) j=trapOldFieldMatrix i j
  fin_cases i
  · exact trapOldReconstruct_0 j
  · exact trapOldReconstruct_1 j
  · exact trapOldReconstruct_2 j
  · exact trapOldReconstruct_3 j
  · exact trapOldReconstruct_4 j
  · exact trapOldReconstruct_5 j
  · exact trapOldReconstruct_6 j
  · exact trapOldReconstruct_7 j
  · exact trapOldReconstruct_8 j
  · exact trapOldReconstruct_9 j
  · exact trapOldReconstruct_10 j
  · exact trapOldReconstruct_11 j

theorem trapNewRows_in_code : ∀ i : Fin 20,trapCompletedFieldMatrix i∈trapNewSpanCode := by
  intro i
  refine ⟨fun k => trapCompletedFieldMatrix i (trapNewInformation k),?_⟩
  funext j
  change trapNewBasis.transpose.mulVec (fun k => trapCompletedFieldMatrix i (trapNewInformation k)) j=trapCompletedFieldMatrix i j
  fin_cases i
  · exact trapNewReconstruct_0 j
  · exact trapNewReconstruct_1 j
  · exact trapNewReconstruct_2 j
  · exact trapNewReconstruct_3 j
  · exact trapNewReconstruct_4 j
  · exact trapNewReconstruct_5 j
  · exact trapNewReconstruct_6 j
  · exact trapNewReconstruct_7 j
  · exact trapNewReconstruct_8 j
  · exact trapNewReconstruct_9 j
  · exact trapNewReconstruct_10 j
  · exact trapNewReconstruct_11 j
  · exact trapNewReconstruct_12 j
  · exact trapNewReconstruct_13 j
  · exact trapNewReconstruct_14 j
  · exact trapNewReconstruct_15 j
  · exact trapNewReconstruct_16 j
  · exact trapNewReconstruct_17 j
  · exact trapNewReconstruct_18 j
  · exact trapNewReconstruct_19 j

theorem trapRetainedRows_in_code : ∀ i : Fin 10,trapCompletedFieldMatrix (trapTenToTwenty i)∈trapOldCode := by
  intro i
  refine ⟨fun k => trapCompletedFieldMatrix (trapTenToTwenty i) (trapOldInformation k),?_⟩
  funext j
  change trapOldBasis.transpose.mulVec (fun k => trapCompletedFieldMatrix (trapTenToTwenty i) (trapOldInformation k)) j=trapCompletedFieldMatrix (trapTenToTwenty i) j
  fin_cases i
  · exact trapRetainedReconstruct_0 j
  · exact trapRetainedReconstruct_1 j
  · exact trapRetainedReconstruct_2 j
  · exact trapRetainedReconstruct_3 j
  · exact trapRetainedReconstruct_4 j
  · exact trapRetainedReconstruct_5 j
  · exact trapRetainedReconstruct_6 j
  · exact trapRetainedReconstruct_7 j
  · exact trapRetainedReconstruct_8 j
  · exact trapRetainedReconstruct_9 j

theorem trapOldCode_finrank : Module.finrank (ZMod 5) trapOldCode=10 :=
  trapMatrixCode_finrank trapOldBasis (trapInformationSelector trapOldInformation) trapOldBasis_information

theorem trapNewSpanCode_finrank : Module.finrank (ZMod 5) trapNewSpanCode=10 :=
  trapMatrixCode_finrank trapNewBasis (trapInformationSelector trapNewInformation) trapNewBasis_information

theorem trapOldCode_self_dual : trapOldCode=(coordinateDotForm (ZMod 5) 20).orthogonal trapOldCode :=
  trapMatrixCode_self_dual trapOldBasis (trapInformationSelector trapOldInformation)
    trapOldBasis_information trapOldBasis_gram (by decide)

theorem trapNewSpanCode_self_dual : trapNewSpanCode=(coordinateDotForm (ZMod 5) 20).orthogonal trapNewSpanCode :=
  trapMatrixCode_self_dual trapNewBasis (trapInformationSelector trapNewInformation)
    trapNewBasis_information trapNewBasis_gram (by decide)

theorem trapOldCode_eq_rowspan : trapOldCode=Submodule.span (ZMod 5) (Set.range trapOldFieldMatrix) := by
  rw [← trapMatrixCode_eq_span_rows]
  apply le_antisymm
  · change trapMatrixCode trapOldBasis≤trapMatrixCode trapOldFieldMatrix
    rw [← trapOldBasis_factor]
    exact trapMatrixCode_mul_le _ _
  · exact trapMatrixCode_le_of_rows _ _ trapOldRows_in_code

theorem trapNewSpanCode_eq_rowspan : trapNewSpanCode=Submodule.span (ZMod 5) (Set.range trapCompletedFieldMatrix) := by
  rw [← trapMatrixCode_eq_span_rows]
  apply le_antisymm
  · change trapMatrixCode trapNewBasis≤trapMatrixCode trapCompletedFieldMatrix
    rw [← trapNewBasis_factor]
    exact trapMatrixCode_mul_le _ _
  · exact trapMatrixCode_le_of_rows _ _ trapNewRows_in_code

theorem trapCompleted_integer_gram : trapCompletedIntegerMatrix*trapCompletedIntegerMatrix.transpose=
    (20 : ℤ) • (1 : Matrix (Fin 20) (Fin 20) ℤ) := by
  apply Matrix.ext
  intro i j
  change (∑ k,trapCompletedIntegerMatrix i k*trapCompletedIntegerMatrix j k)=20*(if i=j then 1 else 0)
  rw [mul_ite,mul_one,mul_zero]
  fin_cases i
  · exact trapCompletedGram_0 j
  · exact trapCompletedGram_1 j
  · exact trapCompletedGram_2 j
  · exact trapCompletedGram_3 j
  · exact trapCompletedGram_4 j
  · exact trapCompletedGram_5 j
  · exact trapCompletedGram_6 j
  · exact trapCompletedGram_7 j
  · exact trapCompletedGram_8 j
  · exact trapCompletedGram_9 j
  · exact trapCompletedGram_10 j
  · exact trapCompletedGram_11 j
  · exact trapCompletedGram_12 j
  · exact trapCompletedGram_13 j
  · exact trapCompletedGram_14 j
  · exact trapCompletedGram_15 j
  · exact trapCompletedGram_16 j
  · exact trapCompletedGram_17 j
  · exact trapCompletedGram_18 j
  · exact trapCompletedGram_19 j

noncomputable def trapCompletedRealMatrix : Matrix (Fin 20) (Fin 20) ℝ := encodedRealFrame trapCompletedMasks

theorem trapCompleted_isHadamard : IsHadamard trapCompletedRealMatrix :=
  encodedRealFrame_partialHadamard trapCompletedMasks trapCompleted_integer_gram

theorem trapPivot_isotropic : (∑ j,trapPivotVector j*trapPivotVector j)=0 := by decide +kernel

theorem trapPivot_nonorthogonal_old_row : (∑ j,trapOldFieldMatrix 3 j*trapPivotVector j)≠0 := by decide +kernel

theorem trapPivot_not_in_old_code : trapPivotVector∉trapOldCode := by
  intro hv
  have horth : trapPivotVector∈(coordinateDotForm (ZMod 5) 20).orthogonal trapOldCode := trapOldCode_self_dual ▸ hv
  have hh := horth (trapOldFieldMatrix 3) (trapOldRows_in_code 3)
  exact trapPivot_nonorthogonal_old_row hh
end CompletionTheory
