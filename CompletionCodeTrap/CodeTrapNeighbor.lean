/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapFiniteFieldFacts
@[expose] public section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory

noncomputable def trapPivotCode : Submodule (ZMod 5) (Fin 20 → ZMod 5) :=
  bilinearCodePivot (coordinateDotForm (ZMod 5) 20) trapOldCode trapPivotVector

theorem trapPivotCode_finrank : Module.finrank (ZMod 5) trapPivotCode=10 := by
  have hp := self_dual_bilinear_pivot (coordinateDotForm (ZMod 5) 20)
    (coordinateDotForm_symm (ZMod 5) 20) (coordinateDotForm_nondegenerate (ZMod 5) 20)
    trapOldCode trapOldCode_self_dual trapPivotVector trapPivot_not_in_old_code trapPivot_isotropic
  exact hp.2.2.2.1.trans trapOldCode_finrank

theorem trapRetainedPivotRows_in_pivot : ∀ i : Fin 11,trapRetainedPivotMatrix i∈trapPivotCode := by
  intro i
  by_cases hi : i.val<10
  · let j : Fin 10 := ⟨i.val,hi⟩
    have he : trapElevenToTwenty i=trapTenToTwenty j := Fin.ext rfl
    change trapCompletedFieldMatrix (trapElevenToTwenty i)∈trapPivotCode
    rw [he]
    apply Submodule.mem_sup_left
    refine ⟨trapRetainedRows_in_code j,?_⟩
    change (coordinateDotForm (ZMod 5) 20) trapPivotVector (trapCompletedFieldMatrix (trapTenToTwenty j))=0
    rw [(coordinateDotForm_symm (ZMod 5) 20).eq trapPivotVector (trapCompletedFieldMatrix (trapTenToTwenty j))]
    have hv : trapPivotVector∈(coordinateDotForm (ZMod 5) 20).orthogonal trapNewSpanCode :=
      trapNewSpanCode_self_dual ▸ trapNewRows_in_code 10
    exact hv _ (trapNewRows_in_code _)
  · have he : i=(10 : Fin 11) := Fin.ext (by have hh := i.isLt; omega)
    subst i
    change trapPivotVector∈trapPivotCode
    apply Submodule.mem_sup_right
    exact Submodule.mem_span_singleton.mpr ⟨1,one_smul _ _⟩

theorem trapNewSpanCode_le_pivot : trapNewSpanCode≤trapPivotCode := by
  change trapMatrixCode trapNewBasis≤trapPivotCode
  rw [← trapNewBasis_pivot_factor]
  exact le_trans (trapMatrixCode_mul_le _ _)
    (trapMatrixCode_le_of_rows _ _ trapRetainedPivotRows_in_pivot)

theorem trapNewSpanCode_eq_pivot : trapNewSpanCode=trapPivotCode := by
  apply Submodule.eq_of_le_of_finrank_le trapNewSpanCode_le_pivot
  rw [trapPivotCode_finrank,trapNewSpanCode_finrank]

theorem trapCodes_intersection_finrank : Module.finrank (ZMod 5) ↥(trapOldCode ⊓ trapNewSpanCode)=9 := by
  have hp := self_dual_coordinate_pivot trapOldCode trapOldCode_self_dual
    trapPivotVector trapPivot_not_in_old_code trapPivot_isotropic
  rw [trapNewSpanCode_eq_pivot]
  exact hp.2.1

theorem trapCodes_distinct : trapNewSpanCode≠trapOldCode := by
  have hp := self_dual_coordinate_pivot trapOldCode trapOldCode_self_dual
    trapPivotVector trapPivot_not_in_old_code trapPivot_isotropic
  rw [trapNewSpanCode_eq_pivot]
  exact hp.2.2.2

theorem trapCodes_union_finrank : Module.finrank (ZMod 5) ↥(trapOldCode ⊔ trapNewSpanCode)=11 := by
  have hh := Submodule.finrank_sup_add_finrank_inf_eq trapOldCode trapNewSpanCode
  rw [trapOldCode_finrank,trapNewSpanCode_finrank,trapCodes_intersection_finrank] at hh
  omega
end CompletionTheory
