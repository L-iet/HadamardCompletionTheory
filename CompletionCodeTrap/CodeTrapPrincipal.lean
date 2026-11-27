/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapSignCounts
public import CompletionCodeTrap.CodeTrapNeighbor
public import CompletionCodeTrap.CodeTrapRealLoss
@[expose] public section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] CompletionTheory.codeSignCandidates
namespace CompletionTheory

theorem finite_self_dual_code_trap :
    Module.finrank (ZMod 5) trapOldCode=10 ∧
    trapOldCode=(coordinateDotForm (ZMod 5) 20).orthogonal trapOldCode ∧
    (codeSignCandidates trapOldCode).card=12 ∧
    codeSignCandidates trapOldCode=Finset.univ.image trapOldWord ∧
    (∀ i : Fin 12,positiveFirstBit (trapOldWord i)) ∧
    trapOldCode=Submodule.span (ZMod 5) (Set.range trapOldFieldMatrix) ∧
    IsPartialHadamard trapOldRealMatrix ∧ NoSignExtension trapOldRealMatrix ∧
    (∀ z : Fin 20 → ℤ,(∀ j,z j=1 ∨ z j= -1) →
      (∀ i,z≠codeTrapOldIntegerMatrix i ∧ z≠ -codeTrapOldIntegerMatrix i) →
      (Finset.univ.filter (fun i : Fin 12 => (∑ j,codeTrapOldIntegerMatrix i j*z j)=0)).card≤10) ∧
    (∀ i : Fin 10,trapRetainedOldIndex i≠3 ∧ trapRetainedOldIndex i≠8 ∧
      ∀ j,trapCompletedRealMatrix (trapTenToTwenty i) j=trapOldRealMatrix (trapRetainedOldIndex i) j) ∧
    (∀ i : Fin 12,i≠3 → i≠8 → ∃ j,trapRetainedOldIndex j=i) ∧
    Matrix.IsHadamard trapCompletedRealMatrix ∧
    trapNewSpanCode=Submodule.span (ZMod 5) (Set.range trapCompletedFieldMatrix) ∧
    Module.finrank (ZMod 5) trapNewSpanCode=10 ∧
    trapNewSpanCode=(coordinateDotForm (ZMod 5) 20).orthogonal trapNewSpanCode ∧
    trapNewSpanCode=bilinearCodePivot (coordinateDotForm (ZMod 5) 20) trapOldCode trapPivotVector ∧
    Module.finrank (ZMod 5) ↥(trapOldCode ⊓ trapNewSpanCode)=9 ∧
    Module.finrank (ZMod 5) ↥(trapOldCode ⊔ trapNewSpanCode)=11 ∧
    trapNewSpanCode≠trapOldCode ∧
    (codeSignCandidates trapNewSpanCode).card=20 ∧
    codeSignCandidates trapNewSpanCode=Finset.univ.image trapNewWord ∧
    (∀ i : Fin 20,positiveFirstBit (trapNewWord i)) ∧
    (∀ H : Matrix (Fin 20) (Fin 20) ℝ,Matrix.IsHadamard H → 2≤trapOldRealRowLoss H) ∧
    trapOldRealRowLoss trapCompletedRealMatrix=2 := by
  refine ⟨trapOldCode_finrank,trapOldCode_self_dual,trapOldCode_sign_count,trapOldCode_candidates,
    trapOldWord_first,trapOldCode_eq_rowspan,trapOldReal_partialHadamard,trapOldReal_terminal,
    codeTrap_new_sign_compatibility_at_most_ten,?_,trapRetainedOldIndex_covers,
    trapCompleted_mathlib_hadamard,trapNewSpanCode_eq_rowspan,trapNewSpanCode_finrank,
    trapNewSpanCode_self_dual,trapNewSpanCode_eq_pivot,trapCodes_intersection_finrank,
    trapCodes_union_finrank,trapCodes_distinct,trapNewCode_sign_count,trapNewCode_candidates,
    trapNewWord_first,trapEveryRealCompletion_loses_two,trapCompleted_real_old_row_loss_two⟩
  intro i
  exact ⟨(trapRetainedOldIndex_properties i).1,(trapRetainedOldIndex_properties i).2.1,
    trapCompletedReal_retention i⟩
end CompletionTheory
