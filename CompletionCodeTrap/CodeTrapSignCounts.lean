/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapSignWordCompleteness
public import CompletionCodeTrap.CodeTrapCandidateMembership
@[expose] public section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory
attribute [local irreducible] codeSignCandidates
theorem trapOldCode_candidates : codeSignCandidates trapOldCode=
    Finset.univ.image trapOldWord := by
  classical
  apply Finset.ext
  intro x
  constructor
  · intro hx
    obtain ⟨hfirst,hcode⟩ := (trap_code_candidate_membership trapOldCode x).mp hx
    obtain ⟨i,hi⟩ := trapOldWord_complete x hfirst hcode
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi.symm⟩
  · intro hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    apply (trap_code_candidate_membership trapOldCode _).mpr
    refine ⟨trapOldWord_first i,?_⟩
    change trapBitFieldVector (trapOldWord i)∈trapOldCode
    rw [trapOldWord_field]
    exact trapOldRows_in_code i

theorem trapOldCode_sign_count : (codeSignCandidates trapOldCode).card=12 := by
  classical
  rw [trapOldCode_candidates,Finset.card_image_of_injective _ trapOldWord_injective]
  simp

theorem trapNewCode_candidates : codeSignCandidates trapNewSpanCode=
    Finset.univ.image trapNewWord := by
  classical
  apply Finset.ext
  intro x
  constructor
  · intro hx
    obtain ⟨hfirst,hcode⟩ := (trap_code_candidate_membership trapNewSpanCode x).mp hx
    obtain ⟨i,hi⟩ := trapNewWord_complete x hfirst hcode
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi.symm⟩
  · intro hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    apply (trap_code_candidate_membership trapNewSpanCode _).mpr
    refine ⟨trapNewWord_first i,?_⟩
    change trapBitFieldVector (trapNewWord i)∈trapNewSpanCode
    rw [trapNewWord_field]
    exact trapNewRows_in_code i

theorem trapNewCode_sign_count : (codeSignCandidates trapNewSpanCode).card=20 := by
  classical
  rw [trapNewCode_candidates,Finset.card_image_of_injective _ trapNewWord_injective]
  simp

end CompletionTheory
