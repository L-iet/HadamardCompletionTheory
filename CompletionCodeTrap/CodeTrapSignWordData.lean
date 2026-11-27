/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapNormalizedWords
@[expose] public section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory
def trapOldWord (i : Fin 12) (j : Fin 20) : Bool := (codeTrapOldMasks i).testBit j.val
def trapNewWord (i : Fin 20) (j : Fin 20) : Bool := (trapCompletedMasks i).testBit j.val

theorem trapOldWord_field (i : Fin 12) : trapBitFieldVector (trapOldWord i)=trapOldFieldMatrix i := rfl
theorem trapNewWord_field (i : Fin 20) : trapBitFieldVector (trapNewWord i)=trapCompletedFieldMatrix i := rfl
theorem trapOldWord_zero : ∀ i,trapOldWord i 0=false := by decide +kernel

theorem trapOldWord_first (i : Fin 12) : positiveFirstBit (trapOldWord i) := by
  intro j hj
  have he : j=0 := Fin.ext hj
  subst j
  exact trapOldWord_zero i

theorem trapOldWords_separate : ∀ i j : Fin 12,i≠j → ∃ k : Fin 20,trapOldWord i k≠trapOldWord j k := by
  decide +kernel

theorem trapOldWord_injective : Function.Injective trapOldWord := by
  intro i j hij
  by_contra hne
  obtain ⟨k,hk⟩ := trapOldWords_separate i j hne
  exact hk (congrFun hij k)

theorem trapNewWord_zero : ∀ i,trapNewWord i 0=false := by decide +kernel

theorem trapNewWord_first (i : Fin 20) : positiveFirstBit (trapNewWord i) := by
  intro j hj
  have he : j=0 := Fin.ext hj
  subst j
  exact trapNewWord_zero i

theorem trapNewWords_separate : ∀ i j : Fin 20,i≠j → ∃ k : Fin 20,trapNewWord i k≠trapNewWord j k := by
  decide +kernel

theorem trapNewWord_injective : Function.Injective trapNewWord := by
  intro i j hij
  by_contra hne
  obtain ⟨k,hk⟩ := trapNewWords_separate i j hne
  exact hk (congrFun hij k)

end CompletionTheory
