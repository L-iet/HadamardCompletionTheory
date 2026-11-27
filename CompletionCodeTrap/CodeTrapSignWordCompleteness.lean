/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapSignWordData
public import CompletionCodeTrap.CodeTrapFieldSeedComplete
@[expose] public section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory
theorem trapOldWord_complete (x : Fin 20 → Bool) (hfirst : positiveFirstBit x)
    (hx : trapBitFieldVector x∈trapOldCode) : ∃ i : Fin 12,x=trapOldWord i := by
  obtain ⟨b,hb⟩ := trapOld_word_seed x hfirst hx
  have hs : ∀ j : Fin 20,trapOldSeedVector b.val j=1 ∨ trapOldSeedVector b.val j= -1 := by
    intro j
    rw [hb]
    cases hbit : x j <;> simp [trapBitFieldVector,modularBitSign,hbit]
  obtain ⟨i,hi⟩ := trapOldSeed_complete b hs
  refine ⟨i,trapBitFieldVector_injective ?_⟩
  exact (hb.symm.trans (funext hi)).trans (trapOldWord_field i).symm

theorem trapNewWord_complete (x : Fin 20 → Bool) (hfirst : positiveFirstBit x)
    (hx : trapBitFieldVector x∈trapNewSpanCode) : ∃ i : Fin 20,x=trapNewWord i := by
  obtain ⟨b,hb⟩ := trapNew_word_seed x hfirst hx
  have hs : ∀ j : Fin 20,trapNewSeedVector b.val j=1 ∨ trapNewSeedVector b.val j= -1 := by
    intro j
    rw [hb]
    cases hbit : x j <;> simp [trapBitFieldVector,modularBitSign,hbit]
  obtain ⟨i,hi⟩ := trapNewSeed_complete b hs
  refine ⟨i,trapBitFieldVector_injective ?_⟩
  exact (hb.symm.trans (funext hi)).trans (trapNewWord_field i).symm

end CompletionTheory
