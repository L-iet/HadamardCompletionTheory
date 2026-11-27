/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapCodeComplete
public import CompletionCodeTrap.CodeTrapFieldReflection
@[expose] public section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory
def trapOldClassIndex : Fin 12 → Fin 12 := ![0,11,5,2,1,9,8,10,3,7,6,4]
def trapNewClassIndex : Fin 20 → Fin 20 := ![0,9,17,12,2,6,14,13,3,19,18,4,16,8,11,1,15,5,7,10]
theorem trapOldClassMask_identification : ∀ i,trapOldClassMask i=codeTrapOldMasks (trapOldClassIndex i) := by decide +kernel

theorem trapNewClassMask_identification : ∀ i,trapNewClassMask i=trapCompletedMasks (trapNewClassIndex i) := by decide +kernel

theorem trapOldResidue_field (i : Fin 12) (j : Fin 20) :
    (trapOldResidueWord i j : ZMod 5)=trapOldFieldMatrix (trapOldClassIndex i) j := by
  change ((if (trapOldClassMask i).testBit j.val then (4 : ℤ) else 1 : ℤ) : ZMod 5)=
    ((if (codeTrapOldMasks (trapOldClassIndex i)).testBit j.val then (-1 : ℤ) else 1 : ℤ) : ZMod 5)
  rw [trapOldClassMask_identification]
  split <;> decide +kernel

theorem trapNewResidue_field (i : Fin 20) (j : Fin 20) :
    (trapNewResidueWord i j : ZMod 5)=trapCompletedFieldMatrix (trapNewClassIndex i) j := by
  change ((if (trapNewClassMask i).testBit j.val then (4 : ℤ) else 1 : ℤ) : ZMod 5)=
    ((if (trapCompletedMasks (trapNewClassIndex i)).testBit j.val then (-1 : ℤ) else 1 : ℤ) : ZMod 5)
  rw [trapNewClassMask_identification]
  split <;> decide +kernel

theorem trapResidue_sign_lift (r : ℤ) (hr : 0≤r ∧ r<5)
    (hs : (r : ZMod 5)=1 ∨ (r : ZMod 5)= -1) : r=1 ∨ r=4 := by
  have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 := by omega
  rcases hc with h|h|h|h|h
  · subst r
    have hb : ¬((0 : ZMod 5)=1 ∨ (0 : ZMod 5)= -1) := by decide +kernel
    exact (hb hs).elim
  · exact Or.inl h
  · subst r
    have hb : ¬((2 : ZMod 5)=1 ∨ (2 : ZMod 5)= -1) := by decide +kernel
    exact (hb hs).elim
  · subst r
    have hb : ¬((3 : ZMod 5)=1 ∨ (3 : ZMod 5)= -1) := by decide +kernel
    exact (hb hs).elim
  · exact Or.inr h
theorem trapOldSeed_complete (b : Fin 512)
    (hsign : ∀ j : Fin 20,trapOldSeedVector b.val j=1 ∨ trapOldSeedVector b.val j= -1) :
    ∃ i : Fin 12,∀ j,trapOldSeedVector b.val j=trapOldFieldMatrix i j := by
  have hr : ∀ j : Fin 20,trapCodewordEntry 0 b.val j.val=1 ∨ trapCodewordEntry 0 b.val j.val=4 := by
    intro j
    apply trapResidue_sign_lift _ (trapCodewordEntry_range 0 b.val j)
    rcases hsign j with h|h
    · exact Or.inl ((trapOldSeed_reflection b.val j).trans h)
    · exact Or.inr ((trapOldSeed_reflection b.val j).trans h)
  obtain ⟨k,hk⟩ := trapOldResidue_classification b hr
  refine ⟨trapOldClassIndex k,?_⟩
  intro j
  calc
    trapOldSeedVector b.val j=(trapCodewordEntry 0 b.val j.val : ZMod 5) := (trapOldSeed_reflection b.val j).symm
    _=(trapOldResidueWord k j : ZMod 5) := congrArg (fun z : ℤ => (z : ZMod 5)) (hk j)
    _=trapOldFieldMatrix (trapOldClassIndex k) j := trapOldResidue_field k j

theorem trapNewSeed_complete (b : Fin 512)
    (hsign : ∀ j : Fin 20,trapNewSeedVector b.val j=1 ∨ trapNewSeedVector b.val j= -1) :
    ∃ i : Fin 20,∀ j,trapNewSeedVector b.val j=trapCompletedFieldMatrix i j := by
  have hr : ∀ j : Fin 20,trapCodewordEntry 1 b.val j.val=1 ∨ trapCodewordEntry 1 b.val j.val=4 := by
    intro j
    apply trapResidue_sign_lift _ (trapCodewordEntry_range 1 b.val j)
    rcases hsign j with h|h
    · exact Or.inl ((trapNewSeed_reflection b.val j).trans h)
    · exact Or.inr ((trapNewSeed_reflection b.val j).trans h)
  obtain ⟨k,hk⟩ := trapNewResidue_classification b hr
  refine ⟨trapNewClassIndex k,?_⟩
  intro j
  calc
    trapNewSeedVector b.val j=(trapCodewordEntry 1 b.val j.val : ZMod 5) := (trapNewSeed_reflection b.val j).symm
    _=(trapNewResidueWord k j : ZMod 5) := congrArg (fun z : ℤ => (z : ZMod 5)) (hk j)
    _=trapCompletedFieldMatrix (trapNewClassIndex k) j := trapNewResidue_field k j

end CompletionTheory
