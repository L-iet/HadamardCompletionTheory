/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapFieldSeedBoolean
public import CompletionCodeTrap.CodeTrapCodeBoolean
public import Mathlib.Tactic.Ring
@[expose] public section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory

theorem trapCodeDigitSign_cast (b j : Nat) : (trapCodeDigitSign b j : ZMod 5)=
    (if j=0 then 1 else if b.testBit (j-1) then -1 else 1) := by
  by_cases hj : j=0 <;> by_cases hb : b.testBit (j-1) <;>
    simp [trapCodeDigitSign,hj,hb]
end CompletionTheory
