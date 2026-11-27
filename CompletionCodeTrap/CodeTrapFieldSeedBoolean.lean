/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapFiniteFieldData
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.ZMod.Defs
@[expose] public section
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory

def trapNormalizedCoefficient (b : ℕ) (j : Fin 10) : ZMod 5 :=
  if j.val=0 then 1 else if b.testBit (j.val-1) then -1 else 1

def trapOldSeedVector (b : ℕ) : Fin 20 → ZMod 5 := trapOldBasis.transpose.mulVec (trapNormalizedCoefficient b)
def trapNewSeedVector (b : ℕ) : Fin 20 → ZMod 5 := trapNewBasis.transpose.mulVec (trapNormalizedCoefficient b)

def trapOldSeedOne (b : ℕ) : Bool := decide
  ((∀ j : Fin 20,trapOldSeedVector b j=1 ∨ trapOldSeedVector b j= -1) →
    ∃ i : Fin 12,∀ j,trapOldSeedVector b j=trapOldFieldMatrix i j)

def trapNewSeedOne (b : ℕ) : Bool := decide
  ((∀ j : Fin 20,trapNewSeedVector b j=1 ∨ trapNewSeedVector b j= -1) →
    ∃ i : Fin 20,∀ j,trapNewSeedVector b j=trapCompletedFieldMatrix i j)

def trapFieldSeedOne (d b : ℕ) : Bool := if d=0 then trapOldSeedOne b else trapNewSeedOne b

def trapFieldSeedBatch (d start : ℕ) : ℕ → Bool
  | 0 => true
  | k+1 => trapFieldSeedOne d (start+k) && trapFieldSeedBatch d start k
end CompletionTheory
