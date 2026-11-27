/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Lean.Elab.Tactic.Decide
@[expose] public section
namespace CompletionTheory

def repairBooleanU (e b j : Nat) : Int :=
  let sign : Int := if j=0 then 1 else if b.testBit (j-1) then -1 else 1
  if e=j+1 then 3*sign else sign

def repairBooleanRow (e b : Nat) : Nat → Int
  | 0 => (4 : Int)*(repairBooleanU e b 0) + (-8 : Int)*(repairBooleanU e b 1) + (4 : Int)*(repairBooleanU e b 2) + (-8 : Int)*(repairBooleanU e b 3) + (-12 : Int)*(repairBooleanU e b 4) + (4 : Int)*(repairBooleanU e b 5) + (-4 : Int)*(repairBooleanU e b 6) + (8 : Int)*(repairBooleanU e b 7) + (-4 : Int)*(repairBooleanU e b 8) + (4 : Int)*(repairBooleanU e b 9) + (8 : Int)*(repairBooleanU e b 10) + (8 : Int)*(repairBooleanU e b 11)
  | 1 => (-8 : Int)*(repairBooleanU e b 0) + (2 : Int)*(repairBooleanU e b 3) + (2 : Int)*(repairBooleanU e b 4) + (-4 : Int)*(repairBooleanU e b 6) + (-8 : Int)*(repairBooleanU e b 7) + (-4 : Int)*(repairBooleanU e b 8) + (-2 : Int)*(repairBooleanU e b 9) + (2 : Int)*(repairBooleanU e b 11)
  | 2 => (-4 : Int)*(repairBooleanU e b 0) + (-4 : Int)*(repairBooleanU e b 1) + (-4 : Int)*(repairBooleanU e b 2) + (-4 : Int)*(repairBooleanU e b 3) + (4 : Int)*(repairBooleanU e b 4) + (-4 : Int)*(repairBooleanU e b 5) + (-8 : Int)*(repairBooleanU e b 6) + (-12 : Int)*(repairBooleanU e b 7) + (-8 : Int)*(repairBooleanU e b 9) + (-8 : Int)*(repairBooleanU e b 10) + (-8 : Int)*(repairBooleanU e b 11)
  | 3 => (6 : Int)*(repairBooleanU e b 0) + (4 : Int)*(repairBooleanU e b 1) + (2 : Int)*(repairBooleanU e b 2) + (3 : Int)*(repairBooleanU e b 3) + (-3 : Int)*(repairBooleanU e b 4) + (2 : Int)*(repairBooleanU e b 5) + (10 : Int)*(repairBooleanU e b 6) + (12 : Int)*(repairBooleanU e b 7) + (4 : Int)*(repairBooleanU e b 8) + (7 : Int)*(repairBooleanU e b 9) + (6 : Int)*(repairBooleanU e b 10) + (3 : Int)*(repairBooleanU e b 11)
  | 4 => (-4 : Int)*(repairBooleanU e b 2) + (2 : Int)*(repairBooleanU e b 3) + (2 : Int)*(repairBooleanU e b 4) + (-4 : Int)*(repairBooleanU e b 5) + (4 : Int)*(repairBooleanU e b 6) + (2 : Int)*(repairBooleanU e b 9) + (-4 : Int)*(repairBooleanU e b 10) + (-2 : Int)*(repairBooleanU e b 11)
  | 5 => (2 : Int)*(repairBooleanU e b 0) + (8 : Int)*(repairBooleanU e b 1) + (2 : Int)*(repairBooleanU e b 2) + (5 : Int)*(repairBooleanU e b 3) + (7 : Int)*(repairBooleanU e b 4) + (2 : Int)*(repairBooleanU e b 5) + (6 : Int)*(repairBooleanU e b 6) + (4 : Int)*(repairBooleanU e b 7) + (8 : Int)*(repairBooleanU e b 8) + repairBooleanU e b 9 + (2 : Int)*(repairBooleanU e b 10) + repairBooleanU e b 11
  | 6 => (-4 : Int)*(repairBooleanU e b 1) + (4 : Int)*(repairBooleanU e b 2) + (-2 : Int)*(repairBooleanU e b 3) + (-6 : Int)*(repairBooleanU e b 4) + (-4 : Int)*(repairBooleanU e b 6) + (4 : Int)*(repairBooleanU e b 7) + (-4 : Int)*(repairBooleanU e b 8) + (2 : Int)*(repairBooleanU e b 9) + (4 : Int)*(repairBooleanU e b 10) + (2 : Int)*(repairBooleanU e b 11)
  | 7 => (-8 : Int)*(repairBooleanU e b 0) + (12 : Int)*(repairBooleanU e b 1) + (-4 : Int)*(repairBooleanU e b 2) + (10 : Int)*(repairBooleanU e b 3) + (10 : Int)*(repairBooleanU e b 4) + (-4 : Int)*(repairBooleanU e b 5) + (8 : Int)*(repairBooleanU e b 6) + (-4 : Int)*(repairBooleanU e b 7) + (6 : Int)*(repairBooleanU e b 9) + (2 : Int)*(repairBooleanU e b 11)
  | 8 => (-2 : Int)*(repairBooleanU e b 0) + (-4 : Int)*(repairBooleanU e b 1) + (-2 : Int)*(repairBooleanU e b 2) + (-5 : Int)*(repairBooleanU e b 3) + repairBooleanU e b 4 + (-2 : Int)*(repairBooleanU e b 5) + (-6 : Int)*(repairBooleanU e b 6) + (-8 : Int)*(repairBooleanU e b 7) + (-9 : Int)*(repairBooleanU e b 9) + (-10 : Int)*(repairBooleanU e b 10) + (-9 : Int)*(repairBooleanU e b 11)
  | 9 => (-4 : Int)*(repairBooleanU e b 0) + (12 : Int)*(repairBooleanU e b 1) + (-4 : Int)*(repairBooleanU e b 2) + (12 : Int)*(repairBooleanU e b 3) + (12 : Int)*(repairBooleanU e b 4) + (8 : Int)*(repairBooleanU e b 6) + (-4 : Int)*(repairBooleanU e b 7) + (4 : Int)*(repairBooleanU e b 8)
  | 10 => (10 : Int)*(repairBooleanU e b 0) + (-16 : Int)*(repairBooleanU e b 1) + (6 : Int)*(repairBooleanU e b 2) + (-15 : Int)*(repairBooleanU e b 3) + (-17 : Int)*(repairBooleanU e b 4) + (6 : Int)*(repairBooleanU e b 5) + (-10 : Int)*(repairBooleanU e b 6) + (8 : Int)*(repairBooleanU e b 7) + (-4 : Int)*(repairBooleanU e b 8) + (-3 : Int)*(repairBooleanU e b 9) + (2 : Int)*(repairBooleanU e b 10) + repairBooleanU e b 11
  | 11 => (4 : Int)*(repairBooleanU e b 0)
  | 12 => (-4 : Int)*(repairBooleanU e b 1) + (-4 : Int)*(repairBooleanU e b 2) + (-4 : Int)*(repairBooleanU e b 3) + (-4 : Int)*(repairBooleanU e b 4) + (-4 : Int)*(repairBooleanU e b 5) + (-4 : Int)*(repairBooleanU e b 6) + (-4 : Int)*(repairBooleanU e b 7) + (-4 : Int)*(repairBooleanU e b 8) + (-4 : Int)*(repairBooleanU e b 9) + (-4 : Int)*(repairBooleanU e b 10) + (-4 : Int)*(repairBooleanU e b 11)
  | 13 => (4 : Int)*(repairBooleanU e b 1)
  | 14 => (4 : Int)*(repairBooleanU e b 2)
  | 15 => (4 : Int)*(repairBooleanU e b 3)
  | 16 => (4 : Int)*(repairBooleanU e b 4)
  | 17 => (4 : Int)*(repairBooleanU e b 5)
  | 18 => (4 : Int)*(repairBooleanU e b 6)
  | 19 => (4 : Int)*(repairBooleanU e b 7)
  | 20 => (4 : Int)*(repairBooleanU e b 8)
  | 21 => (4 : Int)*(repairBooleanU e b 9)
  | 22 => (4 : Int)*(repairBooleanU e b 10)
  | 23 => (4 : Int)*(repairBooleanU e b 11)
  | _ => 0

def repairBooleanOne (e b : Nat) : Bool :=
  let r0 := repairBooleanRow e b 0
  let r1 := repairBooleanRow e b 1
  let r2 := repairBooleanRow e b 2
  let r3 := repairBooleanRow e b 3
  let r4 := repairBooleanRow e b 4
  let r5 := repairBooleanRow e b 5
  let r6 := repairBooleanRow e b 6
  let r7 := repairBooleanRow e b 7
  let r8 := repairBooleanRow e b 8
  let r9 := repairBooleanRow e b 9
  let r10 := repairBooleanRow e b 10
  let r11 := repairBooleanRow e b 11
  let r12 := repairBooleanRow e b 12
  let r13 := repairBooleanRow e b 13
  let r14 := repairBooleanRow e b 14
  let r15 := repairBooleanRow e b 15
  let r16 := repairBooleanRow e b 16
  let r17 := repairBooleanRow e b 17
  let r18 := repairBooleanRow e b 18
  let r19 := repairBooleanRow e b 19
  let r20 := repairBooleanRow e b 20
  let r21 := repairBooleanRow e b 21
  let r22 := repairBooleanRow e b 22
  let r23 := repairBooleanRow e b 23
  if (r0%8 == 4) && (r1%8 == 4) && (r2%8 == 4) && (r3%8 == 4) && (r4%8 == 4) && (r5%8 == 4) && (r6%8 == 4) && (r7%8 == 4) && (r8%8 == 4) && (r9%8 == 4) && (r10%8 == 4) && (r11%8 == 4) && (r12%8 == 4) && (r13%8 == 4) && (r14%8 == 4) && (r15%8 == 4) && (r16%8 == 4) && (r17%8 == 4) && (r18%8 == 4) && (r19%8 == 4) && (r20%8 == 4) && (r21%8 == 4) && (r22%8 == 4) && (r23%8 == 4) then
    decide (640 ≤ r0*r0 + r1*r1 + r2*r2 + r3*r3 + r4*r4 + r5*r5 + r6*r6 + r7*r7 + r8*r8 + r9*r9 + r10*r10 + r11*r11 + r12*r12 + r13*r13 + r14*r14 + r15*r15 + r16*r16 + r17*r17 + r18*r18 + r19*r19 + r20*r20 + r21*r21 + r22*r22 + r23*r23)
  else true

def repairBooleanBatch (e start : Nat) : Nat → Bool
  | 0 => true
  | k+1 => repairBooleanOne e (start+k) && repairBooleanBatch e start k

theorem repairBooleanSmoke : repairBooleanBatch 0 0 16=true := by
  decide +kernel

end CompletionTheory
