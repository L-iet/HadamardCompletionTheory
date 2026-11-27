/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Lean.Elab.Tactic.Decide
@[expose] public section
set_option maxRecDepth 20000
namespace CompletionTheory

def repairCoverU (b j : Nat) : Int := if b.testBit j then -1 else 1

def repairCoverRow (b i : Nat) : Int :=
  match i with
  | 0 => (4)*repairCoverU b 0 + (-8)*repairCoverU b 2 + (4)*repairCoverU b 3 + (-8)*repairCoverU b 4 + (-12)*repairCoverU b 5 + (4)*repairCoverU b 6 + (-4)*repairCoverU b 7 + (8)*repairCoverU b 8 + (-4)*repairCoverU b 9 + (4)*repairCoverU b 10 + (8)*repairCoverU b 11 + (8)*repairCoverU b 12
  | 1 => (-8)*repairCoverU b 0 + (2)*repairCoverU b 4 + (2)*repairCoverU b 5 + (-4)*repairCoverU b 7 + (-8)*repairCoverU b 8 + (-4)*repairCoverU b 9 + (-2)*repairCoverU b 10 + (2)*repairCoverU b 12
  | 2 => (-4)*repairCoverU b 0 + (4)*repairCoverU b 1 + (8)*repairCoverU b 5 + (-4)*repairCoverU b 7 + (-8)*repairCoverU b 8 + (4)*repairCoverU b 9 + (-4)*repairCoverU b 10 + (-4)*repairCoverU b 11 + (-4)*repairCoverU b 12
  | 3 => (6)*repairCoverU b 0 + (-4)*repairCoverU b 1 + (-2)*repairCoverU b 3 + (-1)*repairCoverU b 4 + (-7)*repairCoverU b 5 + (-2)*repairCoverU b 6 + (6)*repairCoverU b 7 + (8)*repairCoverU b 8 + (3)*repairCoverU b 10 + (2)*repairCoverU b 11 + (-1)*repairCoverU b 12
  | 4 => (-4)*repairCoverU b 3 + (2)*repairCoverU b 4 + (2)*repairCoverU b 5 + (-4)*repairCoverU b 6 + (4)*repairCoverU b 7 + (2)*repairCoverU b 10 + (-4)*repairCoverU b 11 + (-2)*repairCoverU b 12
  | 5 => (2)*repairCoverU b 0 + (-4)*repairCoverU b 1 + (4)*repairCoverU b 2 + (-2)*repairCoverU b 3 + (1)*repairCoverU b 4 + (3)*repairCoverU b 5 + (-2)*repairCoverU b 6 + (2)*repairCoverU b 7 + (4)*repairCoverU b 9 + (-3)*repairCoverU b 10 + (-2)*repairCoverU b 11 + (-3)*repairCoverU b 12
  | 6 => (-4)*repairCoverU b 2 + (4)*repairCoverU b 3 + (-2)*repairCoverU b 4 + (-6)*repairCoverU b 5 + (-4)*repairCoverU b 7 + (4)*repairCoverU b 8 + (-4)*repairCoverU b 9 + (2)*repairCoverU b 10 + (4)*repairCoverU b 11 + (2)*repairCoverU b 12
  | 7 => (-8)*repairCoverU b 0 + (-4)*repairCoverU b 1 + (8)*repairCoverU b 2 + (-8)*repairCoverU b 3 + (6)*repairCoverU b 4 + (6)*repairCoverU b 5 + (-8)*repairCoverU b 6 + (4)*repairCoverU b 7 + (-8)*repairCoverU b 8 + (-4)*repairCoverU b 9 + (2)*repairCoverU b 10 + (-4)*repairCoverU b 11 + (-2)*repairCoverU b 12
  | 8 => (-2)*repairCoverU b 0 + (4)*repairCoverU b 1 + (2)*repairCoverU b 3 + (-1)*repairCoverU b 4 + (5)*repairCoverU b 5 + (2)*repairCoverU b 6 + (-2)*repairCoverU b 7 + (-4)*repairCoverU b 8 + (4)*repairCoverU b 9 + (-5)*repairCoverU b 10 + (-6)*repairCoverU b 11 + (-5)*repairCoverU b 12
  | 9 => (-4)*repairCoverU b 0 + (-4)*repairCoverU b 1 + (8)*repairCoverU b 2 + (-8)*repairCoverU b 3 + (8)*repairCoverU b 4 + (8)*repairCoverU b 5 + (-4)*repairCoverU b 6 + (4)*repairCoverU b 7 + (-8)*repairCoverU b 8 + (-4)*repairCoverU b 10 + (-4)*repairCoverU b 11 + (-4)*repairCoverU b 12
  | 10 => (10)*repairCoverU b 0 + (4)*repairCoverU b 1 + (-12)*repairCoverU b 2 + (10)*repairCoverU b 3 + (-11)*repairCoverU b 4 + (-13)*repairCoverU b 5 + (10)*repairCoverU b 6 + (-6)*repairCoverU b 7 + (12)*repairCoverU b 8 + (1)*repairCoverU b 10 + (6)*repairCoverU b 11 + (5)*repairCoverU b 12
  | 11 => (4)*repairCoverU b 0
  | 12 => (4)*repairCoverU b 1
  | 13 => (4)*repairCoverU b 2
  | 14 => (4)*repairCoverU b 3
  | 15 => (4)*repairCoverU b 4
  | 16 => (4)*repairCoverU b 5
  | 17 => (4)*repairCoverU b 6
  | 18 => (4)*repairCoverU b 7
  | 19 => (4)*repairCoverU b 8
  | 20 => (4)*repairCoverU b 9
  | 21 => (4)*repairCoverU b 10
  | 22 => (4)*repairCoverU b 11
  | 23 => (4)*repairCoverU b 12
  | _ => 0

def repairCoverOne (b : Nat) : Bool :=
  let r0 := repairCoverRow b 0
  let r1 := repairCoverRow b 1
  let r2 := repairCoverRow b 2
  let r3 := repairCoverRow b 3
  let r4 := repairCoverRow b 4
  let r5 := repairCoverRow b 5
  let r6 := repairCoverRow b 6
  let r7 := repairCoverRow b 7
  let r8 := repairCoverRow b 8
  let r9 := repairCoverRow b 9
  let r10 := repairCoverRow b 10
  let r11 := repairCoverRow b 11
  let r12 := repairCoverRow b 12
  let r13 := repairCoverRow b 13
  let r14 := repairCoverRow b 14
  let r15 := repairCoverRow b 15
  let r16 := repairCoverRow b 16
  let r17 := repairCoverRow b 17
  let r18 := repairCoverRow b 18
  let r19 := repairCoverRow b 19
  let r20 := repairCoverRow b 20
  let r21 := repairCoverRow b 21
  let r22 := repairCoverRow b 22
  let r23 := repairCoverRow b 23
  if (r0 == 4) && (((r0 == 4) || (r0 == -4)) && ((r1 == 4) || (r1 == -4)) && ((r2 == 4) || (r2 == -4)) && ((r3 == 4) || (r3 == -4)) && ((r4 == 4) || (r4 == -4)) && ((r5 == 4) || (r5 == -4)) && ((r6 == 4) || (r6 == -4)) && ((r7 == 4) || (r7 == -4)) && ((r8 == 4) || (r8 == -4)) && ((r9 == 4) || (r9 == -4)) && ((r10 == 4) || (r10 == -4)) && ((r11 == 4) || (r11 == -4)) && ((r12 == 4) || (r12 == -4)) && ((r13 == 4) || (r13 == -4)) && ((r14 == 4) || (r14 == -4)) && ((r15 == 4) || (r15 == -4)) && ((r16 == 4) || (r16 == -4)) && ((r17 == 4) || (r17 == -4)) && ((r18 == 4) || (r18 == -4)) && ((r19 == 4) || (r19 == -4)) && ((r20 == 4) || (r20 == -4)) && ((r21 == 4) || (r21 == -4)) && ((r22 == 4) || (r22 == -4)) && ((r23 == 4) || (r23 == -4))) then
    ((r0 == 4) && (r1 == 4) && (r2 == -4) && (r3 == -4) && (r4 == -4) && (r5 == -4) && (r6 == -4) && (r7 == 4) && (r8 == -4) && (r9 == 4) && (r10 == -4) && (r11 == -4) && (r12 == 4) && (r13 == 4) && (r14 == -4) && (r15 == -4) && (r16 == 4) && (r17 == 4) && (r18 == 4) && (r19 == 4) && (r20 == -4) && (r21 == -4) && (r22 == 4) && (r23 == 4)) ||
    ((r0 == 4) && (r1 == 4) && (r2 == -4) && (r3 == -4) && (r4 == -4) && (r5 == -4) && (r6 == 4) && (r7 == 4) && (r8 == -4) && (r9 == -4) && (r10 == -4) && (r11 == -4) && (r12 == 4) && (r13 == 4) && (r14 == 4) && (r15 == -4) && (r16 == 4) && (r17 == -4) && (r18 == 4) && (r19 == 4) && (r20 == -4) && (r21 == -4) && (r22 == 4) && (r23 == 4)) ||
    ((r0 == 4) && (r1 == 4) && (r2 == 4) && (r3 == -4) && (r4 == 4) && (r5 == -4) && (r6 == -4) && (r7 == 4) && (r8 == -4) && (r9 == 4) && (r10 == -4) && (r11 == 4) && (r12 == 4) && (r13 == -4) && (r14 == -4) && (r15 == -4) && (r16 == 4) && (r17 == -4) && (r18 == 4) && (r19 == -4) && (r20 == -4) && (r21 == -4) && (r22 == 4) && (r23 == 4)) ||
    ((r0 == 4) && (r1 == 4) && (r2 == 4) && (r3 == -4) && (r4 == 4) && (r5 == -4) && (r6 == 4) && (r7 == -4) && (r8 == 4) && (r9 == -4) && (r10 == 4) && (r11 == -4) && (r12 == 4) && (r13 == -4) && (r14 == -4) && (r15 == 4) && (r16 == -4) && (r17 == -4) && (r18 == -4) && (r19 == 4) && (r20 == 4) && (r21 == -4) && (r22 == -4) && (r23 == 4)) ||
    ((r0 == 4) && (r1 == 4) && (r2 == -4) && (r3 == 4) && (r4 == 4) && (r5 == 4) && (r6 == 4) && (r7 == 4) && (r8 == -4) && (r9 == 4) && (r10 == -4) && (r11 == -4) && (r12 == -4) && (r13 == -4) && (r14 == -4) && (r15 == 4) && (r16 == -4) && (r17 == -4) && (r18 == -4) && (r19 == 4) && (r20 == 4) && (r21 == -4) && (r22 == -4) && (r23 == 4)) ||
    ((r0 == 4) && (r1 == -4) && (r2 == -4) && (r3 == 4) && (r4 == -4) && (r5 == -4) && (r6 == 4) && (r7 == -4) && (r8 == -4) && (r9 == -4) && (r10 == 4) && (r11 == -4) && (r12 == 4) && (r13 == 4) && (r14 == -4) && (r15 == 4) && (r16 == -4) && (r17 == 4) && (r18 == -4) && (r19 == 4) && (r20 == 4) && (r21 == 4) && (r22 == 4) && (r23 == -4)) ||
    ((r0 == 4) && (r1 == -4) && (r2 == 4) && (r3 == 4) && (r4 == 4) && (r5 == 4) && (r6 == 4) && (r7 == 4) && (r8 == -4) && (r9 == -4) && (r10 == -4) && (r11 == -4) && (r12 == -4) && (r13 == -4) && (r14 == -4) && (r15 == -4) && (r16 == 4) && (r17 == -4) && (r18 == -4) && (r19 == 4) && (r20 == 4) && (r21 == 4) && (r22 == 4) && (r23 == -4)) ||
    ((r0 == 4) && (r1 == 4) && (r2 == -4) && (r3 == 4) && (r4 == -4) && (r5 == -4) && (r6 == 4) && (r7 == -4) && (r8 == -4) && (r9 == -4) && (r10 == 4) && (r11 == -4) && (r12 == -4) && (r13 == -4) && (r14 == 4) && (r15 == 4) && (r16 == -4) && (r17 == 4) && (r18 == 4) && (r19 == -4) && (r20 == 4) && (r21 == 4) && (r22 == 4) && (r23 == -4)) ||
    ((r0 == 4) && (r1 == -4) && (r2 == 4) && (r3 == 4) && (r4 == 4) && (r5 == -4) && (r6 == 4) && (r7 == -4) && (r8 == -4) && (r9 == -4) && (r10 == 4) && (r11 == 4) && (r12 == 4) && (r13 == -4) && (r14 == -4) && (r15 == 4) && (r16 == -4) && (r17 == -4) && (r18 == -4) && (r19 == -4) && (r20 == 4) && (r21 == 4) && (r22 == 4) && (r23 == -4)) ||
    ((r0 == 4) && (r1 == -4) && (r2 == 4) && (r3 == 4) && (r4 == -4) && (r5 == 4) && (r6 == 4) && (r7 == -4) && (r8 == 4) && (r9 == -4) && (r10 == 4) && (r11 == -4) && (r12 == 4) && (r13 == 4) && (r14 == -4) && (r15 == -4) && (r16 == -4) && (r17 == -4) && (r18 == -4) && (r19 == 4) && (r20 == 4) && (r21 == -4) && (r22 == 4) && (r23 == -4)) ||
    ((r0 == 4) && (r1 == 4) && (r2 == 4) && (r3 == 4) && (r4 == -4) && (r5 == 4) && (r6 == -4) && (r7 == -4) && (r8 == 4) && (r9 == 4) && (r10 == 4) && (r11 == -4) && (r12 == -4) && (r13 == -4) && (r14 == -4) && (r15 == -4) && (r16 == -4) && (r17 == 4) && (r18 == 4) && (r19 == -4) && (r20 == 4) && (r21 == -4) && (r22 == 4) && (r23 == -4)) ||
    ((r0 == 4) && (r1 == 4) && (r2 == 4) && (r3 == 4) && (r4 == -4) && (r5 == 4) && (r6 == 4) && (r7 == -4) && (r8 == 4) && (r9 == -4) && (r10 == 4) && (r11 == -4) && (r12 == -4) && (r13 == -4) && (r14 == 4) && (r15 == -4) && (r16 == -4) && (r17 == -4) && (r18 == 4) && (r19 == -4) && (r20 == 4) && (r21 == -4) && (r22 == 4) && (r23 == -4)) ||
    ((r0 == 4) && (r1 == 4) && (r2 == 4) && (r3 == -4) && (r4 == 4) && (r5 == -4) && (r6 == 4) && (r7 == 4) && (r8 == 4) && (r9 == -4) && (r10 == 4) && (r11 == -4) && (r12 == -4) && (r13 == -4) && (r14 == -4) && (r15 == -4) && (r16 == 4) && (r17 == 4) && (r18 == -4) && (r19 == 4) && (r20 == -4) && (r21 == 4) && (r22 == -4) && (r23 == -4)) ||
    ((r0 == 4) && (r1 == 4) && (r2 == -4) && (r3 == 4) && (r4 == 4) && (r5 == -4) && (r6 == 4) && (r7 == 4) && (r8 == -4) && (r9 == 4) && (r10 == 4) && (r11 == 4) && (r12 == -4) && (r13 == -4) && (r14 == -4) && (r15 == 4) && (r16 == -4) && (r17 == 4) && (r18 == -4) && (r19 == -4) && (r20 == -4) && (r21 == 4) && (r22 == -4) && (r23 == -4)) ||
    ((r0 == 4) && (r1 == 4) && (r2 == -4) && (r3 == 4) && (r4 == -4) && (r5 == 4) && (r6 == 4) && (r7 == 4) && (r8 == 4) && (r9 == 4) && (r10 == 4) && (r11 == -4) && (r12 == -4) && (r13 == 4) && (r14 == -4) && (r15 == -4) && (r16 == -4) && (r17 == 4) && (r18 == -4) && (r19 == 4) && (r20 == -4) && (r21 == -4) && (r22 == -4) && (r23 == -4)) ||
    ((r0 == 4) && (r1 == 4) && (r2 == 4) && (r3 == 4) && (r4 == 4) && (r5 == 4) && (r6 == 4) && (r7 == 4) && (r8 == 4) && (r9 == 4) && (r10 == 4) && (r11 == 4) && (r12 == -4) && (r13 == -4) && (r14 == -4) && (r15 == -4) && (r16 == -4) && (r17 == -4) && (r18 == -4) && (r19 == -4) && (r20 == -4) && (r21 == -4) && (r22 == -4) && (r23 == -4))
  else true

def repairCoverBatch (start : Nat) : Nat → Bool
  | 0 => true
  | k+1 => repairCoverOne (start+k) && repairCoverBatch start k
end CompletionTheory
