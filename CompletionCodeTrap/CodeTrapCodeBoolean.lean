/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Lean.Elab.Tactic.Decide
@[expose] public section
set_option maxRecDepth 20000
namespace CompletionTheory

def trapCodeDigitSign (b j : Nat) : Int :=
  if j=0 then 1 else if b.testBit (j-1) then -1 else 1

def trapCodewordEntry (d b i : Nat) : Int :=
  match d with
  | 0 => (match i with
    | 0 => (1)*trapCodeDigitSign b 0
    | 1 => (1)*trapCodeDigitSign b 1
    | 2 => (1)*trapCodeDigitSign b 2
    | 3 => (1)*trapCodeDigitSign b 3
    | 4 => (1)*trapCodeDigitSign b 4
    | 5 => (1)*trapCodeDigitSign b 5
    | 6 => (1)*trapCodeDigitSign b 6
    | 7 => (1)*trapCodeDigitSign b 7
    | 8 => (1)*trapCodeDigitSign b 8
    | 9 => (1)*trapCodeDigitSign b 9
    | 10 => (3)*trapCodeDigitSign b 0 + (4)*trapCodeDigitSign b 1 + (1)*trapCodeDigitSign b 2 + (2)*trapCodeDigitSign b 3 + (1)*trapCodeDigitSign b 4 + (2)*trapCodeDigitSign b 6 + (3)*trapCodeDigitSign b 9
    | 11 => (2)*trapCodeDigitSign b 0 + (3)*trapCodeDigitSign b 1 + (2)*trapCodeDigitSign b 2 + (4)*trapCodeDigitSign b 3 + (2)*trapCodeDigitSign b 4 + (3)*trapCodeDigitSign b 5 + (2)*trapCodeDigitSign b 6 + (2)*trapCodeDigitSign b 7 + (4)*trapCodeDigitSign b 8 + (2)*trapCodeDigitSign b 9
    | 12 => (2)*trapCodeDigitSign b 0 + (3)*trapCodeDigitSign b 2 + (4)*trapCodeDigitSign b 3 + (3)*trapCodeDigitSign b 5 + (2)*trapCodeDigitSign b 7 + (1)*trapCodeDigitSign b 8 + (1)*trapCodeDigitSign b 9
    | 13 => (4)*trapCodeDigitSign b 0 + (1)*trapCodeDigitSign b 1 + (3)*trapCodeDigitSign b 4 + (1)*trapCodeDigitSign b 5 + (2)*trapCodeDigitSign b 7 + (3)*trapCodeDigitSign b 8 + (2)*trapCodeDigitSign b 9
    | 14 => (4)*trapCodeDigitSign b 0 + (3)*trapCodeDigitSign b 2 + (2)*trapCodeDigitSign b 3 + (3)*trapCodeDigitSign b 4 + (1)*trapCodeDigitSign b 7 + (2)*trapCodeDigitSign b 8 + (1)*trapCodeDigitSign b 9
    | 15 => (1)*trapCodeDigitSign b 1 + (1)*trapCodeDigitSign b 2 + (4)*trapCodeDigitSign b 3 + (4)*trapCodeDigitSign b 4 + (1)*trapCodeDigitSign b 6 + (1)*trapCodeDigitSign b 7 + (2)*trapCodeDigitSign b 8 + (2)*trapCodeDigitSign b 9
    | 16 => (4)*trapCodeDigitSign b 1 + (1)*trapCodeDigitSign b 2 + (2)*trapCodeDigitSign b 3 + (2)*trapCodeDigitSign b 4 + (4)*trapCodeDigitSign b 5 + (4)*trapCodeDigitSign b 6 + (3)*trapCodeDigitSign b 7 + (3)*trapCodeDigitSign b 8 + (3)*trapCodeDigitSign b 9
    | 17 => (1)*trapCodeDigitSign b 0 + (1)*trapCodeDigitSign b 3 + (4)*trapCodeDigitSign b 4 + (2)*trapCodeDigitSign b 5 + (3)*trapCodeDigitSign b 6 + (3)*trapCodeDigitSign b 7 + (2)*trapCodeDigitSign b 8
    | 18 => (3)*trapCodeDigitSign b 0 + (1)*trapCodeDigitSign b 1 + (3)*trapCodeDigitSign b 3 + (4)*trapCodeDigitSign b 5 + (4)*trapCodeDigitSign b 6 + (4)*trapCodeDigitSign b 7 + (1)*trapCodeDigitSign b 8 + (1)*trapCodeDigitSign b 9
    | 19 => (3)*trapCodeDigitSign b 2 + (2)*trapCodeDigitSign b 3 + (2)*trapCodeDigitSign b 5 + (3)*trapCodeDigitSign b 6 + (1)*trapCodeDigitSign b 7 + (1)*trapCodeDigitSign b 8 + (4)*trapCodeDigitSign b 9
    | _ => 0)%5
  | 1 => (match i with
    | 0 => (1)*trapCodeDigitSign b 0
    | 1 => (1)*trapCodeDigitSign b 1
    | 2 => (1)*trapCodeDigitSign b 2
    | 3 => (1)*trapCodeDigitSign b 3
    | 4 => (1)*trapCodeDigitSign b 4
    | 5 => (1)*trapCodeDigitSign b 5
    | 6 => (1)*trapCodeDigitSign b 6
    | 7 => (1)*trapCodeDigitSign b 7
    | 8 => (1)*trapCodeDigitSign b 8
    | 9 => (3)*trapCodeDigitSign b 0 + (3)*trapCodeDigitSign b 1 + (3)*trapCodeDigitSign b 2 + (4)*trapCodeDigitSign b 3 + (1)*trapCodeDigitSign b 4 + (3)*trapCodeDigitSign b 5 + (4)*trapCodeDigitSign b 8
    | 10 => (2)*trapCodeDigitSign b 0 + (3)*trapCodeDigitSign b 1 + (4)*trapCodeDigitSign b 3 + (4)*trapCodeDigitSign b 4 + (4)*trapCodeDigitSign b 5 + (2)*trapCodeDigitSign b 6 + (2)*trapCodeDigitSign b 8
    | 11 => (1)*trapCodeDigitSign b 9
    | 12 => (3)*trapCodeDigitSign b 0 + (2)*trapCodeDigitSign b 1 + (4)*trapCodeDigitSign b 2 + (2)*trapCodeDigitSign b 6 + (4)*trapCodeDigitSign b 7 + (2)*trapCodeDigitSign b 8 + (4)*trapCodeDigitSign b 9
    | 13 => (1)*trapCodeDigitSign b 0 + (2)*trapCodeDigitSign b 2 + (2)*trapCodeDigitSign b 3 + (3)*trapCodeDigitSign b 4 + (4)*trapCodeDigitSign b 6 + (1)*trapCodeDigitSign b 7 + (3)*trapCodeDigitSign b 9
    | 14 => (1)*trapCodeDigitSign b 0 + (2)*trapCodeDigitSign b 3 + (1)*trapCodeDigitSign b 4 + (1)*trapCodeDigitSign b 6 + (2)*trapCodeDigitSign b 7 + (2)*trapCodeDigitSign b 8 + (2)*trapCodeDigitSign b 9
    | 15 => (3)*trapCodeDigitSign b 0 + (3)*trapCodeDigitSign b 1 + (4)*trapCodeDigitSign b 2 + (2)*trapCodeDigitSign b 4 + (2)*trapCodeDigitSign b 5 + (4)*trapCodeDigitSign b 6 + (4)*trapCodeDigitSign b 7 + (3)*trapCodeDigitSign b 8 + (1)*trapCodeDigitSign b 9
    | 16 => (1)*trapCodeDigitSign b 1 + (1)*trapCodeDigitSign b 2 + (3)*trapCodeDigitSign b 3 + (3)*trapCodeDigitSign b 4 + (1)*trapCodeDigitSign b 5 + (3)*trapCodeDigitSign b 6 + (2)*trapCodeDigitSign b 7 + (4)*trapCodeDigitSign b 8 + (3)*trapCodeDigitSign b 9
    | 17 => (1)*trapCodeDigitSign b 0 + (1)*trapCodeDigitSign b 3 + (4)*trapCodeDigitSign b 4 + (2)*trapCodeDigitSign b 5 + (3)*trapCodeDigitSign b 6 + (3)*trapCodeDigitSign b 7 + (2)*trapCodeDigitSign b 8
    | 18 => (1)*trapCodeDigitSign b 1 + (2)*trapCodeDigitSign b 2 + (3)*trapCodeDigitSign b 3 + (3)*trapCodeDigitSign b 4 + (4)*trapCodeDigitSign b 5 + (1)*trapCodeDigitSign b 8 + (2)*trapCodeDigitSign b 9
    | 19 => (1)*trapCodeDigitSign b 1 + (3)*trapCodeDigitSign b 2 + (3)*trapCodeDigitSign b 4 + (3)*trapCodeDigitSign b 5 + (3)*trapCodeDigitSign b 7 + (4)*trapCodeDigitSign b 8 + (4)*trapCodeDigitSign b 9
    | _ => 0)%5
  | _ => 0

def trapCodeClassOne (d b : Nat) : Bool :=
  let r0 := trapCodewordEntry d b 0
  let r1 := trapCodewordEntry d b 1
  let r2 := trapCodewordEntry d b 2
  let r3 := trapCodewordEntry d b 3
  let r4 := trapCodewordEntry d b 4
  let r5 := trapCodewordEntry d b 5
  let r6 := trapCodewordEntry d b 6
  let r7 := trapCodewordEntry d b 7
  let r8 := trapCodewordEntry d b 8
  let r9 := trapCodewordEntry d b 9
  let r10 := trapCodewordEntry d b 10
  let r11 := trapCodewordEntry d b 11
  let r12 := trapCodewordEntry d b 12
  let r13 := trapCodewordEntry d b 13
  let r14 := trapCodewordEntry d b 14
  let r15 := trapCodewordEntry d b 15
  let r16 := trapCodewordEntry d b 16
  let r17 := trapCodewordEntry d b 17
  let r18 := trapCodewordEntry d b 18
  let r19 := trapCodewordEntry d b 19
  if ((r0 == 1) || (r0 == 4)) && ((r1 == 1) || (r1 == 4)) && ((r2 == 1) || (r2 == 4)) && ((r3 == 1) || (r3 == 4)) && ((r4 == 1) || (r4 == 4)) && ((r5 == 1) || (r5 == 4)) && ((r6 == 1) || (r6 == 4)) && ((r7 == 1) || (r7 == 4)) && ((r8 == 1) || (r8 == 4)) && ((r9 == 1) || (r9 == 4)) && ((r10 == 1) || (r10 == 4)) && ((r11 == 1) || (r11 == 4)) && ((r12 == 1) || (r12 == 4)) && ((r13 == 1) || (r13 == 4)) && ((r14 == 1) || (r14 == 4)) && ((r15 == 1) || (r15 == 4)) && ((r16 == 1) || (r16 == 4)) && ((r17 == 1) || (r17 == 4)) && ((r18 == 1) || (r18 == 4)) && ((r19 == 1) || (r19 == 4)) then
    match d with
    | 0 => ((r0 == 1) && (r1 == 1) && (r2 == 1) && (r3 == 1) && (r4 == 1) && (r5 == 1) && (r6 == 1) && (r7 == 1) && (r8 == 1) && (r9 == 1) && (r10 == 1) && (r11 == 1) && (r12 == 1) && (r13 == 1) && (r14 == 1) && (r15 == 1) && (r16 == 1) && (r17 == 1) && (r18 == 1) && (r19 == 1)) ||
      ((r0 == 1) && (r1 == 4) && (r2 == 4) && (r3 == 1) && (r4 == 4) && (r5 == 4) && (r6 == 1) && (r7 == 1) && (r8 == 1) && (r9 == 1) && (r10 == 4) && (r11 == 1) && (r12 == 4) && (r13 == 1) && (r14 == 4) && (r15 == 4) && (r16 == 4) && (r17 == 4) && (r18 == 1) && (r19 == 1)) ||
      ((r0 == 1) && (r1 == 1) && (r2 == 4) && (r3 == 4) && (r4 == 1) && (r5 == 4) && (r6 == 4) && (r7 == 1) && (r8 == 1) && (r9 == 1) && (r10 == 1) && (r11 == 4) && (r12 == 1) && (r13 == 4) && (r14 == 1) && (r15 == 4) && (r16 == 4) && (r17 == 4) && (r18 == 4) && (r19 == 1)) ||
      ((r0 == 1) && (r1 == 1) && (r2 == 1) && (r3 == 4) && (r4 == 4) && (r5 == 1) && (r6 == 4) && (r7 == 4) && (r8 == 1) && (r9 == 1) && (r10 == 1) && (r11 == 1) && (r12 == 4) && (r13 == 1) && (r14 == 4) && (r15 == 1) && (r16 == 4) && (r17 == 4) && (r18 == 4) && (r19 == 4)) ||
      ((r0 == 1) && (r1 == 1) && (r2 == 1) && (r3 == 1) && (r4 == 4) && (r5 == 1) && (r6 == 1) && (r7 == 1) && (r8 == 4) && (r9 == 1) && (r10 == 4) && (r11 == 4) && (r12 == 4) && (r13 == 4) && (r14 == 1) && (r15 == 4) && (r16 == 1) && (r17 == 4) && (r18 == 4) && (r19 == 4)) ||
      ((r0 == 1) && (r1 == 4) && (r2 == 4) && (r3 == 1) && (r4 == 1) && (r5 == 1) && (r6 == 1) && (r7 == 4) && (r8 == 4) && (r9 == 1) && (r10 == 1) && (r11 == 4) && (r12 == 4) && (r13 == 4) && (r14 == 4) && (r15 == 1) && (r16 == 4) && (r17 == 1) && (r18 == 4) && (r19 == 1)) ||
      ((r0 == 1) && (r1 == 4) && (r2 == 1) && (r3 == 4) && (r4 == 4) && (r5 == 1) && (r6 == 1) && (r7 == 1) && (r8 == 1) && (r9 == 4) && (r10 == 1) && (r11 == 4) && (r12 == 1) && (r13 == 4) && (r14 == 4) && (r15 == 4) && (r16 == 4) && (r17 == 1) && (r18 == 1) && (r19 == 4)) ||
      ((r0 == 1) && (r1 == 4) && (r2 == 4) && (r3 == 1) && (r4 == 1) && (r5 == 1) && (r6 == 4) && (r7 == 4) && (r8 == 1) && (r9 == 4) && (r10 == 1) && (r11 == 4) && (r12 == 4) && (r13 == 1) && (r14 == 1) && (r15 == 4) && (r16 == 1) && (r17 == 4) && (r18 == 1) && (r19 == 4)) ||
      ((r0 == 1) && (r1 == 1) && (r2 == 4) && (r3 == 1) && (r4 == 1) && (r5 == 1) && (r6 == 4) && (r7 == 1) && (r8 == 4) && (r9 == 4) && (r10 == 4) && (r11 == 1) && (r12 == 1) && (r13 == 1) && (r14 == 4) && (r15 == 4) && (r16 == 4) && (r17 == 1) && (r18 == 4) && (r19 == 4)) ||
      ((r0 == 1) && (r1 == 4) && (r2 == 1) && (r3 == 4) && (r4 == 1) && (r5 == 1) && (r6 == 4) && (r7 == 1) && (r8 == 4) && (r9 == 4) && (r10 == 4) && (r11 == 1) && (r12 == 4) && (r13 == 4) && (r14 == 1) && (r15 == 1) && (r16 == 4) && (r17 == 4) && (r18 == 1) && (r19 == 1)) ||
      ((r0 == 1) && (r1 == 4) && (r2 == 1) && (r3 == 1) && (r4 == 4) && (r5 == 4) && (r6 == 4) && (r7 == 1) && (r8 == 4) && (r9 == 4) && (r10 == 1) && (r11 == 4) && (r12 == 1) && (r13 == 1) && (r14 == 4) && (r15 == 1) && (r16 == 1) && (r17 == 4) && (r18 == 4) && (r19 == 1)) ||
      ((r0 == 1) && (r1 == 1) && (r2 == 4) && (r3 == 1) && (r4 == 4) && (r5 == 4) && (r6 == 1) && (r7 == 4) && (r8 == 4) && (r9 == 4) && (r10 == 1) && (r11 == 1) && (r12 == 1) && (r13 == 4) && (r14 == 1) && (r15 == 1) && (r16 == 4) && (r17 == 4) && (r18 == 1) && (r19 == 4))
    | 1 => ((r0 == 1) && (r1 == 1) && (r2 == 1) && (r3 == 1) && (r4 == 1) && (r5 == 1) && (r6 == 1) && (r7 == 1) && (r8 == 1) && (r9 == 1) && (r10 == 1) && (r11 == 1) && (r12 == 1) && (r13 == 1) && (r14 == 1) && (r15 == 1) && (r16 == 1) && (r17 == 1) && (r18 == 1) && (r19 == 1)) ||
      ((r0 == 1) && (r1 == 4) && (r2 == 4) && (r3 == 1) && (r4 == 4) && (r5 == 4) && (r6 == 1) && (r7 == 1) && (r8 == 1) && (r9 == 1) && (r10 == 4) && (r11 == 1) && (r12 == 4) && (r13 == 1) && (r14 == 4) && (r15 == 4) && (r16 == 4) && (r17 == 4) && (r18 == 1) && (r19 == 1)) ||
      ((r0 == 1) && (r1 == 1) && (r2 == 4) && (r3 == 1) && (r4 == 1) && (r5 == 4) && (r6 == 4) && (r7 == 1) && (r8 == 1) && (r9 == 4) && (r10 == 4) && (r11 == 1) && (r12 == 4) && (r13 == 4) && (r14 == 4) && (r15 == 1) && (r16 == 1) && (r17 == 1) && (r18 == 4) && (r19 == 4)) ||
      ((r0 == 1) && (r1 == 4) && (r2 == 1) && (r3 == 4) && (r4 == 4) && (r5 == 4) && (r6 == 1) && (r7 == 4) && (r8 == 1) && (r9 == 4) && (r10 == 1) && (r11 == 1) && (r12 == 4) && (r13 == 4) && (r14 == 1) && (r15 == 4) && (r16 == 1) && (r17 == 1) && (r18 == 4) && (r19 == 1)) ||
      ((r0 == 1) && (r1 == 1) && (r2 == 1) && (r3 == 4) && (r4 == 4) && (r5 == 1) && (r6 == 4) && (r7 == 4) && (r8 == 1) && (r9 == 1) && (r10 == 1) && (r11 == 1) && (r12 == 4) && (r13 == 1) && (r14 == 4) && (r15 == 1) && (r16 == 4) && (r17 == 4) && (r18 == 4) && (r19 == 4)) ||
      ((r0 == 1) && (r1 == 4) && (r2 == 1) && (r3 == 4) && (r4 == 1) && (r5 == 1) && (r6 == 4) && (r7 == 1) && (r8 == 4) && (r9 == 4) && (r10 == 4) && (r11 == 1) && (r12 == 4) && (r13 == 4) && (r14 == 1) && (r15 == 1) && (r16 == 4) && (r17 == 4) && (r18 == 1) && (r19 == 1)) ||
      ((r0 == 1) && (r1 == 4) && (r2 == 4) && (r3 == 4) && (r4 == 4) && (r5 == 1) && (r6 == 4) && (r7 == 1) && (r8 == 4) && (r9 == 1) && (r10 == 1) && (r11 == 1) && (r12 == 1) && (r13 == 4) && (r14 == 4) && (r15 == 4) && (r16 == 1) && (r17 == 1) && (r18 == 1) && (r19 == 4)) ||
      ((r0 == 1) && (r1 == 1) && (r2 == 4) && (r3 == 4) && (r4 == 1) && (r5 == 1) && (r6 == 1) && (r7 == 4) && (r8 == 4) && (r9 == 4) && (r10 == 4) && (r11 == 1) && (r12 == 1) && (r13 == 1) && (r14 == 4) && (r15 == 4) && (r16 == 1) && (r17 == 4) && (r18 == 4) && (r19 == 1)) ||
      ((r0 == 1) && (r1 == 1) && (r2 == 4) && (r3 == 1) && (r4 == 4) && (r5 == 4) && (r6 == 1) && (r7 == 4) && (r8 == 4) && (r9 == 4) && (r10 == 1) && (r11 == 1) && (r12 == 1) && (r13 == 4) && (r14 == 1) && (r15 == 1) && (r16 == 4) && (r17 == 4) && (r18 == 1) && (r19 == 4)) ||
      ((r0 == 1) && (r1 == 4) && (r2 == 1) && (r3 == 1) && (r4 == 1) && (r5 == 4) && (r6 == 4) && (r7 == 4) && (r8 == 4) && (r9 == 1) && (r10 == 4) && (r11 == 1) && (r12 == 1) && (r13 == 1) && (r14 == 1) && (r15 == 4) && (r16 == 4) && (r17 == 1) && (r18 == 4) && (r19 == 4)) ||
      ((r0 == 1) && (r1 == 4) && (r2 == 4) && (r3 == 4) && (r4 == 4) && (r5 == 1) && (r6 == 1) && (r7 == 1) && (r8 == 1) && (r9 == 4) && (r10 == 4) && (r11 == 4) && (r12 == 1) && (r13 == 1) && (r14 == 1) && (r15 == 1) && (r16 == 4) && (r17 == 1) && (r18 == 4) && (r19 == 4)) ||
      ((r0 == 1) && (r1 == 1) && (r2 == 4) && (r3 == 4) && (r4 == 1) && (r5 == 4) && (r6 == 4) && (r7 == 1) && (r8 == 1) && (r9 == 1) && (r10 == 1) && (r11 == 4) && (r12 == 1) && (r13 == 4) && (r14 == 1) && (r15 == 4) && (r16 == 4) && (r17 == 4) && (r18 == 4) && (r19 == 1)) ||
      ((r0 == 1) && (r1 == 4) && (r2 == 1) && (r3 == 4) && (r4 == 1) && (r5 == 4) && (r6 == 1) && (r7 == 4) && (r8 == 1) && (r9 == 1) && (r10 == 4) && (r11 == 4) && (r12 == 1) && (r13 == 4) && (r14 == 4) && (r15 == 1) && (r16 == 1) && (r17 == 4) && (r18 == 1) && (r19 == 4)) ||
      ((r0 == 1) && (r1 == 4) && (r2 == 4) && (r3 == 1) && (r4 == 1) && (r5 == 1) && (r6 == 4) && (r7 == 4) && (r8 == 1) && (r9 == 4) && (r10 == 1) && (r11 == 4) && (r12 == 4) && (r13 == 1) && (r14 == 1) && (r15 == 4) && (r16 == 1) && (r17 == 4) && (r18 == 1) && (r19 == 4)) ||
      ((r0 == 1) && (r1 == 1) && (r2 == 1) && (r3 == 1) && (r4 == 4) && (r5 == 1) && (r6 == 4) && (r7 == 4) && (r8 == 1) && (r9 == 4) && (r10 == 4) && (r11 == 4) && (r12 == 1) && (r13 == 4) && (r14 == 4) && (r15 == 4) && (r16 == 4) && (r17 == 1) && (r18 == 1) && (r19 == 1)) ||
      ((r0 == 1) && (r1 == 1) && (r2 == 1) && (r3 == 1) && (r4 == 4) && (r5 == 1) && (r6 == 1) && (r7 == 1) && (r8 == 4) && (r9 == 1) && (r10 == 4) && (r11 == 4) && (r12 == 4) && (r13 == 4) && (r14 == 1) && (r15 == 4) && (r16 == 1) && (r17 == 4) && (r18 == 4) && (r19 == 4)) ||
      ((r0 == 1) && (r1 == 1) && (r2 == 1) && (r3 == 4) && (r4 == 1) && (r5 == 4) && (r6 == 1) && (r7 == 1) && (r8 == 4) && (r9 == 4) && (r10 == 1) && (r11 == 4) && (r12 == 4) && (r13 == 1) && (r14 == 4) && (r15 == 4) && (r16 == 4) && (r17 == 1) && (r18 == 1) && (r19 == 4)) ||
      ((r0 == 1) && (r1 == 4) && (r2 == 1) && (r3 == 1) && (r4 == 4) && (r5 == 4) && (r6 == 4) && (r7 == 1) && (r8 == 4) && (r9 == 4) && (r10 == 1) && (r11 == 4) && (r12 == 1) && (r13 == 1) && (r14 == 4) && (r15 == 1) && (r16 == 1) && (r17 == 4) && (r18 == 4) && (r19 == 1)) ||
      ((r0 == 1) && (r1 == 4) && (r2 == 4) && (r3 == 1) && (r4 == 1) && (r5 == 1) && (r6 == 1) && (r7 == 4) && (r8 == 4) && (r9 == 1) && (r10 == 1) && (r11 == 4) && (r12 == 4) && (r13 == 4) && (r14 == 4) && (r15 == 1) && (r16 == 4) && (r17 == 1) && (r18 == 4) && (r19 == 1)) ||
      ((r0 == 1) && (r1 == 1) && (r2 == 4) && (r3 == 4) && (r4 == 4) && (r5 == 4) && (r6 == 4) && (r7 == 4) && (r8 == 4) && (r9 == 1) && (r10 == 4) && (r11 == 4) && (r12 == 4) && (r13 == 1) && (r14 == 1) && (r15 == 1) && (r16 == 1) && (r17 == 1) && (r18 == 1) && (r19 == 1))
    | _ => false
  else true

def trapCodeClassBatch (d start : Nat) : Nat → Bool
  | 0 => true
  | k+1 => trapCodeClassOne d (start+k) && trapCodeClassBatch d start k
end CompletionTheory
