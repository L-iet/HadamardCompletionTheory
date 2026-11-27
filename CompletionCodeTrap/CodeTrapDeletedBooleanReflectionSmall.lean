/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapRowEval_0
public import CompletionCodeTrap.CodeTrapRowEval_1
public import CompletionCodeTrap.CodeTrapRowEval_2
public import CompletionCodeTrap.CodeTrapRowEval_3
public import CompletionCodeTrap.CodeTrapRowEval_4
public import CompletionCodeTrap.CodeTrapRowEval_5
public import CompletionCodeTrap.CodeTrapRowEval_6
public import CompletionCodeTrap.CodeTrapRowEval_7
public import CompletionCodeTrap.CodeTrapRowEval_8
public import CompletionCodeTrap.CodeTrapRowEval_9
public import CompletionCodeTrap.CodeTrapRowEval_10
public import CompletionCodeTrap.CodeTrapRowEval_11
public import CompletionCodeTrap.CodeTrapDeletionComplete
public import Mathlib.Tactic.NormNum
@[expose] public section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
namespace CompletionTheory

theorem codeTrapDeleted_boolean_row (d : Fin 12) (b : Nat) (i : Fin 20) :
    (codeTrapDeletionBasis d).mulVec (fun j => codeTrapDeletionSign b j.val) i=
      codeTrapDeletionRow d.val b i.val := by
  fin_cases d <;> fin_cases i
  · exact codeTrapRowEval_0_0 b
  · exact codeTrapRowEval_0_1 b
  · exact codeTrapRowEval_0_2 b
  · exact codeTrapRowEval_0_3 b
  · exact codeTrapRowEval_0_4 b
  · exact codeTrapRowEval_0_5 b
  · exact codeTrapRowEval_0_6 b
  · exact codeTrapRowEval_0_7 b
  · exact codeTrapRowEval_0_8 b
  · exact codeTrapRowEval_0_9 b
  · exact codeTrapRowEval_0_10 b
  · exact codeTrapRowEval_0_11 b
  · exact codeTrapRowEval_0_12 b
  · exact codeTrapRowEval_0_13 b
  · exact codeTrapRowEval_0_14 b
  · exact codeTrapRowEval_0_15 b
  · exact codeTrapRowEval_0_16 b
  · exact codeTrapRowEval_0_17 b
  · exact codeTrapRowEval_0_18 b
  · exact codeTrapRowEval_0_19 b
  · exact codeTrapRowEval_1_0 b
  · exact codeTrapRowEval_1_1 b
  · exact codeTrapRowEval_1_2 b
  · exact codeTrapRowEval_1_3 b
  · exact codeTrapRowEval_1_4 b
  · exact codeTrapRowEval_1_5 b
  · exact codeTrapRowEval_1_6 b
  · exact codeTrapRowEval_1_7 b
  · exact codeTrapRowEval_1_8 b
  · exact codeTrapRowEval_1_9 b
  · exact codeTrapRowEval_1_10 b
  · exact codeTrapRowEval_1_11 b
  · exact codeTrapRowEval_1_12 b
  · exact codeTrapRowEval_1_13 b
  · exact codeTrapRowEval_1_14 b
  · exact codeTrapRowEval_1_15 b
  · exact codeTrapRowEval_1_16 b
  · exact codeTrapRowEval_1_17 b
  · exact codeTrapRowEval_1_18 b
  · exact codeTrapRowEval_1_19 b
  · exact codeTrapRowEval_2_0 b
  · exact codeTrapRowEval_2_1 b
  · exact codeTrapRowEval_2_2 b
  · exact codeTrapRowEval_2_3 b
  · exact codeTrapRowEval_2_4 b
  · exact codeTrapRowEval_2_5 b
  · exact codeTrapRowEval_2_6 b
  · exact codeTrapRowEval_2_7 b
  · exact codeTrapRowEval_2_8 b
  · exact codeTrapRowEval_2_9 b
  · exact codeTrapRowEval_2_10 b
  · exact codeTrapRowEval_2_11 b
  · exact codeTrapRowEval_2_12 b
  · exact codeTrapRowEval_2_13 b
  · exact codeTrapRowEval_2_14 b
  · exact codeTrapRowEval_2_15 b
  · exact codeTrapRowEval_2_16 b
  · exact codeTrapRowEval_2_17 b
  · exact codeTrapRowEval_2_18 b
  · exact codeTrapRowEval_2_19 b
  · exact codeTrapRowEval_3_0 b
  · exact codeTrapRowEval_3_1 b
  · exact codeTrapRowEval_3_2 b
  · exact codeTrapRowEval_3_3 b
  · exact codeTrapRowEval_3_4 b
  · exact codeTrapRowEval_3_5 b
  · exact codeTrapRowEval_3_6 b
  · exact codeTrapRowEval_3_7 b
  · exact codeTrapRowEval_3_8 b
  · exact codeTrapRowEval_3_9 b
  · exact codeTrapRowEval_3_10 b
  · exact codeTrapRowEval_3_11 b
  · exact codeTrapRowEval_3_12 b
  · exact codeTrapRowEval_3_13 b
  · exact codeTrapRowEval_3_14 b
  · exact codeTrapRowEval_3_15 b
  · exact codeTrapRowEval_3_16 b
  · exact codeTrapRowEval_3_17 b
  · exact codeTrapRowEval_3_18 b
  · exact codeTrapRowEval_3_19 b
  · exact codeTrapRowEval_4_0 b
  · exact codeTrapRowEval_4_1 b
  · exact codeTrapRowEval_4_2 b
  · exact codeTrapRowEval_4_3 b
  · exact codeTrapRowEval_4_4 b
  · exact codeTrapRowEval_4_5 b
  · exact codeTrapRowEval_4_6 b
  · exact codeTrapRowEval_4_7 b
  · exact codeTrapRowEval_4_8 b
  · exact codeTrapRowEval_4_9 b
  · exact codeTrapRowEval_4_10 b
  · exact codeTrapRowEval_4_11 b
  · exact codeTrapRowEval_4_12 b
  · exact codeTrapRowEval_4_13 b
  · exact codeTrapRowEval_4_14 b
  · exact codeTrapRowEval_4_15 b
  · exact codeTrapRowEval_4_16 b
  · exact codeTrapRowEval_4_17 b
  · exact codeTrapRowEval_4_18 b
  · exact codeTrapRowEval_4_19 b
  · exact codeTrapRowEval_5_0 b
  · exact codeTrapRowEval_5_1 b
  · exact codeTrapRowEval_5_2 b
  · exact codeTrapRowEval_5_3 b
  · exact codeTrapRowEval_5_4 b
  · exact codeTrapRowEval_5_5 b
  · exact codeTrapRowEval_5_6 b
  · exact codeTrapRowEval_5_7 b
  · exact codeTrapRowEval_5_8 b
  · exact codeTrapRowEval_5_9 b
  · exact codeTrapRowEval_5_10 b
  · exact codeTrapRowEval_5_11 b
  · exact codeTrapRowEval_5_12 b
  · exact codeTrapRowEval_5_13 b
  · exact codeTrapRowEval_5_14 b
  · exact codeTrapRowEval_5_15 b
  · exact codeTrapRowEval_5_16 b
  · exact codeTrapRowEval_5_17 b
  · exact codeTrapRowEval_5_18 b
  · exact codeTrapRowEval_5_19 b
  · exact codeTrapRowEval_6_0 b
  · exact codeTrapRowEval_6_1 b
  · exact codeTrapRowEval_6_2 b
  · exact codeTrapRowEval_6_3 b
  · exact codeTrapRowEval_6_4 b
  · exact codeTrapRowEval_6_5 b
  · exact codeTrapRowEval_6_6 b
  · exact codeTrapRowEval_6_7 b
  · exact codeTrapRowEval_6_8 b
  · exact codeTrapRowEval_6_9 b
  · exact codeTrapRowEval_6_10 b
  · exact codeTrapRowEval_6_11 b
  · exact codeTrapRowEval_6_12 b
  · exact codeTrapRowEval_6_13 b
  · exact codeTrapRowEval_6_14 b
  · exact codeTrapRowEval_6_15 b
  · exact codeTrapRowEval_6_16 b
  · exact codeTrapRowEval_6_17 b
  · exact codeTrapRowEval_6_18 b
  · exact codeTrapRowEval_6_19 b
  · exact codeTrapRowEval_7_0 b
  · exact codeTrapRowEval_7_1 b
  · exact codeTrapRowEval_7_2 b
  · exact codeTrapRowEval_7_3 b
  · exact codeTrapRowEval_7_4 b
  · exact codeTrapRowEval_7_5 b
  · exact codeTrapRowEval_7_6 b
  · exact codeTrapRowEval_7_7 b
  · exact codeTrapRowEval_7_8 b
  · exact codeTrapRowEval_7_9 b
  · exact codeTrapRowEval_7_10 b
  · exact codeTrapRowEval_7_11 b
  · exact codeTrapRowEval_7_12 b
  · exact codeTrapRowEval_7_13 b
  · exact codeTrapRowEval_7_14 b
  · exact codeTrapRowEval_7_15 b
  · exact codeTrapRowEval_7_16 b
  · exact codeTrapRowEval_7_17 b
  · exact codeTrapRowEval_7_18 b
  · exact codeTrapRowEval_7_19 b
  · exact codeTrapRowEval_8_0 b
  · exact codeTrapRowEval_8_1 b
  · exact codeTrapRowEval_8_2 b
  · exact codeTrapRowEval_8_3 b
  · exact codeTrapRowEval_8_4 b
  · exact codeTrapRowEval_8_5 b
  · exact codeTrapRowEval_8_6 b
  · exact codeTrapRowEval_8_7 b
  · exact codeTrapRowEval_8_8 b
  · exact codeTrapRowEval_8_9 b
  · exact codeTrapRowEval_8_10 b
  · exact codeTrapRowEval_8_11 b
  · exact codeTrapRowEval_8_12 b
  · exact codeTrapRowEval_8_13 b
  · exact codeTrapRowEval_8_14 b
  · exact codeTrapRowEval_8_15 b
  · exact codeTrapRowEval_8_16 b
  · exact codeTrapRowEval_8_17 b
  · exact codeTrapRowEval_8_18 b
  · exact codeTrapRowEval_8_19 b
  · exact codeTrapRowEval_9_0 b
  · exact codeTrapRowEval_9_1 b
  · exact codeTrapRowEval_9_2 b
  · exact codeTrapRowEval_9_3 b
  · exact codeTrapRowEval_9_4 b
  · exact codeTrapRowEval_9_5 b
  · exact codeTrapRowEval_9_6 b
  · exact codeTrapRowEval_9_7 b
  · exact codeTrapRowEval_9_8 b
  · exact codeTrapRowEval_9_9 b
  · exact codeTrapRowEval_9_10 b
  · exact codeTrapRowEval_9_11 b
  · exact codeTrapRowEval_9_12 b
  · exact codeTrapRowEval_9_13 b
  · exact codeTrapRowEval_9_14 b
  · exact codeTrapRowEval_9_15 b
  · exact codeTrapRowEval_9_16 b
  · exact codeTrapRowEval_9_17 b
  · exact codeTrapRowEval_9_18 b
  · exact codeTrapRowEval_9_19 b
  · exact codeTrapRowEval_10_0 b
  · exact codeTrapRowEval_10_1 b
  · exact codeTrapRowEval_10_2 b
  · exact codeTrapRowEval_10_3 b
  · exact codeTrapRowEval_10_4 b
  · exact codeTrapRowEval_10_5 b
  · exact codeTrapRowEval_10_6 b
  · exact codeTrapRowEval_10_7 b
  · exact codeTrapRowEval_10_8 b
  · exact codeTrapRowEval_10_9 b
  · exact codeTrapRowEval_10_10 b
  · exact codeTrapRowEval_10_11 b
  · exact codeTrapRowEval_10_12 b
  · exact codeTrapRowEval_10_13 b
  · exact codeTrapRowEval_10_14 b
  · exact codeTrapRowEval_10_15 b
  · exact codeTrapRowEval_10_16 b
  · exact codeTrapRowEval_10_17 b
  · exact codeTrapRowEval_10_18 b
  · exact codeTrapRowEval_10_19 b
  · exact codeTrapRowEval_11_0 b
  · exact codeTrapRowEval_11_1 b
  · exact codeTrapRowEval_11_2 b
  · exact codeTrapRowEval_11_3 b
  · exact codeTrapRowEval_11_4 b
  · exact codeTrapRowEval_11_5 b
  · exact codeTrapRowEval_11_6 b
  · exact codeTrapRowEval_11_7 b
  · exact codeTrapRowEval_11_8 b
  · exact codeTrapRowEval_11_9 b
  · exact codeTrapRowEval_11_10 b
  · exact codeTrapRowEval_11_11 b
  · exact codeTrapRowEval_11_12 b
  · exact codeTrapRowEval_11_13 b
  · exact codeTrapRowEval_11_14 b
  · exact codeTrapRowEval_11_15 b
  · exact codeTrapRowEval_11_16 b
  · exact codeTrapRowEval_11_17 b
  · exact codeTrapRowEval_11_18 b
  · exact codeTrapRowEval_11_19 b

theorem codeTrapDeletionDenom_nonzero : ∀ d : Fin 12,codeTrapDeletionDenom d.val≠0 := by
  decide +kernel

theorem codeTrapDeleted_boolean_cover (d : Fin 12) (b : Fin 512)
    (hsign : ∀ i : Fin 20,codeTrapDeletionRow d.val b.val i.val=codeTrapDeletionDenom d.val ∨
      codeTrapDeletionRow d.val b.val i.val= -codeTrapDeletionDenom d.val) :
    (∀ i : Fin 20,codeTrapDeletionRow d.val b.val i.val=
      codeTrapDeletionDenom d.val*codeTrapOldIntegerMatrix d i) ∨
    (∀ i : Fin 20,codeTrapDeletionRow d.val b.val i.val=
      -(codeTrapDeletionDenom d.val*codeTrapOldIntegerMatrix d i)) := by
  have ha : ∀ i : Fin 20,((codeTrapDeletionRow d.val b.val i.val == codeTrapDeletionDenom d.val) ||
      (codeTrapDeletionRow d.val b.val i.val == -codeTrapDeletionDenom d.val))=true := by
    intro i
    rcases hsign i with h|h <;> simp [h]
  have ha0 : ((codeTrapDeletionRow d.val b.val 0 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 0 == -codeTrapDeletionDenom d.val))=true := ha 0
  have ha1 : ((codeTrapDeletionRow d.val b.val 1 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 1 == -codeTrapDeletionDenom d.val))=true := ha 1
  have ha2 : ((codeTrapDeletionRow d.val b.val 2 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 2 == -codeTrapDeletionDenom d.val))=true := ha 2
  have ha3 : ((codeTrapDeletionRow d.val b.val 3 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 3 == -codeTrapDeletionDenom d.val))=true := ha 3
  have ha4 : ((codeTrapDeletionRow d.val b.val 4 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 4 == -codeTrapDeletionDenom d.val))=true := ha 4
  have ha5 : ((codeTrapDeletionRow d.val b.val 5 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 5 == -codeTrapDeletionDenom d.val))=true := ha 5
  have ha6 : ((codeTrapDeletionRow d.val b.val 6 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 6 == -codeTrapDeletionDenom d.val))=true := ha 6
  have ha7 : ((codeTrapDeletionRow d.val b.val 7 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 7 == -codeTrapDeletionDenom d.val))=true := ha 7
  have ha8 : ((codeTrapDeletionRow d.val b.val 8 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 8 == -codeTrapDeletionDenom d.val))=true := ha 8
  have ha9 : ((codeTrapDeletionRow d.val b.val 9 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 9 == -codeTrapDeletionDenom d.val))=true := ha 9
  have ha10 : ((codeTrapDeletionRow d.val b.val 10 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 10 == -codeTrapDeletionDenom d.val))=true := ha 10
  have ha11 : ((codeTrapDeletionRow d.val b.val 11 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 11 == -codeTrapDeletionDenom d.val))=true := ha 11
  have ha12 : ((codeTrapDeletionRow d.val b.val 12 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 12 == -codeTrapDeletionDenom d.val))=true := ha 12
  have ha13 : ((codeTrapDeletionRow d.val b.val 13 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 13 == -codeTrapDeletionDenom d.val))=true := ha 13
  have ha14 : ((codeTrapDeletionRow d.val b.val 14 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 14 == -codeTrapDeletionDenom d.val))=true := ha 14
  have ha15 : ((codeTrapDeletionRow d.val b.val 15 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 15 == -codeTrapDeletionDenom d.val))=true := ha 15
  have ha16 : ((codeTrapDeletionRow d.val b.val 16 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 16 == -codeTrapDeletionDenom d.val))=true := ha 16
  have ha17 : ((codeTrapDeletionRow d.val b.val 17 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 17 == -codeTrapDeletionDenom d.val))=true := ha 17
  have ha18 : ((codeTrapDeletionRow d.val b.val 18 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 18 == -codeTrapDeletionDenom d.val))=true := ha 18
  have ha19 : ((codeTrapDeletionRow d.val b.val 19 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 19 == -codeTrapDeletionDenom d.val))=true := ha 19
  have hc : (((codeTrapDeletionRow d.val b.val 0 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 0 == -codeTrapDeletionDenom d.val)) && ((codeTrapDeletionRow d.val b.val 1 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 1 == -codeTrapDeletionDenom d.val)) && ((codeTrapDeletionRow d.val b.val 2 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 2 == -codeTrapDeletionDenom d.val)) && ((codeTrapDeletionRow d.val b.val 3 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 3 == -codeTrapDeletionDenom d.val)) && ((codeTrapDeletionRow d.val b.val 4 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 4 == -codeTrapDeletionDenom d.val)) && ((codeTrapDeletionRow d.val b.val 5 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 5 == -codeTrapDeletionDenom d.val)) && ((codeTrapDeletionRow d.val b.val 6 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 6 == -codeTrapDeletionDenom d.val)) && ((codeTrapDeletionRow d.val b.val 7 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 7 == -codeTrapDeletionDenom d.val)) && ((codeTrapDeletionRow d.val b.val 8 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 8 == -codeTrapDeletionDenom d.val)) && ((codeTrapDeletionRow d.val b.val 9 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 9 == -codeTrapDeletionDenom d.val)) && ((codeTrapDeletionRow d.val b.val 10 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 10 == -codeTrapDeletionDenom d.val)) && ((codeTrapDeletionRow d.val b.val 11 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 11 == -codeTrapDeletionDenom d.val)) && ((codeTrapDeletionRow d.val b.val 12 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 12 == -codeTrapDeletionDenom d.val)) && ((codeTrapDeletionRow d.val b.val 13 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 13 == -codeTrapDeletionDenom d.val)) && ((codeTrapDeletionRow d.val b.val 14 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 14 == -codeTrapDeletionDenom d.val)) && ((codeTrapDeletionRow d.val b.val 15 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 15 == -codeTrapDeletionDenom d.val)) && ((codeTrapDeletionRow d.val b.val 16 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 16 == -codeTrapDeletionDenom d.val)) && ((codeTrapDeletionRow d.val b.val 17 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 17 == -codeTrapDeletionDenom d.val)) && ((codeTrapDeletionRow d.val b.val 18 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 18 == -codeTrapDeletionDenom d.val)) && ((codeTrapDeletionRow d.val b.val 19 == codeTrapDeletionDenom d.val) || (codeTrapDeletionRow d.val b.val 19 == -codeTrapDeletionDenom d.val)))=true := by
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ha0,ha1⟩,ha2⟩,ha3⟩,ha4⟩,ha5⟩,ha6⟩,ha7⟩,ha8⟩,ha9⟩,ha10⟩,ha11⟩,ha12⟩,ha13⟩,ha14⟩,ha15⟩,ha16⟩,ha17⟩,ha18⟩,ha19⟩
  have hh := codeTrap_deletion_all d b
  unfold codeTrapDeletionOne at hh
  rw [if_pos hc] at hh
  fin_cases d <;>
    norm_num [Fin.forall_fin_succ,codeTrapOldIntegerMatrix,codeTrapOldMasks,codeTrapDeletionDenom,
      Nat.testBit_eq_decide_div_mod_eq,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,and_assoc] at hh ⊢ <;>
    exact hh
end CompletionTheory
