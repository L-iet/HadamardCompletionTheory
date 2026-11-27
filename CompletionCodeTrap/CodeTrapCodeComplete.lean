/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fin.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.NormNum
public import Lean.Elab.Tactic.Omega
public import CompletionCodeTrap.CodeTrapCodeBatch_0_0
public import CompletionCodeTrap.CodeTrapCodeBatch_0_1
public import CompletionCodeTrap.CodeTrapCodeBatch_1_0
public import CompletionCodeTrap.CodeTrapCodeBatch_1_1
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace CompletionTheory
theorem trap_code_class_batch_spec (e start count : Nat) :
    trapCodeClassBatch e start count=true ↔
      ∀ b,start≤b → b<start+count → trapCodeClassOne e b=true := by
  induction count with
  | zero =>
    constructor
    · intro h b hlo hhi
      omega
    · intro h
      rfl
  | succ count ih =>
    rw [trapCodeClassBatch,Bool.and_eq_true,ih]
    constructor
    · rintro ⟨htop,hrest⟩ b hlo hhi
      by_cases hb : b=start+count
      · subst b
        exact htop
      · exact hrest b hlo (by omega)
    · intro h
      refine ⟨h (start+count) (by omega) (by omega),?_⟩
      intro b hlo hhi
      exact h b hlo (by omega)

@[irreducible] def trapCodeClassBatchVerified (d k : Nat) : Prop := trapCodeClassBatch d (k*256) 256=true

theorem trap_code_class_table : ∀ (d : Fin 2) (k : Fin 2),trapCodeClassBatchVerified d.val k.val := by
  intro d k
  fin_cases d <;> fin_cases k
  · simpa only [trapCodeClassBatchVerified] using trapCodeClassCertificate_0_0
  · simpa only [trapCodeClassBatchVerified] using trapCodeClassCertificate_0_1
  · simpa only [trapCodeClassBatchVerified] using trapCodeClassCertificate_1_0
  · simpa only [trapCodeClassBatchVerified] using trapCodeClassCertificate_1_1

theorem trap_code_class_all (d : Fin 2) (b : Fin 512) : trapCodeClassOne d.val b.val=true := by
  let k : Fin 2 := ⟨b.val/256,by omega⟩
  have hh : trapCodeClassBatch d.val (k.val*256) 256=true := by
    simpa only [trapCodeClassBatchVerified] using trap_code_class_table d k
  apply (trap_code_class_batch_spec d.val (k.val*256) 256).mp hh b.val
  · dsimp [k]; omega
  · dsimp [k]; omega
def trapOldClassMask : Fin 12 → ℕ := ![0,250934,501868,1003736,965904,358790,649754,694982,902980,210762,412530,730036]
def trapNewClassMask : Fin 20 → ℕ := ![0,250934,816740,307898,1003736,210762,581982,444300,730036,886242,855582,501868,683178,694982,126672,965904,645928,412530,358790,7676]
def trapOldResidueWord (i : Fin 12) (j : Fin 20) : ℤ := if (trapOldClassMask i).testBit j.val then 4 else 1
def trapNewResidueWord (i : Fin 20) (j : Fin 20) : ℤ := if (trapNewClassMask i).testBit j.val then 4 else 1
theorem trapOldResidue_classification (b : Fin 512)
    (hsign : ∀ i : Fin 20,trapCodewordEntry 0 b.val i.val=1 ∨ trapCodewordEntry 0 b.val i.val=4) :
    ∃ k : Fin 12,∀ i : Fin 20,trapCodewordEntry 0 b.val i.val=trapOldResidueWord k i := by
  have ha : ∀ i : Fin 20,((trapCodewordEntry 0 b.val i.val == 1) || (trapCodewordEntry 0 b.val i.val == 4))=true := by
    intro i
    rcases hsign i with h|h <;> simp [h]
  have ha0 : ((trapCodewordEntry 0 b.val 0 == 1) || (trapCodewordEntry 0 b.val 0 == 4))=true := ha 0
  have ha1 : ((trapCodewordEntry 0 b.val 1 == 1) || (trapCodewordEntry 0 b.val 1 == 4))=true := ha 1
  have ha2 : ((trapCodewordEntry 0 b.val 2 == 1) || (trapCodewordEntry 0 b.val 2 == 4))=true := ha 2
  have ha3 : ((trapCodewordEntry 0 b.val 3 == 1) || (trapCodewordEntry 0 b.val 3 == 4))=true := ha 3
  have ha4 : ((trapCodewordEntry 0 b.val 4 == 1) || (trapCodewordEntry 0 b.val 4 == 4))=true := ha 4
  have ha5 : ((trapCodewordEntry 0 b.val 5 == 1) || (trapCodewordEntry 0 b.val 5 == 4))=true := ha 5
  have ha6 : ((trapCodewordEntry 0 b.val 6 == 1) || (trapCodewordEntry 0 b.val 6 == 4))=true := ha 6
  have ha7 : ((trapCodewordEntry 0 b.val 7 == 1) || (trapCodewordEntry 0 b.val 7 == 4))=true := ha 7
  have ha8 : ((trapCodewordEntry 0 b.val 8 == 1) || (trapCodewordEntry 0 b.val 8 == 4))=true := ha 8
  have ha9 : ((trapCodewordEntry 0 b.val 9 == 1) || (trapCodewordEntry 0 b.val 9 == 4))=true := ha 9
  have ha10 : ((trapCodewordEntry 0 b.val 10 == 1) || (trapCodewordEntry 0 b.val 10 == 4))=true := ha 10
  have ha11 : ((trapCodewordEntry 0 b.val 11 == 1) || (trapCodewordEntry 0 b.val 11 == 4))=true := ha 11
  have ha12 : ((trapCodewordEntry 0 b.val 12 == 1) || (trapCodewordEntry 0 b.val 12 == 4))=true := ha 12
  have ha13 : ((trapCodewordEntry 0 b.val 13 == 1) || (trapCodewordEntry 0 b.val 13 == 4))=true := ha 13
  have ha14 : ((trapCodewordEntry 0 b.val 14 == 1) || (trapCodewordEntry 0 b.val 14 == 4))=true := ha 14
  have ha15 : ((trapCodewordEntry 0 b.val 15 == 1) || (trapCodewordEntry 0 b.val 15 == 4))=true := ha 15
  have ha16 : ((trapCodewordEntry 0 b.val 16 == 1) || (trapCodewordEntry 0 b.val 16 == 4))=true := ha 16
  have ha17 : ((trapCodewordEntry 0 b.val 17 == 1) || (trapCodewordEntry 0 b.val 17 == 4))=true := ha 17
  have ha18 : ((trapCodewordEntry 0 b.val 18 == 1) || (trapCodewordEntry 0 b.val 18 == 4))=true := ha 18
  have ha19 : ((trapCodewordEntry 0 b.val 19 == 1) || (trapCodewordEntry 0 b.val 19 == 4))=true := ha 19
  have hc : (((trapCodewordEntry 0 b.val 0 == 1) || (trapCodewordEntry 0 b.val 0 == 4)) && ((trapCodewordEntry 0 b.val 1 == 1) || (trapCodewordEntry 0 b.val 1 == 4)) && ((trapCodewordEntry 0 b.val 2 == 1) || (trapCodewordEntry 0 b.val 2 == 4)) && ((trapCodewordEntry 0 b.val 3 == 1) || (trapCodewordEntry 0 b.val 3 == 4)) && ((trapCodewordEntry 0 b.val 4 == 1) || (trapCodewordEntry 0 b.val 4 == 4)) && ((trapCodewordEntry 0 b.val 5 == 1) || (trapCodewordEntry 0 b.val 5 == 4)) && ((trapCodewordEntry 0 b.val 6 == 1) || (trapCodewordEntry 0 b.val 6 == 4)) && ((trapCodewordEntry 0 b.val 7 == 1) || (trapCodewordEntry 0 b.val 7 == 4)) && ((trapCodewordEntry 0 b.val 8 == 1) || (trapCodewordEntry 0 b.val 8 == 4)) && ((trapCodewordEntry 0 b.val 9 == 1) || (trapCodewordEntry 0 b.val 9 == 4)) && ((trapCodewordEntry 0 b.val 10 == 1) || (trapCodewordEntry 0 b.val 10 == 4)) && ((trapCodewordEntry 0 b.val 11 == 1) || (trapCodewordEntry 0 b.val 11 == 4)) && ((trapCodewordEntry 0 b.val 12 == 1) || (trapCodewordEntry 0 b.val 12 == 4)) && ((trapCodewordEntry 0 b.val 13 == 1) || (trapCodewordEntry 0 b.val 13 == 4)) && ((trapCodewordEntry 0 b.val 14 == 1) || (trapCodewordEntry 0 b.val 14 == 4)) && ((trapCodewordEntry 0 b.val 15 == 1) || (trapCodewordEntry 0 b.val 15 == 4)) && ((trapCodewordEntry 0 b.val 16 == 1) || (trapCodewordEntry 0 b.val 16 == 4)) && ((trapCodewordEntry 0 b.val 17 == 1) || (trapCodewordEntry 0 b.val 17 == 4)) && ((trapCodewordEntry 0 b.val 18 == 1) || (trapCodewordEntry 0 b.val 18 == 4)) && ((trapCodewordEntry 0 b.val 19 == 1) || (trapCodewordEntry 0 b.val 19 == 4)))=true := by
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ha0,ha1⟩,ha2⟩,ha3⟩,ha4⟩,ha5⟩,ha6⟩,ha7⟩,ha8⟩,ha9⟩,ha10⟩,ha11⟩,ha12⟩,ha13⟩,ha14⟩,ha15⟩,ha16⟩,ha17⟩,ha18⟩,ha19⟩
  have hh := trap_code_class_all 0 b
  change trapCodeClassOne 0 b.val=true at hh
  unfold trapCodeClassOne at hh
  dsimp only at hh
  rw [if_pos hc] at hh
  norm_num [Fin.exists_fin_succ,Fin.forall_fin_succ,trapOldResidueWord,trapOldClassMask,
    Nat.testBit_eq_decide_div_mod_eq,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,and_assoc,or_assoc] at hh ⊢
  exact hh

theorem trapNewResidue_classification (b : Fin 512)
    (hsign : ∀ i : Fin 20,trapCodewordEntry 1 b.val i.val=1 ∨ trapCodewordEntry 1 b.val i.val=4) :
    ∃ k : Fin 20,∀ i : Fin 20,trapCodewordEntry 1 b.val i.val=trapNewResidueWord k i := by
  have ha : ∀ i : Fin 20,((trapCodewordEntry 1 b.val i.val == 1) || (trapCodewordEntry 1 b.val i.val == 4))=true := by
    intro i
    rcases hsign i with h|h <;> simp [h]
  have ha0 : ((trapCodewordEntry 1 b.val 0 == 1) || (trapCodewordEntry 1 b.val 0 == 4))=true := ha 0
  have ha1 : ((trapCodewordEntry 1 b.val 1 == 1) || (trapCodewordEntry 1 b.val 1 == 4))=true := ha 1
  have ha2 : ((trapCodewordEntry 1 b.val 2 == 1) || (trapCodewordEntry 1 b.val 2 == 4))=true := ha 2
  have ha3 : ((trapCodewordEntry 1 b.val 3 == 1) || (trapCodewordEntry 1 b.val 3 == 4))=true := ha 3
  have ha4 : ((trapCodewordEntry 1 b.val 4 == 1) || (trapCodewordEntry 1 b.val 4 == 4))=true := ha 4
  have ha5 : ((trapCodewordEntry 1 b.val 5 == 1) || (trapCodewordEntry 1 b.val 5 == 4))=true := ha 5
  have ha6 : ((trapCodewordEntry 1 b.val 6 == 1) || (trapCodewordEntry 1 b.val 6 == 4))=true := ha 6
  have ha7 : ((trapCodewordEntry 1 b.val 7 == 1) || (trapCodewordEntry 1 b.val 7 == 4))=true := ha 7
  have ha8 : ((trapCodewordEntry 1 b.val 8 == 1) || (trapCodewordEntry 1 b.val 8 == 4))=true := ha 8
  have ha9 : ((trapCodewordEntry 1 b.val 9 == 1) || (trapCodewordEntry 1 b.val 9 == 4))=true := ha 9
  have ha10 : ((trapCodewordEntry 1 b.val 10 == 1) || (trapCodewordEntry 1 b.val 10 == 4))=true := ha 10
  have ha11 : ((trapCodewordEntry 1 b.val 11 == 1) || (trapCodewordEntry 1 b.val 11 == 4))=true := ha 11
  have ha12 : ((trapCodewordEntry 1 b.val 12 == 1) || (trapCodewordEntry 1 b.val 12 == 4))=true := ha 12
  have ha13 : ((trapCodewordEntry 1 b.val 13 == 1) || (trapCodewordEntry 1 b.val 13 == 4))=true := ha 13
  have ha14 : ((trapCodewordEntry 1 b.val 14 == 1) || (trapCodewordEntry 1 b.val 14 == 4))=true := ha 14
  have ha15 : ((trapCodewordEntry 1 b.val 15 == 1) || (trapCodewordEntry 1 b.val 15 == 4))=true := ha 15
  have ha16 : ((trapCodewordEntry 1 b.val 16 == 1) || (trapCodewordEntry 1 b.val 16 == 4))=true := ha 16
  have ha17 : ((trapCodewordEntry 1 b.val 17 == 1) || (trapCodewordEntry 1 b.val 17 == 4))=true := ha 17
  have ha18 : ((trapCodewordEntry 1 b.val 18 == 1) || (trapCodewordEntry 1 b.val 18 == 4))=true := ha 18
  have ha19 : ((trapCodewordEntry 1 b.val 19 == 1) || (trapCodewordEntry 1 b.val 19 == 4))=true := ha 19
  have hc : (((trapCodewordEntry 1 b.val 0 == 1) || (trapCodewordEntry 1 b.val 0 == 4)) && ((trapCodewordEntry 1 b.val 1 == 1) || (trapCodewordEntry 1 b.val 1 == 4)) && ((trapCodewordEntry 1 b.val 2 == 1) || (trapCodewordEntry 1 b.val 2 == 4)) && ((trapCodewordEntry 1 b.val 3 == 1) || (trapCodewordEntry 1 b.val 3 == 4)) && ((trapCodewordEntry 1 b.val 4 == 1) || (trapCodewordEntry 1 b.val 4 == 4)) && ((trapCodewordEntry 1 b.val 5 == 1) || (trapCodewordEntry 1 b.val 5 == 4)) && ((trapCodewordEntry 1 b.val 6 == 1) || (trapCodewordEntry 1 b.val 6 == 4)) && ((trapCodewordEntry 1 b.val 7 == 1) || (trapCodewordEntry 1 b.val 7 == 4)) && ((trapCodewordEntry 1 b.val 8 == 1) || (trapCodewordEntry 1 b.val 8 == 4)) && ((trapCodewordEntry 1 b.val 9 == 1) || (trapCodewordEntry 1 b.val 9 == 4)) && ((trapCodewordEntry 1 b.val 10 == 1) || (trapCodewordEntry 1 b.val 10 == 4)) && ((trapCodewordEntry 1 b.val 11 == 1) || (trapCodewordEntry 1 b.val 11 == 4)) && ((trapCodewordEntry 1 b.val 12 == 1) || (trapCodewordEntry 1 b.val 12 == 4)) && ((trapCodewordEntry 1 b.val 13 == 1) || (trapCodewordEntry 1 b.val 13 == 4)) && ((trapCodewordEntry 1 b.val 14 == 1) || (trapCodewordEntry 1 b.val 14 == 4)) && ((trapCodewordEntry 1 b.val 15 == 1) || (trapCodewordEntry 1 b.val 15 == 4)) && ((trapCodewordEntry 1 b.val 16 == 1) || (trapCodewordEntry 1 b.val 16 == 4)) && ((trapCodewordEntry 1 b.val 17 == 1) || (trapCodewordEntry 1 b.val 17 == 4)) && ((trapCodewordEntry 1 b.val 18 == 1) || (trapCodewordEntry 1 b.val 18 == 4)) && ((trapCodewordEntry 1 b.val 19 == 1) || (trapCodewordEntry 1 b.val 19 == 4)))=true := by
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ha0,ha1⟩,ha2⟩,ha3⟩,ha4⟩,ha5⟩,ha6⟩,ha7⟩,ha8⟩,ha9⟩,ha10⟩,ha11⟩,ha12⟩,ha13⟩,ha14⟩,ha15⟩,ha16⟩,ha17⟩,ha18⟩,ha19⟩
  have hh := trap_code_class_all 1 b
  change trapCodeClassOne 1 b.val=true at hh
  unfold trapCodeClassOne at hh
  dsimp only at hh
  rw [if_pos hc] at hh
  norm_num [Fin.exists_fin_succ,Fin.forall_fin_succ,trapNewResidueWord,trapNewClassMask,
    Nat.testBit_eq_decide_div_mod_eq,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,and_assoc,or_assoc] at hh ⊢
  exact hh

theorem trapCodewordEntry_range (d : Fin 2) (b : Nat) (i : Fin 20) :
    0≤trapCodewordEntry d.val b i.val ∧ trapCodewordEntry d.val b i.val<5 := by
  fin_cases d <;> fin_cases i <;> simp only [trapCodewordEntry] <;>
    exact ⟨Int.emod_nonneg _ (by decide),Int.emod_lt_of_pos _ (by decide)⟩
end CompletionTheory
