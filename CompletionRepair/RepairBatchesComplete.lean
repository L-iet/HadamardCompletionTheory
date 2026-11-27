/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Fin
public import Lean.Elab.Tactic.Omega
public import CompletionRepair.RepairBatch_0_0
public import CompletionRepair.RepairBatch_0_1
public import CompletionRepair.RepairBatch_0_2
public import CompletionRepair.RepairBatch_0_3
public import CompletionRepair.RepairBatch_0_4
public import CompletionRepair.RepairBatch_0_5
public import CompletionRepair.RepairBatch_0_6
public import CompletionRepair.RepairBatch_0_7
public import CompletionRepair.RepairBatch_1_0
public import CompletionRepair.RepairBatch_1_1
public import CompletionRepair.RepairBatch_1_2
public import CompletionRepair.RepairBatch_1_3
public import CompletionRepair.RepairBatch_1_4
public import CompletionRepair.RepairBatch_1_5
public import CompletionRepair.RepairBatch_1_6
public import CompletionRepair.RepairBatch_1_7
public import CompletionRepair.RepairBatch_2_0
public import CompletionRepair.RepairBatch_2_1
public import CompletionRepair.RepairBatch_2_2
public import CompletionRepair.RepairBatch_2_3
public import CompletionRepair.RepairBatch_2_4
public import CompletionRepair.RepairBatch_2_5
public import CompletionRepair.RepairBatch_2_6
public import CompletionRepair.RepairBatch_2_7
public import CompletionRepair.RepairBatch_3_0
public import CompletionRepair.RepairBatch_3_1
public import CompletionRepair.RepairBatch_3_2
public import CompletionRepair.RepairBatch_3_3
public import CompletionRepair.RepairBatch_3_4
public import CompletionRepair.RepairBatch_3_5
public import CompletionRepair.RepairBatch_3_6
public import CompletionRepair.RepairBatch_3_7
public import CompletionRepair.RepairBatch_4_0
public import CompletionRepair.RepairBatch_4_1
public import CompletionRepair.RepairBatch_4_2
public import CompletionRepair.RepairBatch_4_3
public import CompletionRepair.RepairBatch_4_4
public import CompletionRepair.RepairBatch_4_5
public import CompletionRepair.RepairBatch_4_6
public import CompletionRepair.RepairBatch_4_7
public import CompletionRepair.RepairBatch_5_0
public import CompletionRepair.RepairBatch_5_1
public import CompletionRepair.RepairBatch_5_2
public import CompletionRepair.RepairBatch_5_3
public import CompletionRepair.RepairBatch_5_4
public import CompletionRepair.RepairBatch_5_5
public import CompletionRepair.RepairBatch_5_6
public import CompletionRepair.RepairBatch_5_7
public import CompletionRepair.RepairBatch_6_0
public import CompletionRepair.RepairBatch_6_1
public import CompletionRepair.RepairBatch_6_2
public import CompletionRepair.RepairBatch_6_3
public import CompletionRepair.RepairBatch_6_4
public import CompletionRepair.RepairBatch_6_5
public import CompletionRepair.RepairBatch_6_6
public import CompletionRepair.RepairBatch_6_7
public import CompletionRepair.RepairBatch_7_0
public import CompletionRepair.RepairBatch_7_1
public import CompletionRepair.RepairBatch_7_2
public import CompletionRepair.RepairBatch_7_3
public import CompletionRepair.RepairBatch_7_4
public import CompletionRepair.RepairBatch_7_5
public import CompletionRepair.RepairBatch_7_6
public import CompletionRepair.RepairBatch_7_7
public import CompletionRepair.RepairBatch_8_0
public import CompletionRepair.RepairBatch_8_1
public import CompletionRepair.RepairBatch_8_2
public import CompletionRepair.RepairBatch_8_3
public import CompletionRepair.RepairBatch_8_4
public import CompletionRepair.RepairBatch_8_5
public import CompletionRepair.RepairBatch_8_6
public import CompletionRepair.RepairBatch_8_7
public import CompletionRepair.RepairBatch_9_0
public import CompletionRepair.RepairBatch_9_1
public import CompletionRepair.RepairBatch_9_2
public import CompletionRepair.RepairBatch_9_3
public import CompletionRepair.RepairBatch_9_4
public import CompletionRepair.RepairBatch_9_5
public import CompletionRepair.RepairBatch_9_6
public import CompletionRepair.RepairBatch_9_7
public import CompletionRepair.RepairBatch_10_0
public import CompletionRepair.RepairBatch_10_1
public import CompletionRepair.RepairBatch_10_2
public import CompletionRepair.RepairBatch_10_3
public import CompletionRepair.RepairBatch_10_4
public import CompletionRepair.RepairBatch_10_5
public import CompletionRepair.RepairBatch_10_6
public import CompletionRepair.RepairBatch_10_7
public import CompletionRepair.RepairBatch_11_0
public import CompletionRepair.RepairBatch_11_1
public import CompletionRepair.RepairBatch_11_2
public import CompletionRepair.RepairBatch_11_3
public import CompletionRepair.RepairBatch_11_4
public import CompletionRepair.RepairBatch_11_5
public import CompletionRepair.RepairBatch_11_6
public import CompletionRepair.RepairBatch_11_7
public import CompletionRepair.RepairBatch_12_0
public import CompletionRepair.RepairBatch_12_1
public import CompletionRepair.RepairBatch_12_2
public import CompletionRepair.RepairBatch_12_3
public import CompletionRepair.RepairBatch_12_4
public import CompletionRepair.RepairBatch_12_5
public import CompletionRepair.RepairBatch_12_6
public import CompletionRepair.RepairBatch_12_7
@[expose] public section
set_option maxRecDepth 20000
namespace CompletionTheory

theorem repair_boolean_batch_spec (e start count : Nat) :
    repairBooleanBatch e start count=true ↔
      ∀ b,start≤b → b<start+count → repairBooleanOne e b=true := by
  induction count with
  | zero =>
    constructor
    · intro h b hlo hhi
      omega
    · intro h
      rfl
  | succ count ih =>
    rw [repairBooleanBatch,Bool.and_eq_true,ih]
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

@[irreducible] def repairBooleanBatchVerified (e k : Nat) : Prop :=
  repairBooleanBatch e (k*256) 256=true

theorem repair_boolean_batch_table_verified : ∀ (e : Fin 13) (k : Fin 8),
    repairBooleanBatchVerified e.val k.val := by
  intro e k
  fin_cases e <;> fin_cases k
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_0_0
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_0_1
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_0_2
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_0_3
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_0_4
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_0_5
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_0_6
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_0_7
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_1_0
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_1_1
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_1_2
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_1_3
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_1_4
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_1_5
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_1_6
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_1_7
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_2_0
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_2_1
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_2_2
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_2_3
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_2_4
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_2_5
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_2_6
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_2_7
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_3_0
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_3_1
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_3_2
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_3_3
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_3_4
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_3_5
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_3_6
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_3_7
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_4_0
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_4_1
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_4_2
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_4_3
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_4_4
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_4_5
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_4_6
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_4_7
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_5_0
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_5_1
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_5_2
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_5_3
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_5_4
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_5_5
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_5_6
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_5_7
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_6_0
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_6_1
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_6_2
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_6_3
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_6_4
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_6_5
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_6_6
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_6_7
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_7_0
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_7_1
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_7_2
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_7_3
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_7_4
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_7_5
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_7_6
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_7_7
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_8_0
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_8_1
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_8_2
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_8_3
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_8_4
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_8_5
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_8_6
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_8_7
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_9_0
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_9_1
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_9_2
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_9_3
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_9_4
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_9_5
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_9_6
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_9_7
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_10_0
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_10_1
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_10_2
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_10_3
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_10_4
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_10_5
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_10_6
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_10_7
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_11_0
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_11_1
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_11_2
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_11_3
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_11_4
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_11_5
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_11_6
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_11_7
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_12_0
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_12_1
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_12_2
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_12_3
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_12_4
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_12_5
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_12_6
  · unfold repairBooleanBatchVerified
    exact repairBooleanCertificate_12_7

theorem repair_boolean_batch_table (e : Fin 13) (k : Fin 8) :
    repairBooleanBatch e.val (k.val*256) 256=true := by
  simpa only [repairBooleanBatchVerified] using repair_boolean_batch_table_verified e k

theorem repair_boolean_all (e : Fin 13) (b : Fin 2048) :
    repairBooleanOne e.val b.val=true := by
  let k : Fin 8 := ⟨b.val/256,by omega⟩
  have hh := repair_boolean_batch_table e k
  apply (repair_boolean_batch_spec e.val (k.val*256) 256).mp hh b.val
  · dsimp [k]
    omega
  · dsimp [k]
    omega
end CompletionTheory
