/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Fin
public import Lean.Elab.Tactic.Omega
public import CompletionRepair.RepairCoverBatch_0
public import CompletionRepair.RepairCoverBatch_1
public import CompletionRepair.RepairCoverBatch_2
public import CompletionRepair.RepairCoverBatch_3
public import CompletionRepair.RepairCoverBatch_4
public import CompletionRepair.RepairCoverBatch_5
public import CompletionRepair.RepairCoverBatch_6
public import CompletionRepair.RepairCoverBatch_7
public import CompletionRepair.RepairCoverBatch_8
public import CompletionRepair.RepairCoverBatch_9
public import CompletionRepair.RepairCoverBatch_10
public import CompletionRepair.RepairCoverBatch_11
public import CompletionRepair.RepairCoverBatch_12
public import CompletionRepair.RepairCoverBatch_13
public import CompletionRepair.RepairCoverBatch_14
public import CompletionRepair.RepairCoverBatch_15
public import CompletionRepair.RepairCoverBatch_16
public import CompletionRepair.RepairCoverBatch_17
public import CompletionRepair.RepairCoverBatch_18
public import CompletionRepair.RepairCoverBatch_19
public import CompletionRepair.RepairCoverBatch_20
public import CompletionRepair.RepairCoverBatch_21
public import CompletionRepair.RepairCoverBatch_22
public import CompletionRepair.RepairCoverBatch_23
public import CompletionRepair.RepairCoverBatch_24
public import CompletionRepair.RepairCoverBatch_25
public import CompletionRepair.RepairCoverBatch_26
public import CompletionRepair.RepairCoverBatch_27
public import CompletionRepair.RepairCoverBatch_28
public import CompletionRepair.RepairCoverBatch_29
public import CompletionRepair.RepairCoverBatch_30
public import CompletionRepair.RepairCoverBatch_31
@[expose] public section
set_option maxRecDepth 20000
namespace CompletionTheory
theorem repair_cover_batch_spec (start count : Nat) :
    repairCoverBatch start count=true ↔
      ∀ b,start≤b → b<start+count → repairCoverOne b=true := by
  induction count with
  | zero =>
    constructor
    · intro h b hlo hhi
      omega
    · intro h
      rfl
  | succ count ih =>
    rw [repairCoverBatch,Bool.and_eq_true,ih]
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

@[irreducible] def repairCoverBatchVerified (k : Nat) : Prop := repairCoverBatch (k*256) 256=true

theorem repair_cover_batch_table_verified : ∀ k : Fin 32,repairCoverBatchVerified k.val := by
  intro k
  fin_cases k
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_0
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_1
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_2
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_3
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_4
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_5
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_6
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_7
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_8
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_9
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_10
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_11
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_12
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_13
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_14
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_15
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_16
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_17
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_18
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_19
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_20
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_21
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_22
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_23
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_24
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_25
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_26
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_27
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_28
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_29
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_30
  · simpa only [repairCoverBatchVerified] using repairCoverCertificate_31

theorem repair_cover_all (b : Fin 8192) : repairCoverOne b.val=true := by
  let k : Fin 32 := ⟨b.val/256,by omega⟩
  have hh : repairCoverBatch (k.val*256) 256=true := by
    simpa only [repairCoverBatchVerified] using repair_cover_batch_table_verified k
  apply (repair_cover_batch_spec (k.val*256) 256).mp hh b.val
  · dsimp [k]; omega
  · dsimp [k]; omega
end CompletionTheory
