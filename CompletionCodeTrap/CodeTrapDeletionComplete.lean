/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Fin
public import Lean.Elab.Tactic.Omega
public import CompletionCodeTrap.CodeTrapDeletionBatch_0_0
public import CompletionCodeTrap.CodeTrapDeletionBatch_0_1
public import CompletionCodeTrap.CodeTrapDeletionBatch_1_0
public import CompletionCodeTrap.CodeTrapDeletionBatch_1_1
public import CompletionCodeTrap.CodeTrapDeletionBatch_2_0
public import CompletionCodeTrap.CodeTrapDeletionBatch_2_1
public import CompletionCodeTrap.CodeTrapDeletionBatch_3_0
public import CompletionCodeTrap.CodeTrapDeletionBatch_3_1
public import CompletionCodeTrap.CodeTrapDeletionBatch_4_0
public import CompletionCodeTrap.CodeTrapDeletionBatch_4_1
public import CompletionCodeTrap.CodeTrapDeletionBatch_5_0
public import CompletionCodeTrap.CodeTrapDeletionBatch_5_1
public import CompletionCodeTrap.CodeTrapDeletionBatch_6_0
public import CompletionCodeTrap.CodeTrapDeletionBatch_6_1
public import CompletionCodeTrap.CodeTrapDeletionBatch_7_0
public import CompletionCodeTrap.CodeTrapDeletionBatch_7_1
public import CompletionCodeTrap.CodeTrapDeletionBatch_8_0
public import CompletionCodeTrap.CodeTrapDeletionBatch_8_1
public import CompletionCodeTrap.CodeTrapDeletionBatch_9_0
public import CompletionCodeTrap.CodeTrapDeletionBatch_9_1
public import CompletionCodeTrap.CodeTrapDeletionBatch_10_0
public import CompletionCodeTrap.CodeTrapDeletionBatch_10_1
public import CompletionCodeTrap.CodeTrapDeletionBatch_11_0
public import CompletionCodeTrap.CodeTrapDeletionBatch_11_1
@[expose] public section
set_option maxRecDepth 20000
namespace CompletionTheory
theorem codeTrap_deletion_batch_spec (e start count : Nat) :
    codeTrapDeletionBatch e start count=true ↔
      ∀ b,start≤b → b<start+count → codeTrapDeletionOne e b=true := by
  induction count with
  | zero =>
    constructor
    · intro h b hlo hhi
      omega
    · intro h
      rfl
  | succ count ih =>
    rw [codeTrapDeletionBatch,Bool.and_eq_true,ih]
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

@[irreducible] def codeTrapDeletionBatchVerified (d k : Nat) : Prop := codeTrapDeletionBatch d (k*256) 256=true

theorem codeTrap_deletion_table : ∀ (d : Fin 12) (k : Fin 2),codeTrapDeletionBatchVerified d.val k.val := by
  intro d k
  fin_cases d <;> fin_cases k
  · simpa only [codeTrapDeletionBatchVerified] using codeTrapDeletionCertificate_0_0
  · simpa only [codeTrapDeletionBatchVerified] using codeTrapDeletionCertificate_0_1
  · simpa only [codeTrapDeletionBatchVerified] using codeTrapDeletionCertificate_1_0
  · simpa only [codeTrapDeletionBatchVerified] using codeTrapDeletionCertificate_1_1
  · simpa only [codeTrapDeletionBatchVerified] using codeTrapDeletionCertificate_2_0
  · simpa only [codeTrapDeletionBatchVerified] using codeTrapDeletionCertificate_2_1
  · simpa only [codeTrapDeletionBatchVerified] using codeTrapDeletionCertificate_3_0
  · simpa only [codeTrapDeletionBatchVerified] using codeTrapDeletionCertificate_3_1
  · simpa only [codeTrapDeletionBatchVerified] using codeTrapDeletionCertificate_4_0
  · simpa only [codeTrapDeletionBatchVerified] using codeTrapDeletionCertificate_4_1
  · simpa only [codeTrapDeletionBatchVerified] using codeTrapDeletionCertificate_5_0
  · simpa only [codeTrapDeletionBatchVerified] using codeTrapDeletionCertificate_5_1
  · simpa only [codeTrapDeletionBatchVerified] using codeTrapDeletionCertificate_6_0
  · simpa only [codeTrapDeletionBatchVerified] using codeTrapDeletionCertificate_6_1
  · simpa only [codeTrapDeletionBatchVerified] using codeTrapDeletionCertificate_7_0
  · simpa only [codeTrapDeletionBatchVerified] using codeTrapDeletionCertificate_7_1
  · simpa only [codeTrapDeletionBatchVerified] using codeTrapDeletionCertificate_8_0
  · simpa only [codeTrapDeletionBatchVerified] using codeTrapDeletionCertificate_8_1
  · simpa only [codeTrapDeletionBatchVerified] using codeTrapDeletionCertificate_9_0
  · simpa only [codeTrapDeletionBatchVerified] using codeTrapDeletionCertificate_9_1
  · simpa only [codeTrapDeletionBatchVerified] using codeTrapDeletionCertificate_10_0
  · simpa only [codeTrapDeletionBatchVerified] using codeTrapDeletionCertificate_10_1
  · simpa only [codeTrapDeletionBatchVerified] using codeTrapDeletionCertificate_11_0
  · simpa only [codeTrapDeletionBatchVerified] using codeTrapDeletionCertificate_11_1

theorem codeTrap_deletion_all (d : Fin 12) (b : Fin 512) : codeTrapDeletionOne d.val b.val=true := by
  let k : Fin 2 := ⟨b.val/256,by omega⟩
  have hh : codeTrapDeletionBatch d.val (k.val*256) 256=true := by
    simpa only [codeTrapDeletionBatchVerified] using codeTrap_deletion_table d k
  apply (codeTrap_deletion_batch_spec d.val (k.val*256) 256).mp hh b.val
  · dsimp [k]; omega
  · dsimp [k]; omega
end CompletionTheory
