/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapDeletionBoolean
@[expose] public section
set_option maxHeartbeats 40000000
set_option maxRecDepth 20000
namespace CompletionTheory
theorem codeTrapDeletionCertificate_11_1 : codeTrapDeletionBatch 11 256 256=true := by
  decide +kernel
end CompletionTheory
