/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionRepair.RepairCoverBoolean
@[expose] public section
set_option maxHeartbeats 40000000
set_option maxRecDepth 20000
namespace CompletionTheory
theorem repairCoverCertificate_5 : repairCoverBatch 1280 256=true := by
  decide +kernel
end CompletionTheory
