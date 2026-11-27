/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapCodeBoolean
@[expose] public section
set_option maxHeartbeats 40000000
set_option maxRecDepth 20000
namespace CompletionTheory
theorem trapCodeClassCertificate_0_1 : trapCodeClassBatch 0 256 256=true := by
  decide +kernel
end CompletionTheory
