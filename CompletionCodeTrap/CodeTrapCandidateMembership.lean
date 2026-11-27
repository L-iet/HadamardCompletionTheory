/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.ModularCodeParity
@[expose] public section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory
theorem trap_code_candidate_membership {q N : ℕ}
    (C : Submodule (ZMod q) (Fin N → ZMod q)) (x : Fin N → Bool) :
    x∈codeSignCandidates C ↔ positiveFirstBit x ∧ (fun j => (modularBitSign (x j) : ZMod q))∈C := by
  classical
  simp only [codeSignCandidates,Finset.mem_filter,Finset.mem_univ,true_and]
end CompletionTheory
