/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionRepair.RepairMinimumEnergy
@[expose] public section
namespace CompletionTheory

def repairOddWitness : Fin 24 → ℤ := ![-1,-1,3,-1,1,1,-3,-1,1,1,-1,1,1,-1,-1,-1,1,-1,1,-1,1,-1,1,1]

theorem repair_odd_witness_parity : ∀ i,repairOddWitness i%2=1 := by decide +kernel

theorem repair_odd_witness_kernel_entries : ∀ i,repairOriginalMatrix.mulVec repairOddWitness i=0 := by decide +kernel

theorem repair_odd_witness_kernel : repairOriginalMatrix.mulVec repairOddWitness=0 := by
  funext i
  exact repair_odd_witness_kernel_entries i

theorem repair_odd_witness_energy : (∑ i,repairOddWitness i^2)=40 := by decide +kernel

theorem repair_original_odd_minimum_exact :
    (∀ z : Fin 24 → ℤ,(∀ i,z i%2=1) → repairOriginalMatrix.mulVec z=0 → 40≤∑ i,z i^2) ∧
    ∃ z : Fin 24 → ℤ,(∀ i,z i%2=1) ∧ repairOriginalMatrix.mulVec z=0 ∧ (∑ i,z i^2)=40 := by
  exact ⟨repair_original_odd_energy_floor,repairOddWitness,repair_odd_witness_parity,
    repair_odd_witness_kernel,repair_odd_witness_energy⟩
end CompletionTheory
