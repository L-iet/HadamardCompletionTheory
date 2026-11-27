/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionRepair.RepairOriginalRelations
public import CompletionRepair.RepairShortVectors
@[expose] public section
set_option maxHeartbeats 4000000
namespace CompletionTheory

theorem repair_original_positive_short_impossible (z : Fin 24 → ℤ)
    (hz : ∀ i,z i%2=1) (hker : repairOriginalMatrix.mulVec z=0)
    (hpos : 0<z (repairFreePosition 0)) (hshort : (∑ i,z i^2)<40) : False := by
  let u : Fin 12 → ℤ := fun k => z (repairFreePosition k)
  have hv := repair_short_odd_alphabet z hz hshort
  obtain ⟨e,he⟩ := repair_four_value_shape u (fun k => hv _) (by
    intro i j hi hj
    apply repairFreePosition_injective
    exact repair_short_at_most_one_three z hz hshort _ _ hi hj)
  obtain ⟨b,hb⟩ := repair_positive_shape_encoding u hpos e he
  have henc : u=repairShortFreeVector e b := by
    funext j
    simpa [repairShortFreeVector,repairBooleanU] using hb j
  have hrec : ∀ i,repairShortNumerators e b i=4*z i := by
    intro i
    have hh := repairOriginal_reconstruct z hker i
    change 4*z i=repairKernelNumerators.mulVec u i at hh
    rw [henc] at hh
    exact hh.symm
  have hf := repairShortNumerators_odd_energy_floor e b (by
    intro i
    rw [hrec]
    have hh := hz i
    omega)
  have hsum : (∑ i,(repairShortNumerators e b i)^2)=16*∑ i,z i^2 := by
    simp_rw [hrec]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum] at hf
  omega

theorem repair_original_odd_energy_floor (z : Fin 24 → ℤ)
    (hz : ∀ i,z i%2=1) (hker : repairOriginalMatrix.mulVec z=0) :
    40≤∑ i,z i^2 := by
  by_contra hh
  have hshort : (∑ i,z i^2)<40 := by omega
  by_cases hp : 0<z (repairFreePosition 0)
  · exact repair_original_positive_short_impossible z hz hker hp hshort
  · have hn : z (repairFreePosition 0)<0 := by have hm := hz (repairFreePosition 0); omega
    have hz' : ∀ i,(-z i)%2=1 := by intro i; have hm := hz i; omega
    have hk' : repairOriginalMatrix.mulVec (fun i => -z i)=0 := by
      change repairOriginalMatrix.mulVec (-z)=0
      rw [Matrix.mulVec_neg,hker,neg_zero]
    have hs' : (∑ i,(-z i)^2)<40 := by simpa only [neg_sq] using hshort
    exact repair_original_positive_short_impossible (fun i => -z i) hz' hk' (by omega) hs'
end CompletionTheory
