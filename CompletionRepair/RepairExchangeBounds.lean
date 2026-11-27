/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionRepair.RepairCandidateCover
public import CompletionRepair.RepairExactMinimum
@[expose] public section
namespace CompletionTheory

theorem repair_retained_candidate_cover (z : Fin 24 → ℤ)
    (hz : ∀ i,z i=1 ∨ z i= -1) (hker : repairRetainedMatrix.mulVec z=0) :
    ∃ v : Fin 16,(∀ j,z j=repairPoolRow v j) ∨ (∀ j,z j= -repairPoolRow v j) := by
  rcases hz 0 with hpos|hneg
  · obtain ⟨v,hv⟩ := repair_retained_positive_candidate_cover z hz hker hpos
    exact ⟨v,Or.inl hv⟩
  · have hz' : ∀ i,(-z i)=1 ∨ (-z i)= -1 := by
      intro i
      rcases hz i with h|h <;> simp [h]
    have hk' : repairRetainedMatrix.mulVec (fun i => -z i)=0 := by
      change repairRetainedMatrix.mulVec (-z)=0
      rw [Matrix.mulVec_neg,hker,neg_zero]
    obtain ⟨v,hv⟩ := repair_retained_positive_candidate_cover (fun i => -z i) hz' hk' (by omega)
    refine ⟨v,Or.inr ?_⟩
    intro j
    have hh := hv j
    omega

theorem repair_retained_orthogonal_family_bound {r : ℕ} (A : Fin r → Fin 24 → ℤ)
    (hsign : ∀ i j,A i j=1 ∨ A i j= -1)
    (hker : ∀ i,repairRetainedMatrix.mulVec (A i)=0)
    (horth : ∀ i j,i≠j → (∑ k,A i k*A j k)=0) : r≤5 := by
  apply repair_colored_pool_family_bound A horth
  intro i
  exact repair_retained_candidate_cover (A i) (hsign i) (hker i)

theorem repair_original_no_sign_extension :
    ¬∃ z : Fin 24 → ℤ,(∀ i,z i=1 ∨ z i= -1) ∧ repairOriginalMatrix.mulVec z=0 := by
  rintro ⟨z,hz,hker⟩
  have hodd : ∀ i,z i%2=1 := by
    intro i
    rcases hz i with h|h <;> simp [h]
  have hh := repair_original_odd_energy_floor z hodd hker
  have hs : ∀ i,z i^2=(1 : ℤ) := by
    intro i
    rcases hz i with h|h <;> norm_num [h]
  simp only [hs,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hh
  omega
end CompletionTheory
