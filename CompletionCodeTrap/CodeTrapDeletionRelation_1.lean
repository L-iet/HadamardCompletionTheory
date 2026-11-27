/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapDeletionData
@[expose] public section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
namespace CompletionTheory
theorem codeTrapDeleteRelation_1_0 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 1*(codeTrapDeletionDenom 1*(if (0 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 1 0 k*codeTrapDeletionSelector 1 k j)=
      ∑ k,codeTrapDeletionRelation 1 0 k*codeTrapDeletedMatrix 1 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_1_1 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 1*(codeTrapDeletionDenom 1*(if (1 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 1 1 k*codeTrapDeletionSelector 1 k j)=
      ∑ k,codeTrapDeletionRelation 1 1 k*codeTrapDeletedMatrix 1 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_1_2 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 1*(codeTrapDeletionDenom 1*(if (2 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 1 2 k*codeTrapDeletionSelector 1 k j)=
      ∑ k,codeTrapDeletionRelation 1 2 k*codeTrapDeletedMatrix 1 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_1_3 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 1*(codeTrapDeletionDenom 1*(if (3 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 1 3 k*codeTrapDeletionSelector 1 k j)=
      ∑ k,codeTrapDeletionRelation 1 3 k*codeTrapDeletedMatrix 1 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_1_4 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 1*(codeTrapDeletionDenom 1*(if (4 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 1 4 k*codeTrapDeletionSelector 1 k j)=
      ∑ k,codeTrapDeletionRelation 1 4 k*codeTrapDeletedMatrix 1 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_1_5 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 1*(codeTrapDeletionDenom 1*(if (5 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 1 5 k*codeTrapDeletionSelector 1 k j)=
      ∑ k,codeTrapDeletionRelation 1 5 k*codeTrapDeletedMatrix 1 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_1_6 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 1*(codeTrapDeletionDenom 1*(if (6 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 1 6 k*codeTrapDeletionSelector 1 k j)=
      ∑ k,codeTrapDeletionRelation 1 6 k*codeTrapDeletedMatrix 1 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_1_7 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 1*(codeTrapDeletionDenom 1*(if (7 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 1 7 k*codeTrapDeletionSelector 1 k j)=
      ∑ k,codeTrapDeletionRelation 1 7 k*codeTrapDeletedMatrix 1 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_1_8 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 1*(codeTrapDeletionDenom 1*(if (8 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 1 8 k*codeTrapDeletionSelector 1 k j)=
      ∑ k,codeTrapDeletionRelation 1 8 k*codeTrapDeletedMatrix 1 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_1_9 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 1*(codeTrapDeletionDenom 1*(if (9 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 1 9 k*codeTrapDeletionSelector 1 k j)=
      ∑ k,codeTrapDeletionRelation 1 9 k*codeTrapDeletedMatrix 1 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_1_10 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 1*(codeTrapDeletionDenom 1*(if (10 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 1 10 k*codeTrapDeletionSelector 1 k j)=
      ∑ k,codeTrapDeletionRelation 1 10 k*codeTrapDeletedMatrix 1 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_1_11 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 1*(codeTrapDeletionDenom 1*(if (11 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 1 11 k*codeTrapDeletionSelector 1 k j)=
      ∑ k,codeTrapDeletionRelation 1 11 k*codeTrapDeletedMatrix 1 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_1_12 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 1*(codeTrapDeletionDenom 1*(if (12 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 1 12 k*codeTrapDeletionSelector 1 k j)=
      ∑ k,codeTrapDeletionRelation 1 12 k*codeTrapDeletedMatrix 1 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_1_13 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 1*(codeTrapDeletionDenom 1*(if (13 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 1 13 k*codeTrapDeletionSelector 1 k j)=
      ∑ k,codeTrapDeletionRelation 1 13 k*codeTrapDeletedMatrix 1 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_1_14 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 1*(codeTrapDeletionDenom 1*(if (14 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 1 14 k*codeTrapDeletionSelector 1 k j)=
      ∑ k,codeTrapDeletionRelation 1 14 k*codeTrapDeletedMatrix 1 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_1_15 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 1*(codeTrapDeletionDenom 1*(if (15 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 1 15 k*codeTrapDeletionSelector 1 k j)=
      ∑ k,codeTrapDeletionRelation 1 15 k*codeTrapDeletedMatrix 1 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_1_16 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 1*(codeTrapDeletionDenom 1*(if (16 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 1 16 k*codeTrapDeletionSelector 1 k j)=
      ∑ k,codeTrapDeletionRelation 1 16 k*codeTrapDeletedMatrix 1 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_1_17 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 1*(codeTrapDeletionDenom 1*(if (17 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 1 17 k*codeTrapDeletionSelector 1 k j)=
      ∑ k,codeTrapDeletionRelation 1 17 k*codeTrapDeletedMatrix 1 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_1_18 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 1*(codeTrapDeletionDenom 1*(if (18 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 1 18 k*codeTrapDeletionSelector 1 k j)=
      ∑ k,codeTrapDeletionRelation 1 18 k*codeTrapDeletedMatrix 1 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_1_19 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 1*(codeTrapDeletionDenom 1*(if (19 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 1 19 k*codeTrapDeletionSelector 1 k j)=
      ∑ k,codeTrapDeletionRelation 1 19 k*codeTrapDeletedMatrix 1 k j := by
  decide +kernel

end CompletionTheory
