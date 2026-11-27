/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapDeletionData
@[expose] public section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
namespace CompletionTheory
theorem codeTrapDeleteRelation_3_0 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 3*(codeTrapDeletionDenom 3*(if (0 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 3 0 k*codeTrapDeletionSelector 3 k j)=
      ∑ k,codeTrapDeletionRelation 3 0 k*codeTrapDeletedMatrix 3 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_3_1 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 3*(codeTrapDeletionDenom 3*(if (1 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 3 1 k*codeTrapDeletionSelector 3 k j)=
      ∑ k,codeTrapDeletionRelation 3 1 k*codeTrapDeletedMatrix 3 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_3_2 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 3*(codeTrapDeletionDenom 3*(if (2 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 3 2 k*codeTrapDeletionSelector 3 k j)=
      ∑ k,codeTrapDeletionRelation 3 2 k*codeTrapDeletedMatrix 3 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_3_3 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 3*(codeTrapDeletionDenom 3*(if (3 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 3 3 k*codeTrapDeletionSelector 3 k j)=
      ∑ k,codeTrapDeletionRelation 3 3 k*codeTrapDeletedMatrix 3 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_3_4 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 3*(codeTrapDeletionDenom 3*(if (4 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 3 4 k*codeTrapDeletionSelector 3 k j)=
      ∑ k,codeTrapDeletionRelation 3 4 k*codeTrapDeletedMatrix 3 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_3_5 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 3*(codeTrapDeletionDenom 3*(if (5 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 3 5 k*codeTrapDeletionSelector 3 k j)=
      ∑ k,codeTrapDeletionRelation 3 5 k*codeTrapDeletedMatrix 3 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_3_6 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 3*(codeTrapDeletionDenom 3*(if (6 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 3 6 k*codeTrapDeletionSelector 3 k j)=
      ∑ k,codeTrapDeletionRelation 3 6 k*codeTrapDeletedMatrix 3 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_3_7 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 3*(codeTrapDeletionDenom 3*(if (7 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 3 7 k*codeTrapDeletionSelector 3 k j)=
      ∑ k,codeTrapDeletionRelation 3 7 k*codeTrapDeletedMatrix 3 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_3_8 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 3*(codeTrapDeletionDenom 3*(if (8 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 3 8 k*codeTrapDeletionSelector 3 k j)=
      ∑ k,codeTrapDeletionRelation 3 8 k*codeTrapDeletedMatrix 3 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_3_9 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 3*(codeTrapDeletionDenom 3*(if (9 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 3 9 k*codeTrapDeletionSelector 3 k j)=
      ∑ k,codeTrapDeletionRelation 3 9 k*codeTrapDeletedMatrix 3 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_3_10 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 3*(codeTrapDeletionDenom 3*(if (10 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 3 10 k*codeTrapDeletionSelector 3 k j)=
      ∑ k,codeTrapDeletionRelation 3 10 k*codeTrapDeletedMatrix 3 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_3_11 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 3*(codeTrapDeletionDenom 3*(if (11 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 3 11 k*codeTrapDeletionSelector 3 k j)=
      ∑ k,codeTrapDeletionRelation 3 11 k*codeTrapDeletedMatrix 3 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_3_12 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 3*(codeTrapDeletionDenom 3*(if (12 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 3 12 k*codeTrapDeletionSelector 3 k j)=
      ∑ k,codeTrapDeletionRelation 3 12 k*codeTrapDeletedMatrix 3 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_3_13 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 3*(codeTrapDeletionDenom 3*(if (13 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 3 13 k*codeTrapDeletionSelector 3 k j)=
      ∑ k,codeTrapDeletionRelation 3 13 k*codeTrapDeletedMatrix 3 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_3_14 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 3*(codeTrapDeletionDenom 3*(if (14 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 3 14 k*codeTrapDeletionSelector 3 k j)=
      ∑ k,codeTrapDeletionRelation 3 14 k*codeTrapDeletedMatrix 3 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_3_15 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 3*(codeTrapDeletionDenom 3*(if (15 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 3 15 k*codeTrapDeletionSelector 3 k j)=
      ∑ k,codeTrapDeletionRelation 3 15 k*codeTrapDeletedMatrix 3 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_3_16 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 3*(codeTrapDeletionDenom 3*(if (16 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 3 16 k*codeTrapDeletionSelector 3 k j)=
      ∑ k,codeTrapDeletionRelation 3 16 k*codeTrapDeletedMatrix 3 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_3_17 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 3*(codeTrapDeletionDenom 3*(if (17 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 3 17 k*codeTrapDeletionSelector 3 k j)=
      ∑ k,codeTrapDeletionRelation 3 17 k*codeTrapDeletedMatrix 3 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_3_18 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 3*(codeTrapDeletionDenom 3*(if (18 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 3 18 k*codeTrapDeletionSelector 3 k j)=
      ∑ k,codeTrapDeletionRelation 3 18 k*codeTrapDeletedMatrix 3 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_3_19 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 3*(codeTrapDeletionDenom 3*(if (19 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 3 19 k*codeTrapDeletionSelector 3 k j)=
      ∑ k,codeTrapDeletionRelation 3 19 k*codeTrapDeletedMatrix 3 k j := by
  decide +kernel

end CompletionTheory
