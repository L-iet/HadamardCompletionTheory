/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapDeletionData
@[expose] public section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
namespace CompletionTheory
theorem codeTrapDeleteRelation_2_0 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 2*(codeTrapDeletionDenom 2*(if (0 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 2 0 k*codeTrapDeletionSelector 2 k j)=
      ∑ k,codeTrapDeletionRelation 2 0 k*codeTrapDeletedMatrix 2 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_2_1 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 2*(codeTrapDeletionDenom 2*(if (1 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 2 1 k*codeTrapDeletionSelector 2 k j)=
      ∑ k,codeTrapDeletionRelation 2 1 k*codeTrapDeletedMatrix 2 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_2_2 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 2*(codeTrapDeletionDenom 2*(if (2 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 2 2 k*codeTrapDeletionSelector 2 k j)=
      ∑ k,codeTrapDeletionRelation 2 2 k*codeTrapDeletedMatrix 2 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_2_3 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 2*(codeTrapDeletionDenom 2*(if (3 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 2 3 k*codeTrapDeletionSelector 2 k j)=
      ∑ k,codeTrapDeletionRelation 2 3 k*codeTrapDeletedMatrix 2 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_2_4 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 2*(codeTrapDeletionDenom 2*(if (4 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 2 4 k*codeTrapDeletionSelector 2 k j)=
      ∑ k,codeTrapDeletionRelation 2 4 k*codeTrapDeletedMatrix 2 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_2_5 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 2*(codeTrapDeletionDenom 2*(if (5 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 2 5 k*codeTrapDeletionSelector 2 k j)=
      ∑ k,codeTrapDeletionRelation 2 5 k*codeTrapDeletedMatrix 2 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_2_6 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 2*(codeTrapDeletionDenom 2*(if (6 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 2 6 k*codeTrapDeletionSelector 2 k j)=
      ∑ k,codeTrapDeletionRelation 2 6 k*codeTrapDeletedMatrix 2 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_2_7 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 2*(codeTrapDeletionDenom 2*(if (7 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 2 7 k*codeTrapDeletionSelector 2 k j)=
      ∑ k,codeTrapDeletionRelation 2 7 k*codeTrapDeletedMatrix 2 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_2_8 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 2*(codeTrapDeletionDenom 2*(if (8 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 2 8 k*codeTrapDeletionSelector 2 k j)=
      ∑ k,codeTrapDeletionRelation 2 8 k*codeTrapDeletedMatrix 2 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_2_9 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 2*(codeTrapDeletionDenom 2*(if (9 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 2 9 k*codeTrapDeletionSelector 2 k j)=
      ∑ k,codeTrapDeletionRelation 2 9 k*codeTrapDeletedMatrix 2 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_2_10 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 2*(codeTrapDeletionDenom 2*(if (10 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 2 10 k*codeTrapDeletionSelector 2 k j)=
      ∑ k,codeTrapDeletionRelation 2 10 k*codeTrapDeletedMatrix 2 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_2_11 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 2*(codeTrapDeletionDenom 2*(if (11 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 2 11 k*codeTrapDeletionSelector 2 k j)=
      ∑ k,codeTrapDeletionRelation 2 11 k*codeTrapDeletedMatrix 2 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_2_12 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 2*(codeTrapDeletionDenom 2*(if (12 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 2 12 k*codeTrapDeletionSelector 2 k j)=
      ∑ k,codeTrapDeletionRelation 2 12 k*codeTrapDeletedMatrix 2 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_2_13 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 2*(codeTrapDeletionDenom 2*(if (13 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 2 13 k*codeTrapDeletionSelector 2 k j)=
      ∑ k,codeTrapDeletionRelation 2 13 k*codeTrapDeletedMatrix 2 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_2_14 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 2*(codeTrapDeletionDenom 2*(if (14 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 2 14 k*codeTrapDeletionSelector 2 k j)=
      ∑ k,codeTrapDeletionRelation 2 14 k*codeTrapDeletedMatrix 2 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_2_15 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 2*(codeTrapDeletionDenom 2*(if (15 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 2 15 k*codeTrapDeletionSelector 2 k j)=
      ∑ k,codeTrapDeletionRelation 2 15 k*codeTrapDeletedMatrix 2 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_2_16 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 2*(codeTrapDeletionDenom 2*(if (16 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 2 16 k*codeTrapDeletionSelector 2 k j)=
      ∑ k,codeTrapDeletionRelation 2 16 k*codeTrapDeletedMatrix 2 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_2_17 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 2*(codeTrapDeletionDenom 2*(if (17 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 2 17 k*codeTrapDeletionSelector 2 k j)=
      ∑ k,codeTrapDeletionRelation 2 17 k*codeTrapDeletedMatrix 2 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_2_18 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 2*(codeTrapDeletionDenom 2*(if (18 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 2 18 k*codeTrapDeletionSelector 2 k j)=
      ∑ k,codeTrapDeletionRelation 2 18 k*codeTrapDeletedMatrix 2 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_2_19 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 2*(codeTrapDeletionDenom 2*(if (19 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 2 19 k*codeTrapDeletionSelector 2 k j)=
      ∑ k,codeTrapDeletionRelation 2 19 k*codeTrapDeletedMatrix 2 k j := by
  decide +kernel

end CompletionTheory
