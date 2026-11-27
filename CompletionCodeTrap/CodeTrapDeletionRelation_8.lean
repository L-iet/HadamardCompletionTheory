/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapDeletionData
@[expose] public section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
namespace CompletionTheory
theorem codeTrapDeleteRelation_8_0 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 8*(codeTrapDeletionDenom 8*(if (0 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 8 0 k*codeTrapDeletionSelector 8 k j)=
      ∑ k,codeTrapDeletionRelation 8 0 k*codeTrapDeletedMatrix 8 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_8_1 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 8*(codeTrapDeletionDenom 8*(if (1 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 8 1 k*codeTrapDeletionSelector 8 k j)=
      ∑ k,codeTrapDeletionRelation 8 1 k*codeTrapDeletedMatrix 8 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_8_2 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 8*(codeTrapDeletionDenom 8*(if (2 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 8 2 k*codeTrapDeletionSelector 8 k j)=
      ∑ k,codeTrapDeletionRelation 8 2 k*codeTrapDeletedMatrix 8 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_8_3 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 8*(codeTrapDeletionDenom 8*(if (3 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 8 3 k*codeTrapDeletionSelector 8 k j)=
      ∑ k,codeTrapDeletionRelation 8 3 k*codeTrapDeletedMatrix 8 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_8_4 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 8*(codeTrapDeletionDenom 8*(if (4 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 8 4 k*codeTrapDeletionSelector 8 k j)=
      ∑ k,codeTrapDeletionRelation 8 4 k*codeTrapDeletedMatrix 8 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_8_5 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 8*(codeTrapDeletionDenom 8*(if (5 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 8 5 k*codeTrapDeletionSelector 8 k j)=
      ∑ k,codeTrapDeletionRelation 8 5 k*codeTrapDeletedMatrix 8 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_8_6 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 8*(codeTrapDeletionDenom 8*(if (6 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 8 6 k*codeTrapDeletionSelector 8 k j)=
      ∑ k,codeTrapDeletionRelation 8 6 k*codeTrapDeletedMatrix 8 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_8_7 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 8*(codeTrapDeletionDenom 8*(if (7 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 8 7 k*codeTrapDeletionSelector 8 k j)=
      ∑ k,codeTrapDeletionRelation 8 7 k*codeTrapDeletedMatrix 8 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_8_8 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 8*(codeTrapDeletionDenom 8*(if (8 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 8 8 k*codeTrapDeletionSelector 8 k j)=
      ∑ k,codeTrapDeletionRelation 8 8 k*codeTrapDeletedMatrix 8 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_8_9 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 8*(codeTrapDeletionDenom 8*(if (9 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 8 9 k*codeTrapDeletionSelector 8 k j)=
      ∑ k,codeTrapDeletionRelation 8 9 k*codeTrapDeletedMatrix 8 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_8_10 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 8*(codeTrapDeletionDenom 8*(if (10 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 8 10 k*codeTrapDeletionSelector 8 k j)=
      ∑ k,codeTrapDeletionRelation 8 10 k*codeTrapDeletedMatrix 8 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_8_11 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 8*(codeTrapDeletionDenom 8*(if (11 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 8 11 k*codeTrapDeletionSelector 8 k j)=
      ∑ k,codeTrapDeletionRelation 8 11 k*codeTrapDeletedMatrix 8 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_8_12 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 8*(codeTrapDeletionDenom 8*(if (12 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 8 12 k*codeTrapDeletionSelector 8 k j)=
      ∑ k,codeTrapDeletionRelation 8 12 k*codeTrapDeletedMatrix 8 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_8_13 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 8*(codeTrapDeletionDenom 8*(if (13 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 8 13 k*codeTrapDeletionSelector 8 k j)=
      ∑ k,codeTrapDeletionRelation 8 13 k*codeTrapDeletedMatrix 8 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_8_14 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 8*(codeTrapDeletionDenom 8*(if (14 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 8 14 k*codeTrapDeletionSelector 8 k j)=
      ∑ k,codeTrapDeletionRelation 8 14 k*codeTrapDeletedMatrix 8 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_8_15 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 8*(codeTrapDeletionDenom 8*(if (15 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 8 15 k*codeTrapDeletionSelector 8 k j)=
      ∑ k,codeTrapDeletionRelation 8 15 k*codeTrapDeletedMatrix 8 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_8_16 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 8*(codeTrapDeletionDenom 8*(if (16 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 8 16 k*codeTrapDeletionSelector 8 k j)=
      ∑ k,codeTrapDeletionRelation 8 16 k*codeTrapDeletedMatrix 8 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_8_17 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 8*(codeTrapDeletionDenom 8*(if (17 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 8 17 k*codeTrapDeletionSelector 8 k j)=
      ∑ k,codeTrapDeletionRelation 8 17 k*codeTrapDeletedMatrix 8 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_8_18 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 8*(codeTrapDeletionDenom 8*(if (18 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 8 18 k*codeTrapDeletionSelector 8 k j)=
      ∑ k,codeTrapDeletionRelation 8 18 k*codeTrapDeletedMatrix 8 k j := by
  decide +kernel

theorem codeTrapDeleteRelation_8_19 : ∀ j : Fin 20,
    codeTrapDeletionMultiplier 8*(codeTrapDeletionDenom 8*(if (19 : Fin 20)=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis 8 19 k*codeTrapDeletionSelector 8 k j)=
      ∑ k,codeTrapDeletionRelation 8 19 k*codeTrapDeletedMatrix 8 k j := by
  decide +kernel

end CompletionTheory
