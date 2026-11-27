/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapDeletionRelation_0
public import CompletionCodeTrap.CodeTrapDeletionRelation_1
public import CompletionCodeTrap.CodeTrapDeletionRelation_2
public import CompletionCodeTrap.CodeTrapDeletionRelation_3
public import CompletionCodeTrap.CodeTrapDeletionRelation_4
public import CompletionCodeTrap.CodeTrapDeletionRelation_5
public import CompletionCodeTrap.CodeTrapDeletionRelation_6
public import CompletionCodeTrap.CodeTrapDeletionRelation_7
public import CompletionCodeTrap.CodeTrapDeletionRelation_8
public import CompletionCodeTrap.CodeTrapDeletionRelation_9
public import CompletionCodeTrap.CodeTrapDeletionRelation_10
public import CompletionCodeTrap.CodeTrapDeletionRelation_11
@[expose] public section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
namespace CompletionTheory
theorem codeTrapDeleted_relation_entries : ∀ (d : Fin 12) (i j : Fin 20),
    codeTrapDeletionMultiplier d*(codeTrapDeletionDenom d.val*(if i=j then (1 : ℤ) else 0)-
      ∑ k,codeTrapDeletionBasis d i k*codeTrapDeletionSelector d k j)=
      ∑ k,codeTrapDeletionRelation d i k*codeTrapDeletedMatrix d k j := by
  intro d i
  fin_cases d <;> fin_cases i
  · exact codeTrapDeleteRelation_0_0
  · exact codeTrapDeleteRelation_0_1
  · exact codeTrapDeleteRelation_0_2
  · exact codeTrapDeleteRelation_0_3
  · exact codeTrapDeleteRelation_0_4
  · exact codeTrapDeleteRelation_0_5
  · exact codeTrapDeleteRelation_0_6
  · exact codeTrapDeleteRelation_0_7
  · exact codeTrapDeleteRelation_0_8
  · exact codeTrapDeleteRelation_0_9
  · exact codeTrapDeleteRelation_0_10
  · exact codeTrapDeleteRelation_0_11
  · exact codeTrapDeleteRelation_0_12
  · exact codeTrapDeleteRelation_0_13
  · exact codeTrapDeleteRelation_0_14
  · exact codeTrapDeleteRelation_0_15
  · exact codeTrapDeleteRelation_0_16
  · exact codeTrapDeleteRelation_0_17
  · exact codeTrapDeleteRelation_0_18
  · exact codeTrapDeleteRelation_0_19
  · exact codeTrapDeleteRelation_1_0
  · exact codeTrapDeleteRelation_1_1
  · exact codeTrapDeleteRelation_1_2
  · exact codeTrapDeleteRelation_1_3
  · exact codeTrapDeleteRelation_1_4
  · exact codeTrapDeleteRelation_1_5
  · exact codeTrapDeleteRelation_1_6
  · exact codeTrapDeleteRelation_1_7
  · exact codeTrapDeleteRelation_1_8
  · exact codeTrapDeleteRelation_1_9
  · exact codeTrapDeleteRelation_1_10
  · exact codeTrapDeleteRelation_1_11
  · exact codeTrapDeleteRelation_1_12
  · exact codeTrapDeleteRelation_1_13
  · exact codeTrapDeleteRelation_1_14
  · exact codeTrapDeleteRelation_1_15
  · exact codeTrapDeleteRelation_1_16
  · exact codeTrapDeleteRelation_1_17
  · exact codeTrapDeleteRelation_1_18
  · exact codeTrapDeleteRelation_1_19
  · exact codeTrapDeleteRelation_2_0
  · exact codeTrapDeleteRelation_2_1
  · exact codeTrapDeleteRelation_2_2
  · exact codeTrapDeleteRelation_2_3
  · exact codeTrapDeleteRelation_2_4
  · exact codeTrapDeleteRelation_2_5
  · exact codeTrapDeleteRelation_2_6
  · exact codeTrapDeleteRelation_2_7
  · exact codeTrapDeleteRelation_2_8
  · exact codeTrapDeleteRelation_2_9
  · exact codeTrapDeleteRelation_2_10
  · exact codeTrapDeleteRelation_2_11
  · exact codeTrapDeleteRelation_2_12
  · exact codeTrapDeleteRelation_2_13
  · exact codeTrapDeleteRelation_2_14
  · exact codeTrapDeleteRelation_2_15
  · exact codeTrapDeleteRelation_2_16
  · exact codeTrapDeleteRelation_2_17
  · exact codeTrapDeleteRelation_2_18
  · exact codeTrapDeleteRelation_2_19
  · exact codeTrapDeleteRelation_3_0
  · exact codeTrapDeleteRelation_3_1
  · exact codeTrapDeleteRelation_3_2
  · exact codeTrapDeleteRelation_3_3
  · exact codeTrapDeleteRelation_3_4
  · exact codeTrapDeleteRelation_3_5
  · exact codeTrapDeleteRelation_3_6
  · exact codeTrapDeleteRelation_3_7
  · exact codeTrapDeleteRelation_3_8
  · exact codeTrapDeleteRelation_3_9
  · exact codeTrapDeleteRelation_3_10
  · exact codeTrapDeleteRelation_3_11
  · exact codeTrapDeleteRelation_3_12
  · exact codeTrapDeleteRelation_3_13
  · exact codeTrapDeleteRelation_3_14
  · exact codeTrapDeleteRelation_3_15
  · exact codeTrapDeleteRelation_3_16
  · exact codeTrapDeleteRelation_3_17
  · exact codeTrapDeleteRelation_3_18
  · exact codeTrapDeleteRelation_3_19
  · exact codeTrapDeleteRelation_4_0
  · exact codeTrapDeleteRelation_4_1
  · exact codeTrapDeleteRelation_4_2
  · exact codeTrapDeleteRelation_4_3
  · exact codeTrapDeleteRelation_4_4
  · exact codeTrapDeleteRelation_4_5
  · exact codeTrapDeleteRelation_4_6
  · exact codeTrapDeleteRelation_4_7
  · exact codeTrapDeleteRelation_4_8
  · exact codeTrapDeleteRelation_4_9
  · exact codeTrapDeleteRelation_4_10
  · exact codeTrapDeleteRelation_4_11
  · exact codeTrapDeleteRelation_4_12
  · exact codeTrapDeleteRelation_4_13
  · exact codeTrapDeleteRelation_4_14
  · exact codeTrapDeleteRelation_4_15
  · exact codeTrapDeleteRelation_4_16
  · exact codeTrapDeleteRelation_4_17
  · exact codeTrapDeleteRelation_4_18
  · exact codeTrapDeleteRelation_4_19
  · exact codeTrapDeleteRelation_5_0
  · exact codeTrapDeleteRelation_5_1
  · exact codeTrapDeleteRelation_5_2
  · exact codeTrapDeleteRelation_5_3
  · exact codeTrapDeleteRelation_5_4
  · exact codeTrapDeleteRelation_5_5
  · exact codeTrapDeleteRelation_5_6
  · exact codeTrapDeleteRelation_5_7
  · exact codeTrapDeleteRelation_5_8
  · exact codeTrapDeleteRelation_5_9
  · exact codeTrapDeleteRelation_5_10
  · exact codeTrapDeleteRelation_5_11
  · exact codeTrapDeleteRelation_5_12
  · exact codeTrapDeleteRelation_5_13
  · exact codeTrapDeleteRelation_5_14
  · exact codeTrapDeleteRelation_5_15
  · exact codeTrapDeleteRelation_5_16
  · exact codeTrapDeleteRelation_5_17
  · exact codeTrapDeleteRelation_5_18
  · exact codeTrapDeleteRelation_5_19
  · exact codeTrapDeleteRelation_6_0
  · exact codeTrapDeleteRelation_6_1
  · exact codeTrapDeleteRelation_6_2
  · exact codeTrapDeleteRelation_6_3
  · exact codeTrapDeleteRelation_6_4
  · exact codeTrapDeleteRelation_6_5
  · exact codeTrapDeleteRelation_6_6
  · exact codeTrapDeleteRelation_6_7
  · exact codeTrapDeleteRelation_6_8
  · exact codeTrapDeleteRelation_6_9
  · exact codeTrapDeleteRelation_6_10
  · exact codeTrapDeleteRelation_6_11
  · exact codeTrapDeleteRelation_6_12
  · exact codeTrapDeleteRelation_6_13
  · exact codeTrapDeleteRelation_6_14
  · exact codeTrapDeleteRelation_6_15
  · exact codeTrapDeleteRelation_6_16
  · exact codeTrapDeleteRelation_6_17
  · exact codeTrapDeleteRelation_6_18
  · exact codeTrapDeleteRelation_6_19
  · exact codeTrapDeleteRelation_7_0
  · exact codeTrapDeleteRelation_7_1
  · exact codeTrapDeleteRelation_7_2
  · exact codeTrapDeleteRelation_7_3
  · exact codeTrapDeleteRelation_7_4
  · exact codeTrapDeleteRelation_7_5
  · exact codeTrapDeleteRelation_7_6
  · exact codeTrapDeleteRelation_7_7
  · exact codeTrapDeleteRelation_7_8
  · exact codeTrapDeleteRelation_7_9
  · exact codeTrapDeleteRelation_7_10
  · exact codeTrapDeleteRelation_7_11
  · exact codeTrapDeleteRelation_7_12
  · exact codeTrapDeleteRelation_7_13
  · exact codeTrapDeleteRelation_7_14
  · exact codeTrapDeleteRelation_7_15
  · exact codeTrapDeleteRelation_7_16
  · exact codeTrapDeleteRelation_7_17
  · exact codeTrapDeleteRelation_7_18
  · exact codeTrapDeleteRelation_7_19
  · exact codeTrapDeleteRelation_8_0
  · exact codeTrapDeleteRelation_8_1
  · exact codeTrapDeleteRelation_8_2
  · exact codeTrapDeleteRelation_8_3
  · exact codeTrapDeleteRelation_8_4
  · exact codeTrapDeleteRelation_8_5
  · exact codeTrapDeleteRelation_8_6
  · exact codeTrapDeleteRelation_8_7
  · exact codeTrapDeleteRelation_8_8
  · exact codeTrapDeleteRelation_8_9
  · exact codeTrapDeleteRelation_8_10
  · exact codeTrapDeleteRelation_8_11
  · exact codeTrapDeleteRelation_8_12
  · exact codeTrapDeleteRelation_8_13
  · exact codeTrapDeleteRelation_8_14
  · exact codeTrapDeleteRelation_8_15
  · exact codeTrapDeleteRelation_8_16
  · exact codeTrapDeleteRelation_8_17
  · exact codeTrapDeleteRelation_8_18
  · exact codeTrapDeleteRelation_8_19
  · exact codeTrapDeleteRelation_9_0
  · exact codeTrapDeleteRelation_9_1
  · exact codeTrapDeleteRelation_9_2
  · exact codeTrapDeleteRelation_9_3
  · exact codeTrapDeleteRelation_9_4
  · exact codeTrapDeleteRelation_9_5
  · exact codeTrapDeleteRelation_9_6
  · exact codeTrapDeleteRelation_9_7
  · exact codeTrapDeleteRelation_9_8
  · exact codeTrapDeleteRelation_9_9
  · exact codeTrapDeleteRelation_9_10
  · exact codeTrapDeleteRelation_9_11
  · exact codeTrapDeleteRelation_9_12
  · exact codeTrapDeleteRelation_9_13
  · exact codeTrapDeleteRelation_9_14
  · exact codeTrapDeleteRelation_9_15
  · exact codeTrapDeleteRelation_9_16
  · exact codeTrapDeleteRelation_9_17
  · exact codeTrapDeleteRelation_9_18
  · exact codeTrapDeleteRelation_9_19
  · exact codeTrapDeleteRelation_10_0
  · exact codeTrapDeleteRelation_10_1
  · exact codeTrapDeleteRelation_10_2
  · exact codeTrapDeleteRelation_10_3
  · exact codeTrapDeleteRelation_10_4
  · exact codeTrapDeleteRelation_10_5
  · exact codeTrapDeleteRelation_10_6
  · exact codeTrapDeleteRelation_10_7
  · exact codeTrapDeleteRelation_10_8
  · exact codeTrapDeleteRelation_10_9
  · exact codeTrapDeleteRelation_10_10
  · exact codeTrapDeleteRelation_10_11
  · exact codeTrapDeleteRelation_10_12
  · exact codeTrapDeleteRelation_10_13
  · exact codeTrapDeleteRelation_10_14
  · exact codeTrapDeleteRelation_10_15
  · exact codeTrapDeleteRelation_10_16
  · exact codeTrapDeleteRelation_10_17
  · exact codeTrapDeleteRelation_10_18
  · exact codeTrapDeleteRelation_10_19
  · exact codeTrapDeleteRelation_11_0
  · exact codeTrapDeleteRelation_11_1
  · exact codeTrapDeleteRelation_11_2
  · exact codeTrapDeleteRelation_11_3
  · exact codeTrapDeleteRelation_11_4
  · exact codeTrapDeleteRelation_11_5
  · exact codeTrapDeleteRelation_11_6
  · exact codeTrapDeleteRelation_11_7
  · exact codeTrapDeleteRelation_11_8
  · exact codeTrapDeleteRelation_11_9
  · exact codeTrapDeleteRelation_11_10
  · exact codeTrapDeleteRelation_11_11
  · exact codeTrapDeleteRelation_11_12
  · exact codeTrapDeleteRelation_11_13
  · exact codeTrapDeleteRelation_11_14
  · exact codeTrapDeleteRelation_11_15
  · exact codeTrapDeleteRelation_11_16
  · exact codeTrapDeleteRelation_11_17
  · exact codeTrapDeleteRelation_11_18
  · exact codeTrapDeleteRelation_11_19

theorem codeTrapDeleted_matrix_relation (d : Fin 12) :
    codeTrapDeletionMultiplier d •
      (codeTrapDeletionDenom d.val • (1 : Matrix (Fin 20) (Fin 20) ℤ)-
        codeTrapDeletionBasis d*codeTrapDeletionSelector d)=
      codeTrapDeletionRelation d*codeTrapDeletedMatrix d := by
  apply Matrix.ext
  intro i j
  change codeTrapDeletionMultiplier d*(codeTrapDeletionDenom d.val*(if i=j then (1 : ℤ) else 0)-
    ∑ k,codeTrapDeletionBasis d i k*codeTrapDeletionSelector d k j)=
    ∑ k,codeTrapDeletionRelation d i k*codeTrapDeletedMatrix d k j
  exact codeTrapDeleted_relation_entries d i j

theorem codeTrapDeleted_reconstruct (d : Fin 12) (z : Fin 20 → ℤ)
    (hker : (codeTrapDeletedMatrix d).mulVec z=0) :
    ∀ i,codeTrapDeletionDenom d.val*z i=
      (codeTrapDeletionBasis d).mulVec (fun k => z (codeTrapDeletionFree d k)) i := by
  have hh := congrArg (fun M : Matrix (Fin 20) (Fin 20) ℤ => M.mulVec z)
    (codeTrapDeleted_matrix_relation d)
  simp only [Matrix.smul_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec,hker,Matrix.mulVec_zero] at hh
  rw [codeTrapDeletionSelector_mulVec] at hh
  intro i
  have hi := congrFun hh i
  change codeTrapDeletionMultiplier d*(codeTrapDeletionDenom d.val*z i-
    (codeTrapDeletionBasis d).mulVec (fun k => z (codeTrapDeletionFree d k)) i)=0 at hi
  exact sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left (codeTrapDeletionMultiplier_nonzero d))
end CompletionTheory
