/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapOptimalLoss
public import CompletionTheory.AffineFiberRepair
@[expose] public section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory

noncomputable def trapRealIntegerEncoding (H : Matrix (Fin 20) (Fin 20) ℝ) :
    Matrix (Fin 20) (Fin 20) ℤ := by
  classical
  exact fun i j => if H i j=1 then 1 else -1

theorem trapRealIntegerEncoding_cast (H : Matrix (Fin 20) (Fin 20) ℝ) (hs : IsSignMatrix H) :
    ∀ i j,(trapRealIntegerEncoding H i j : ℝ)=H i j := by
  intro i j
  rcases hs i j with h|h <;> norm_num [trapRealIntegerEncoding,h]

theorem trapRealIntegerEncoding_hadamard (H : Matrix (Fin 20) (Fin 20) ℝ)
    (hH : IsHadamard H) : trapIntegerHadamard (trapRealIntegerEncoding H) := by
  constructor
  · intro i j
    unfold trapRealIntegerEncoding
    split <;> simp
  · intro i j
    have hh := congrArg (fun M : Matrix (Fin 20) (Fin 20) ℝ => M i j) hH.2
    change (∑ k,H i k*H j k)=20*(if i=j then 1 else 0) at hh
    have hs : (∑ k,(trapRealIntegerEncoding H i k : ℝ)*(trapRealIntegerEncoding H j k : ℝ))=
        if i=j then 20 else 0 := by
      simpa only [trapRealIntegerEncoding_cast H hH.1,mul_ite,mul_one,mul_zero] using hh
    by_cases hij : i=j
    · have hs' : (∑ k,(trapRealIntegerEncoding H i k : ℝ)*(trapRealIntegerEncoding H j k : ℝ))=20 := by simpa [hij] using hs
      have hz : (∑ k,trapRealIntegerEncoding H i k*trapRealIntegerEncoding H j k)=20 := by exact_mod_cast hs'
      simpa [hij] using hz
    · have hs' : (∑ k,(trapRealIntegerEncoding H i k : ℝ)*(trapRealIntegerEncoding H j k : ℝ))=0 := by simpa [hij] using hs
      have hz : (∑ k,trapRealIntegerEncoding H i k*trapRealIntegerEncoding H j k)=0 := by exact_mod_cast hs'
      simpa [hij] using hz

noncomputable def trapRetainedOldRealClasses (H : Matrix (Fin 20) (Fin 20) ℝ) : Finset (Fin 12) := by
  classical
  exact Finset.univ.filter (fun i => ∃ j : Fin 20,H j=trapOldRealMatrix i ∨ H j= -trapOldRealMatrix i)

noncomputable def trapOldRealRowLoss (H : Matrix (Fin 20) (Fin 20) ℝ) : ℕ :=
  12-(trapRetainedOldRealClasses H).card

theorem trapOldIntegerMatrix_cast (i : Fin 12) (j : Fin 20) :
    (codeTrapOldIntegerMatrix i j : ℝ)=trapOldRealMatrix i j := rfl

theorem trapRealRetained_subset_integer (H : Matrix (Fin 20) (Fin 20) ℝ) (hs : IsSignMatrix H) :
    trapRetainedOldRealClasses H⊆trapRetainedOldClasses (trapRealIntegerEncoding H) := by
  classical
  intro i hi
  obtain ⟨j,hj⟩ := (Finset.mem_filter.mp hi).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,j,?_⟩
  rcases hj with hj|hj
  · left
    funext k
    apply Int.cast_injective (α := ℝ)
    calc
      (trapRealIntegerEncoding H j k : ℝ)=H j k := trapRealIntegerEncoding_cast H hs j k
      _=trapOldRealMatrix i k := congrFun hj k
      _=(codeTrapOldIntegerMatrix i k : ℝ) := (trapOldIntegerMatrix_cast i k).symm
  · right
    funext k
    apply Int.cast_injective (α := ℝ)
    have hc : (trapRealIntegerEncoding H j k : ℝ)= -(codeTrapOldIntegerMatrix i k : ℝ) := by
      calc
        (trapRealIntegerEncoding H j k : ℝ)=H j k := trapRealIntegerEncoding_cast H hs j k
        _= -trapOldRealMatrix i k := by simpa only [Pi.neg_apply] using congrFun hj k
        _= -(codeTrapOldIntegerMatrix i k : ℝ) := by rw [trapOldIntegerMatrix_cast]
    simpa only [Int.cast_neg,Pi.neg_apply] using hc

theorem trapRetainedOldRealClasses_bound (H : Matrix (Fin 20) (Fin 20) ℝ)
    (hH : IsHadamard H) : (trapRetainedOldRealClasses H).card≤10 :=
  le_trans (Finset.card_le_card (trapRealRetained_subset_integer H hH.1))
    (trapRetainedOldClasses_bound _ (trapRealIntegerEncoding_hadamard H hH))

theorem trapEveryRealCompletion_loses_two (H : Matrix (Fin 20) (Fin 20) ℝ)
    (hH : Matrix.IsHadamard H) : 2≤trapOldRealRowLoss H := by
  have hh := trapRetainedOldRealClasses_bound H (mathlib_hadamard_partial hH)
  unfold trapOldRealRowLoss
  omega

theorem trapCompletedReal_retention (i : Fin 10) (j : Fin 20) :
    trapCompletedRealMatrix (trapTenToTwenty i) j=trapOldRealMatrix (trapRetainedOldIndex i) j := by
  exact congrArg (fun z : ℤ => (z : ℝ)) ((trapRetainedOldIndex_properties i).2.2 j)

theorem trapCompletedReal_retains_ten : 10≤(trapRetainedOldRealClasses trapCompletedRealMatrix).card := by
  classical
  have hsub : Finset.univ.image trapRetainedOldIndex⊆trapRetainedOldRealClasses trapCompletedRealMatrix := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,trapTenToTwenty j,Or.inl ?_⟩
    funext k
    exact trapCompletedReal_retention j k
  have hc := Finset.card_le_card hsub
  simpa only [Finset.card_image_of_injective _ trapRetainedOldIndex_injective,
    Finset.card_univ,Fintype.card_fin] using hc

theorem trapCompleted_real_old_row_loss_two : trapOldRealRowLoss trapCompletedRealMatrix=2 := by
  have hle := trapRetainedOldRealClasses_bound trapCompletedRealMatrix trapCompleted_isHadamard
  have hge := trapCompletedReal_retains_ten
  unfold trapOldRealRowLoss
  omega

theorem trapMinimum_real_old_row_loss_two :
    (∀ H : Matrix (Fin 20) (Fin 20) ℝ,Matrix.IsHadamard H → 2≤trapOldRealRowLoss H) ∧
    Matrix.IsHadamard trapCompletedRealMatrix ∧ trapOldRealRowLoss trapCompletedRealMatrix=2 :=
  ⟨trapEveryRealCompletion_loses_two,trapCompleted_mathlib_hadamard,trapCompleted_real_old_row_loss_two⟩
end CompletionTheory
