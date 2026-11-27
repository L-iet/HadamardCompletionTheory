/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionBloch.BlochAlgebra
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.SpecialFunctions.Sqrt
@[expose] public section
namespace CompletionTheory.Bloch
noncomputable section
open scoped BigOperators

theorem dot3_positive {s : Fin 3 → ℝ} (hs : s≠0) : 0<dot3 s s := by
  have h0 := sq_nonneg (s 0)
  have h1 := sq_nonneg (s 1)
  have h2 := sq_nonneg (s 2)
  have he : dot3 s s=(s 0)^2+(s 1)^2+(s 2)^2 := by simp [dot3,Fin.sum_univ_succ]; ring
  by_contra h
  rw [he] at h
  have hz0 : s 0=0 := sq_eq_zero_iff.mp (by nlinarith : (s 0)^2=0)
  have hz1 : s 1=0 := sq_eq_zero_iff.mp (by nlinarith : (s 1)^2=0)
  have hz2 : s 2=0 := sq_eq_zero_iff.mp (by nlinarith : (s 2)^2=0)
  apply hs
  funext i
  fin_cases i <;> simp [hz0,hz1,hz2]

theorem real_gram_rank_axis_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι (Fin 3) ℝ) :
    (M*M.transpose).rank≤2 ↔
      ∃ s : Fin 3 → ℝ,dot3 s s=1 ∧ ∀ i,dot3 (M i) s=0 := by
  classical
  rw [Matrix.rank_self_mul_transpose]
  have hdim := M.mulVecLin.finrank_range_add_finrank_ker
  have hd : M.rank+Module.finrank ℝ (LinearMap.ker M.mulVecLin)=3 := by
    simpa only [Matrix.rank,Module.finrank_pi,Module.finrank_self,Fintype.card_fin,mul_one] using hdim
  constructor
  · intro hrank
    have hpos : 0<Module.finrank ℝ (LinearMap.ker M.mulVecLin) := by omega
    obtain ⟨v,hv⟩ := (Module.finrank_pos_iff_exists_ne_zero (R:=ℝ) (M:=LinearMap.ker M.mulVecLin)).mp hpos
    have hv0 : (v.val : Fin 3 → ℝ)≠0 := by
      intro h
      apply hv
      exact Subtype.ext h
    have hnorm : 0<dot3 v.val v.val := dot3_positive hv0
    let s : Fin 3 → ℝ := fun j => v.val j/Real.sqrt (dot3 v.val v.val)
    refine ⟨s,?_,?_⟩
    · simp only [dot3,s,div_mul_div_comm,←Finset.sum_div]
      change dot3 v.val v.val/(Real.sqrt (dot3 v.val v.val)*Real.sqrt (dot3 v.val v.val))=1
      rw [Real.mul_self_sqrt hnorm.le]
      exact div_self hnorm.ne'
    · intro i
      have hh : dot3 (M i) v.val=0 := by
        change M.mulVec v.val i=0
        exact congrFun v.property i
      simp only [dot3,s,←mul_div_assoc,←Finset.sum_div]
      change dot3 (M i) v.val / Real.sqrt (dot3 v.val v.val)=0
      rw [hh,zero_div]
  · rintro ⟨s,hs,horth⟩
    have hs0 : s≠0 := by intro h; subst s; simp [dot3] at hs
    have hmem : M.mulVecLin s=0 := by
      ext i
      exact horth i
    have hk : (⟨s,hmem⟩ : LinearMap.ker M.mulVecLin)≠0 := by
      intro h
      exact hs0 (congrArg Subtype.val h)
    have hpos : 0<Module.finrank ℝ (LinearMap.ker M.mulVecLin) :=
      (Module.finrank_pos_iff_exists_ne_zero (R:=ℝ) (M:=LinearMap.ker M.mulVecLin)).mpr ⟨_,hk⟩
    omega

end
end CompletionTheory.Bloch
