/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionLattice.RationalAlternative
public import CompletionTheory.ExchangeBudget
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory
noncomputable section
open scoped BigOperators Matrix

theorem real_row_span_zero_budget {r N : ℕ}
    (P : Matrix (Fin r) (Fin N) ℝ) (hP : P*Pᵀ=(N : ℝ) • 1)
    (x : Fin N → ℤ)
    (hx : (fun j => (x j : ℝ))∈Submodule.span ℝ (Set.range P)) :
    witnessBudget P x=0 := by
  let R : Matrix (Fin N) (Fin N) ℝ := (N : ℝ) • 1-Pᵀ*P
  have hRP : R*Pᵀ=0 := by
    change ((N : ℝ) • 1-Pᵀ*P)*Pᵀ=0
    rw [Matrix.sub_mul,Matrix.smul_mul,Matrix.one_mul,Matrix.mul_assoc,hP,
      Matrix.mul_smul,Matrix.mul_one,sub_self]
  have hzero : ∀ v∈Submodule.span ℝ (Set.range P),R.mulVec v=0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨i,rfl⟩ := hv
      funext j
      have hh := congrFun (congrFun hRP j) i
      simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.zero_apply,Matrix.mulVec,dotProduct,Pi.zero_apply] using hh
    | zero => simp
    | add v w hv hw ihv ihw => rw [Matrix.mulVec_add,ihv,ihw,zero_add]
    | smul c v hv ih => rw [Matrix.mulVec_smul,ih,smul_zero]
  rw [witnessBudget_eq_residual]
  simp only [Fintype.card_fin]
  change dotProduct (fun j => (x j : ℝ)) (R.mulVec (fun j => (x j : ℝ)))=0
  rw [hzero _ hx]
  simp

theorem rational_row_span_zero_budget {r N : ℕ}
    (P : Matrix (Fin r) (Fin N) ℤ)
    (hP : ∀ i j : Fin r,(∑ k : Fin N,(P i k : ℝ)*(P j k : ℝ))=
      if i=j then (N : ℝ) else 0)
    (x : Fin N → ℤ)
    (hx : integerToRationalLinear N x∈Submodule.span ℚ
      (Set.range (fun i : Fin r => fun j : Fin N => (P i j : ℚ)))) :
    witnessBudget (fun i j => (P i j : ℝ)) x=0 := by
  let W := Submodule.span ℝ (Set.range (fun i : Fin r => fun j : Fin N => (P i j : ℝ)))
  have hcast : ∀ v∈Submodule.span ℚ (Set.range (fun i : Fin r => fun j : Fin N => (P i j : ℚ))),
      (fun j => (v j : ℝ))∈W := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨i,rfl⟩ := hv
      have he : (fun j : Fin N => ((P i j : ℚ) : ℝ))=(fun j => (P i j : ℝ)) := by
        funext j; norm_cast
      rw [he]
      exact Submodule.subset_span ⟨i,rfl⟩
    | zero =>
      have he : (fun j : Fin N => ((0 : Fin N → ℚ) j : ℝ))=(0 : Fin N → ℝ) := by
        funext j; simp only [Pi.zero_apply,Rat.cast_zero]
      rw [he]
      exact W.zero_mem
    | add v w hv hw ihv ihw =>
      convert W.add_mem ihv ihw using 1 <;> ext j <;> simp only [Pi.add_apply,Rat.cast_add]
    | smul c v hv ih =>
      have hh := W.smul_mem (c : ℝ) ih
      convert hh using 1 <;> ext j <;> simp only [Pi.smul_apply,smul_eq_mul,Rat.cast_mul]
  let Q : Matrix (Fin r) (Fin N) ℝ := fun i j => (P i j : ℝ)
  have hQ : Q*Qᵀ=(N : ℝ) • 1 := by
    ext i j
    simpa only [Q,Matrix.mul_apply,Matrix.transpose_apply,Matrix.smul_apply,Matrix.one_apply,
      smul_eq_mul,mul_ite,mul_one,mul_zero] using hP i j
  apply real_row_span_zero_budget Q hQ x
  have hh := hcast _ hx
  simpa [integerToRationalLinear] using hh

end
end CompletionTheory
