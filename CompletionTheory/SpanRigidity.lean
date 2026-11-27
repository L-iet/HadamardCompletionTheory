/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module

public import CompletionTheory.TensorExchange
public import CompletionTheory.InformationCoordinates
public import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Exact row-range confinement for span-rigid exchanges -/

@[expose] public section
namespace CompletionTheory
open Matrix

def SpanRigidThrough {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (P : Matrix ι κ ℝ) (c : ℕ) : Prop :=
  NoSignExtension P ∧ ∀ I : Finset ι, I.card ≤ c → ∀ f : κ → ℝ,
    IsCubeVector f → (∀ i, i ∉ I → ∑ j, P i j * f j = 0) →
      f ∈ Submodule.span ℝ (P '' (I : Set ι))

theorem partial_transpose_mulVec_injective {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ]
    (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) :
    Function.Injective P.transpose.mulVecLin := by
  intro x y hxy
  have hn : (Fintype.card κ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h := congrArg (fun z => P.mulVec z) hxy
  change P.mulVec (P.transpose.mulVec x) = P.mulVec (P.transpose.mulVec y) at h
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP.2] at h
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec] at h
  funext i
  exact mul_left_cancel₀ hn (congrFun h i)

theorem row_range_family_card_le {ι κ ν : Type*}
    [Fintype ι] [Fintype κ] [Fintype ν] [DecidableEq ν] [Nonempty κ]
    (R : Matrix ι κ ℝ) (V : Matrix ν κ ℝ) (hV : IsPartialHadamard V)
    (hmem : ∀ a, V a ∈ LinearMap.range R.transpose.mulVecLin) :
    Fintype.card ν ≤ Fintype.card ι := by
  have hinc : LinearMap.range V.transpose.mulVecLin ≤ LinearMap.range R.transpose.mulVecLin := by
    rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro x ⟨a, rfl⟩
    exact hmem a
  have hfirst := Submodule.finrank_mono hinc
  have hlast := R.transpose.mulVecLin.finrank_range_le
  have hdim : Module.finrank ℝ (LinearMap.range V.transpose.mulVecLin) = Fintype.card ν := by
    rw [LinearMap.finrank_range_of_inj (partial_transpose_mulVec_injective V hV)]
    simp
  rw [hdim] at hfirst
  exact hfirst.trans (by simpa using hlast)

theorem row_range_restrict_of_orthogonal {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ]
    (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (D : Finset ι) (f : κ → ℝ)
    (hf : f ∈ LinearMap.range P.transpose.mulVecLin)
    (horth : ∀ i, i ∉ D → ∑ j, P i j * f j = 0) :
    f ∈ LinearMap.range (P.submatrix (fun i : D => i.val) id).transpose.mulVecLin := by
  classical
  obtain ⟨x, hx⟩ := hf
  have hn : (Fintype.card κ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcoeff : P.mulVec f = (Fintype.card κ : ℝ) • x := by
    rw [← hx]
    change P.mulVec (P.transpose.mulVec x) = _
    rw [Matrix.mulVec_mulVec, hP.2, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hxzero (i : ι) (hi : i ∉ D) : x i = 0 := by
    have h := congrFun hcoeff i
    change (∑ j, P i j * f j) = (Fintype.card κ : ℝ) * x i at h
    rw [horth i hi] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hn
  refine ⟨fun i : D => x i.val, ?_⟩
  funext j
  change (∑ i : D, P i.val j * x i.val) = f j
  calc
    _ = ∑ i ∈ D, P i j * x i := Finset.sum_coe_sort D (fun i => P i j * x i)
    _ = ∑ i : ι, P i j * x i := Finset.sum_subset (Finset.subset_univ D)
      (fun i _ hi => by rw [hxzero i hi, mul_zero])
    _ = f j := congrFun hx j

theorem hadamard_transpose_mulVec_surjective {τ : Type*}
    [Fintype τ] [DecidableEq τ] [Nonempty τ] (H : Matrix τ τ ℝ) (hH : IsHadamard H) :
    Function.Surjective H.transpose.mulVecLin := by
  have hn : (Fintype.card τ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc : H.transpose * H = (Fintype.card τ : ℝ) • 1 := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using (isHadamard_mathlib hH).conjTranspose_mul
  let M : Matrix τ τ ℝ := (Fintype.card τ : ℝ)⁻¹ • H
  have hHM : H.transpose * M = 1 := by
    simp only [M, Matrix.mul_smul, hc, smul_smul, inv_mul_cancel₀ hn, one_smul]
  intro y
  refine ⟨M.mulVec y, ?_⟩
  change H.transpose.mulVec (M.mulVec y) = y
  rw [Matrix.mulVec_mulVec, hHM, Matrix.one_mulVec]

theorem tensor_row_range_of_columns {ι κ τ : Type*}
    [Fintype ι] [Fintype κ] [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (P : Matrix ι κ ℝ) (H : Matrix τ τ ℝ) (hH : IsHadamard H) (f : (κ × τ) → ℝ)
    (hcol : ∀ b : τ, (fun j => f (j, b)) ∈ LinearMap.range P.transpose.mulVecLin) :
    f ∈ LinearMap.range (tensorFrame P H).transpose.mulVecLin := by
  classical
  choose y hy using hcol
  have hs := hadamard_transpose_mulVec_surjective H hH
  have hex (i : ι) : ∃ z : τ → ℝ, H.transpose.mulVec z = fun b => y b i := hs _
  choose z hz using hex
  refine ⟨fun i : ι × τ => z i.1 i.2, ?_⟩
  funext v
  rcases v with ⟨j, b⟩
  change (∑ i : ι × τ, (P i.1 j * H i.2 b) * z i.1 i.2) = f (j, b)
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ i : ι, P i j * ∑ a : τ, H a b * z i a := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = ∑ i : ι, P i j * y b i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [show (∑ a : τ, H a b * z i a) = y b i from congrFun (hz i) b]
    _ = f (j, b) := congrFun (hy b) j

theorem tensor_fiber_orthogonal_columns {ι κ τ : Type*}
    [Fintype κ] [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (P : Matrix ι κ ℝ) (H : Matrix τ τ ℝ) (hH : IsHadamard H)
    (f : (κ × τ) → ℝ) (i : ι)
    (horth : ∀ a : τ, ∑ j : κ × τ, tensorFrame P H (i, a) j * f j = 0) :
    ∀ b : τ, (∑ j, P i j * f (j, b)) = 0 := by
  classical
  have hn : (Fintype.card τ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  let M : Matrix τ τ ℝ := (Fintype.card τ : ℝ)⁻¹ • H.transpose
  have hHM : H * M = 1 := by simp [M, hH.2, smul_smul, hn]
  have hMH : M * H = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hHM
  let v : τ → ℝ := fun b => ∑ j, P i j * f (j, b)
  have hv : H.mulVec v = 0 := by
    ext a
    change (∑ b, H a b * ∑ j, P i j * f (j, b)) = 0
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ j, ∑ b, (P i j * H a b) * f (j, b) := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro b hb
        ring
      _ = 0 := by simpa only [tensorFrame, Fintype.sum_prod_type] using horth a
  have hv0 : v = 0 := by
    have h := congrArg (fun x => M.mulVec x) hv
    simpa only [Matrix.mulVec_mulVec, hMH, Matrix.one_mulVec, Matrix.mulVec_zero] using h
  intro b
  exact congrFun hv0 b

theorem span_rigid_tensor_candidate_confined {ι κ τ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ]
    [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P)
    (H : Matrix τ τ ℝ) (hH : IsHadamard H) (c : ℕ) (hrigid : SpanRigidThrough P c)
    (D : Finset (ι × τ)) (hD : D.card ≤ c) (f : (κ × τ) → ℝ) (hf : IsCubeVector f)
    (horth : ∀ i, i ∉ D → ∑ j, tensorFrame P H i j * f j = 0) :
    f ∈ LinearMap.range
      ((tensorFrame P H).submatrix (fun i : D => i.val) id).transpose.mulVecLin := by
  classical
  let I : Finset ι := D.image Prod.fst
  have hI : I.card ≤ c := Finset.card_image_le.trans hD
  have hcol (b : τ) : (fun j => f (j, b)) ∈ LinearMap.range P.transpose.mulVecLin := by
    have hcols : ∀ i, i ∉ I → ∑ j, P i j * f (j, b) = 0 := by
      intro i hi
      apply tensor_fiber_orthogonal_columns P H hH f i ?_ b
      intro a
      apply horth (i, a)
      intro hm
      exact hi (Finset.mem_image.mpr ⟨(i, a), hm, rfl⟩)
    have hspan := hrigid.2 I hI (fun j => f (j, b)) (fun j => hf (j, b)) hcols
    rw [Matrix.range_mulVecLin]
    change (fun j => f (j, b)) ∈ Submodule.span ℝ (Set.range P)
    apply (Submodule.span_mono (show P '' (I : Set ι) ⊆ Set.range P from ?_)) hspan
    rintro x ⟨i, hi, rfl⟩
    exact ⟨i, rfl⟩
  exact row_range_restrict_of_orthogonal (tensorFrame P H) (tensorFrame_partialHadamard P H hP hH)
    D f (tensor_row_range_of_columns P H hH f hcol) horth

theorem span_rigidity_excludes_tensor_exchange {ι κ τ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ]
    [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P)
    (H : Matrix τ τ ℝ) (hH : IsHadamard H) (c : ℕ) (hrigid : SpanRigidThrough P c)
    (k : ℕ) (hk : k ≤ c) : ¬ HasAugmentingExchange (tensorFrame P H) k := by
  classical
  rintro ⟨D, hD, V, hV, horth⟩
  have hmem (a : Fin (k + 1)) : V a ∈ LinearMap.range
      ((tensorFrame P H).submatrix (fun i : D => i.val) id).transpose.mulVecLin := by
    apply span_rigid_tensor_candidate_confined P hP H hH c hrigid D (by omega)
      (V a) (hV.1 a)
    intro i hi
    exact horth i hi a
  have hbound := row_range_family_card_le
    ((tensorFrame P H).submatrix (fun i : D => i.val) id) V hV hmem
  simp only [Fintype.card_fin, Fintype.card_coe] at hbound
  omega

theorem span_rigidity_tensor_cost_lower {ι κ τ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ]
    [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P)
    (H : Matrix τ τ ℝ) (hH : IsHadamard H) (c : ℕ) (hrigid : SpanRigidThrough P c) :
    (c : WithTop ℕ) < exchangeCost (tensorFrame P H) := by
  apply lt_of_not_ge
  intro hcost
  obtain ⟨k, hk, hx⟩ := (exchangeCost_le_iff (tensorFrame P H) c).mp hcost
  exact span_rigidity_excludes_tensor_exchange P hP H hH c hrigid k hk hx

end CompletionTheory
