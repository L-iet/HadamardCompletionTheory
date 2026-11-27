/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module

public import CompletionTheory.HalfOverlapGeometry

/-! # Two-deletion tensor barriers from original candidate correlations -/

@[expose] public section
namespace CompletionTheory
open Matrix

def OriginalCandidate {ι κ : Type*} [Fintype κ] [DecidableEq ι]
    (P : Matrix ι κ ℝ) (I : Finset ι) (x : κ → ℝ) : Prop :=
  IsCubeVector x ∧ ∀ i, i ∉ I → ∑ j, P i j * x j = 0

def SameSignLine {κ : Type*} (x y : κ → ℝ) : Prop := x = y ∨ x = -y

def HalfOverlapCorrelationConditions {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (P : Matrix ι κ ℝ) : Prop :=
  NoSignExtension P ∧
    (∀ i x, OriginalCandidate P {i} x → x ∈ LinearMap.range P.transpose.mulVecLin) ∧
    ∀ i j, i ≠ j → ∃ σ : ℝ, IsSign σ ∧ ∀ x, OriginalCandidate P {i, j} x →
      HalfCorrelationPattern (Fintype.card κ) σ (∑ k, P i k * x k) (∑ k, P j k * x k)

def HalfOverlapExtraLines {ι κ : Type*} [Fintype κ] [DecidableEq ι]
    (P : Matrix ι κ ℝ) (i j : ι) : Prop :=
  ∃ x y : κ → ℝ, ∃ σ : ℝ, OriginalCandidate P {i, j} x ∧ OriginalCandidate P {i, j} y ∧
    IsSign σ ∧ (∑ k, x k * y k) = 0 ∧
    (∑ k, P i k * x k) = (Fintype.card κ : ℝ) / 2 ∧
    (∑ k, P j k * x k) = σ * ((Fintype.card κ : ℝ) / 2) ∧
    (∑ k, P i k * y k) = (Fintype.card κ : ℝ) / 2 ∧
    (∑ k, P j k * y k) = σ * ((Fintype.card κ : ℝ) / 2) ∧
    ∀ z, OriginalCandidate P {i, j} z →
      SameSignLine z (P i) ∨ SameSignLine z (P j) ∨ SameSignLine z x ∨ SameSignLine z y

def HalfOverlapPairStructure {ι κ : Type*} [Fintype κ] [DecidableEq ι]
    (P : Matrix ι κ ℝ) : Prop :=
  NoSignExtension P ∧
    (∀ i x, OriginalCandidate P {i} x → SameSignLine x (P i)) ∧
    ∀ i j, i ≠ j →
      (∀ x, OriginalCandidate P {i, j} x → SameSignLine x (P i) ∨ SameSignLine x (P j)) ∨
        HalfOverlapExtraLines P i j

theorem halfCorrelationPattern_neg (N σ u v : ℝ) (h : HalfCorrelationPattern N σ u v) :
    HalfCorrelationPattern N σ (-u) (-v) := by
  rcases h with hp | hp | hp
  · exact Or.inl ⟨by simp [hp.1], by simpa only [abs_neg] using hp.2⟩
  · exact Or.inr (Or.inl ⟨by simp [hp.1], by simpa only [abs_neg] using hp.2⟩)
  · refine Or.inr (Or.inr ⟨by simpa only [abs_neg] using hp.1, ?_⟩)
    rw [hp.2]
    ring

theorem sameSignLine_correlation_pattern {ι κ : Type*} [Fintype κ]
    (P : Matrix ι κ ℝ) (i j : ι) (N σ : ℝ) (x y : κ → ℝ)
    (hline : SameSignLine x y)
    (hpattern : HalfCorrelationPattern N σ (∑ k, P i k * y k) (∑ k, P j k * y k)) :
    HalfCorrelationPattern N σ (∑ k, P i k * x k) (∑ k, P j k * x k) := by
  rcases hline with rfl | rfl
  · exact hpattern
  · simpa only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib] using
      halfCorrelationPattern_neg N σ _ _ hpattern

theorem partial_row_correlation {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (i j : ι) :
    (∑ k, P i k * P j k) = (Fintype.card κ : ℝ) * (if i = j then 1 else 0) := by
  have h := congrArg (fun M => M i j) hP.2
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul] using h

theorem half_overlap_structure_implies_correlations {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ]
    (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (hstruct : HalfOverlapPairStructure P) :
    HalfOverlapCorrelationConditions P := by
  have hrow (i : ι) : P i ∈ LinearMap.range P.transpose.mulVecLin := by
    rw [Matrix.range_mulVecLin]
    change P i ∈ Submodule.span ℝ (Set.range P)
    exact Submodule.subset_span ⟨i, rfl⟩
  refine ⟨hstruct.1, ?_, ?_⟩
  · intro i x hx
    rcases hstruct.2.1 i x hx with rfl | rfl
    · exact hrow i
    · exact Submodule.neg_mem _ (hrow i)
  · intro i j hij
    have hi (σ : ℝ) : HalfCorrelationPattern (Fintype.card κ) σ
        (∑ k, P i k * P i k) (∑ k, P j k * P i k) := by
      simp [HalfCorrelationPattern, partial_row_correlation P hP, Ne.symm hij]
    have hj (σ : ℝ) : HalfCorrelationPattern (Fintype.card κ) σ
        (∑ k, P i k * P j k) (∑ k, P j k * P j k) := by
      simp [HalfCorrelationPattern, partial_row_correlation P hP, hij]
    rcases hstruct.2.2 i j hij with hold | hextra
    · refine ⟨1, Or.inl rfl, ?_⟩
      intro z hz
      rcases hold z hz with hline | hline
      · exact sameSignLine_correlation_pattern P i j _ 1 z (P i) hline (hi 1)
      · exact sameSignLine_correlation_pattern P i j _ 1 z (P j) hline (hj 1)
    · obtain ⟨x, y, σ, hx, hy, hσ, hxy, hix, hjx, hiy, hjy, hcover⟩ := hextra
      have hn : (0 : ℝ) ≤ Fintype.card κ / 2 := div_nonneg (Nat.cast_nonneg _) (by norm_num)
      have hpx : HalfCorrelationPattern (Fintype.card κ) σ
          (∑ k, P i k * x k) (∑ k, P j k * x k) := by
        exact Or.inr (Or.inr ⟨by rw [hix, abs_of_nonneg hn], by rw [hix, hjx]⟩)
      have hpy : HalfCorrelationPattern (Fintype.card κ) σ
          (∑ k, P i k * y k) (∑ k, P j k * y k) := by
        exact Or.inr (Or.inr ⟨by rw [hiy, abs_of_nonneg hn], by rw [hiy, hjy]⟩)
      refine ⟨σ, hσ, ?_⟩
      intro z hz
      rcases hcover z hz with hline | hline | hline | hline
      · exact sameSignLine_correlation_pattern P i j _ σ z (P i) hline (hi σ)
      · exact sameSignLine_correlation_pattern P i j _ σ z (P j) hline (hj σ)
      · exact sameSignLine_correlation_pattern P i j _ σ z x hline hpx
      · exact sameSignLine_correlation_pattern P i j _ σ z y hline hpy

theorem single_original_deletion_card_bound {ι κ τ ν : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ]
    [Fintype τ] [DecidableEq τ] [Nonempty τ] [Fintype ν] [DecidableEq ν]
    (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (H : Matrix τ τ ℝ) (hH : IsHadamard H)
    (i : ι) (D : Finset (ι × τ)) (hD : ∀ r ∈ D, r.1 = i)
    (hsingle : ∀ x, OriginalCandidate P {i} x → x ∈ LinearMap.range P.transpose.mulVecLin)
    (V : Matrix ν (κ × τ) ℝ) (hV : IsPartialHadamard V)
    (hret : ∀ r, r ∉ D → ∀ v, ∑ k, tensorFrame P H r k * V v k = 0) :
    Fintype.card ν ≤ D.card := by
  classical
  have hmem (v : ν) : V v ∈ LinearMap.range
      ((tensorFrame P H).submatrix (fun r : D => r.val) id).transpose.mulVecLin := by
    have hcol (b : τ) : (fun k => V v (k, b)) ∈ LinearMap.range P.transpose.mulVecLin := by
      apply hsingle
      refine ⟨fun k => hV.1 v (k, b), ?_⟩
      intro j hj
      have hji : j ≠ i := by simpa only [Finset.mem_singleton] using hj
      apply tensor_fiber_orthogonal_columns P H hH (V v) j ?_ b
      intro a
      apply hret (j, a) ?_ v
      intro hm
      exact hji (hD (j, a) hm)
    exact row_range_restrict_of_orthogonal (tensorFrame P H) (tensorFrame_partialHadamard P H hP hH)
      D (V v) (tensor_row_range_of_columns P H hH (V v) hcol) (fun r hr => hret r hr v)
  have h := row_range_family_card_le
    ((tensorFrame P H).submatrix (fun r : D => r.val) id) V hV hmem
  simpa only [Fintype.card_coe] using h

theorem half_overlap_correlation_excludes_exchange {ι κ τ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ]
    [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (H : Matrix τ τ ℝ) (hH : IsHadamard H)
    (hcond : HalfOverlapCorrelationConditions P) (k : ℕ) (hk : k ≤ 2) :
    ¬ HasAugmentingExchange (tensorFrame P H) k := by
  classical
  rintro ⟨D, hD, V, hV, hret⟩
  have hcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · have he : D = ∅ := Finset.card_eq_zero.mp hD
    exact tensor_noSignExtension P H hH hcond.1
      ⟨V 0, hV.1 0, fun r => hret r (by simp [he]) 0⟩
  · obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hD
    have hbound := single_original_deletion_card_bound P hP H hH r.1 D
      (by intro x hx
          have hxr : x = r := by simpa only [hr, Finset.mem_singleton] using hx
          exact congrArg Prod.fst hxr)
      (hcond.2.1 r.1) V hV hret
    simp only [Fintype.card_fin] at hbound
    omega
  · obtain ⟨r, t, hrt, heq⟩ := Finset.card_eq_two.mp hD
    rcases r with ⟨i, a⟩
    rcases t with ⟨j, b⟩
    by_cases hij : i = j
    · subst j
      have hbound := single_original_deletion_card_bound P hP H hH i D
        (by intro x hx; rw [heq] at hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl <;> rfl)
        (hcond.2.1 i) V hV hret
      simp only [Fintype.card_fin] at hbound
      omega
    · obtain ⟨σ, hσ, hp⟩ := hcond.2.2 i j hij
      have hbound := two_distinct_rows_half_overlap_bound P hP H hH i j hij a b σ hσ
        (by intro x hx horth; exact hp x ⟨hx, fun r hr =>
          horth r (by simp_all) (by simp_all)⟩) V hV (by simpa only [heq] using hret)
      simp only [Fintype.card_fin] at hbound
      omega

theorem half_overlap_pair_structure_excludes_exchange {ι κ τ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ]
    [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (H : Matrix τ τ ℝ) (hH : IsHadamard H)
    (hstruct : HalfOverlapPairStructure P) (k : ℕ) (hk : k ≤ 2) :
    ¬ HasAugmentingExchange (tensorFrame P H) k :=
  half_overlap_correlation_excludes_exchange P hP H hH
    (half_overlap_structure_implies_correlations P hP hstruct) k hk

theorem half_overlap_tensor_cost_three {ι κ τ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ]
    [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (H : Matrix τ τ ℝ) (hH : IsHadamard H)
    (hstruct : HalfOverlapPairStructure P) (hcost : exchangeCost P = 3) :
    exchangeCost (tensorFrame P H) = 3 := by
  classical
  have hu := tensor_exchangeCost_le P H hH
  rw [hcost] at hu
  by_cases hex : ∃ k, HasAugmentingExchange (tensorFrame P H) k
  · rw [exchangeCost_eq_minimum _ hex] at hu ⊢
    have hk : Nat.find hex ≤ 3 := by exact_mod_cast hu
    have hn : ¬ Nat.find hex ≤ 2 := by
      intro h
      exact half_overlap_pair_structure_excludes_exchange P hP H hH hstruct _ h (Nat.find_spec hex)
    have heq : Nat.find hex = 3 := by omega
    rw [heq]
    norm_num
  · rw [exchangeCost_eq_top _ hex] at hu
    simp at hu

end CompletionTheory
