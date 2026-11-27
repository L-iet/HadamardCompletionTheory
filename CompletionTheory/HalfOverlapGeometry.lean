/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module

public import CompletionTheory.SpanRigidity
public import CompletionTheory.ExchangeBudget

/-! # Exact shared-projection bounds for half-overlap candidates -/

@[expose] public section
namespace CompletionTheory

noncomputable def halfOverlapWitness {κ : Type*} (u v : κ → ℝ) (σ : ℝ) : κ → ℝ :=
  fun j => (u j + σ * v j) / 2

theorem halfOverlapWitness_norm {κ : Type*} [Fintype κ]
    (u v : κ → ℝ) (σ N : ℝ) (hσ : IsSign σ)
    (hu : ∑ j, u j ^ 2 = N) (hv : ∑ j, v j ^ 2 = N)
    (huv : ∑ j, u j * v j = 0) :
    (∑ j, halfOverlapWitness u v σ j ^ 2) = N / 2 := by
  have hs := isSign_sq hσ
  have hterm (j : κ) : halfOverlapWitness u v σ j ^ 2 =
      u j ^ 2 / 4 + σ * (u j * v j) / 2 + v j ^ 2 / 4 := by
    unfold halfOverlapWitness
    calc
      _ = u j ^ 2 / 4 + σ * (u j * v j) / 2 + σ ^ 2 * v j ^ 2 / 4 := by ring
      _ = _ := by rw [hs, one_mul]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [← Finset.sum_div, ← Finset.mul_sum, hu, hv, huv]
  ring

theorem halfOverlapWitness_dot {κ : Type*} [Fintype κ]
    (u v x : κ → ℝ) (σ : ℝ) :
    (∑ j, halfOverlapWitness u v σ j * x j) =
      ((∑ j, u j * x j) + σ * ∑ j, v j * x j) / 2 := by
  calc
    _ = ∑ j, (u j * x j + σ * (v j * x j)) / 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [halfOverlapWitness]
      ring
    _ = _ := by rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem shared_half_projection_card_le_two {ν κ : Type*}
    [Fintype ν] [DecidableEq ν] [Fintype κ]
    (V : Matrix ν κ ℝ) (N : ℝ) (hN : 0 < N)
    (hV : V * V.transpose = N • 1) (w : κ → ℝ)
    (hw : ∑ j, w j ^ 2 = N / 2)
    (hproj : ∀ i, |∑ j, V i j * w j| = N / 2) :
    Fintype.card ν ≤ 2 := by
  have hb := rowGram_bessel V N hN hV w
  have hsq (i : ν) : (∑ j, V i j * w j) ^ 2 = (N / 2) ^ 2 := by
    rw [← sq_abs, hproj]
  simp_rw [hsq] at hb
  rw [hw] at hb
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hb
  by_contra hn
  have hc : (2 : ℝ) < Fintype.card ν := by exact_mod_cast (by omega : 2 < Fintype.card ν)
  have hp : 0 < ((Fintype.card ν : ℝ) - 2) * (N / 2) ^ 2 :=
    mul_pos (by linarith) (sq_pos_of_pos (by linarith))
  nlinarith

theorem partial_row_pair_witness_norm {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (i j : ι) (hij : i ≠ j)
    (σ : ℝ) (hσ : IsSign σ) :
    (∑ k, halfOverlapWitness (P i) (P j) σ k ^ 2) = (Fintype.card κ : ℝ) / 2 := by
  have hnorm (a : ι) : (∑ k, P a k ^ 2) = Fintype.card κ := by
    have h := congrArg (fun M => M a a) hP.2
    simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, pow_two] using h
  have horth : (∑ k, P i k * P j k) = 0 := by
    have h := congrArg (fun M => M i j) hP.2
    simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, hij] using h
  exact halfOverlapWitness_norm (P i) (P j) σ _ hσ (hnorm i) (hnorm j) horth

def HalfCorrelationPattern (N σ u v : ℝ) : Prop :=
  (u = 0 ∧ |v| = N) ∨ (v = 0 ∧ |u| = N) ∨ (|u| = N / 2 ∧ v = σ * u)

theorem halfCorrelationPattern_flat_rows {τ : Type*}
    [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (H : Matrix τ τ ℝ) (hH : IsHadamard H) (a b : τ)
    (N σ α β : ℝ) (hN : 0 < N) (hσ : IsSign σ)
    (hpattern : ∀ k, HalfCorrelationPattern N σ (α * H a k) (β * H b k)) :
    |α + σ * β| = N := by
  classical
  have habs (i k : τ) : |H i k| = 1 := by
    rcases hH.1 i k with h | h <;> simp [h]
  have hne (i k : τ) : H i k ≠ 0 := by
    rcases hH.1 i k with h | h <;> simp [h]
  have hσabs : |σ| = 1 := by rcases hσ with h | h <;> simp [h]
  let k0 : τ := Classical.arbitrary τ
  rcases hpattern k0 with hz | hz | hz
  · have hα : α = 0 := (mul_eq_zero.mp hz.1).resolve_right (hne a k0)
    have hβ : |β| = N := by simpa only [abs_mul, habs, mul_one] using hz.2
    simp [hα, abs_mul, hσabs, hβ]
  · have hβ : β = 0 := (mul_eq_zero.mp hz.1).resolve_right (hne b k0)
    have hα : |α| = N := by simpa only [abs_mul, habs, mul_one] using hz.2
    simp [hβ, hα]
  · have hα : |α| = N / 2 := by simpa only [abs_mul, habs, mul_one] using hz.1
    have hαne : α ≠ 0 := by intro h; simp [h] at hα; linarith
    have hrel (k : τ) : β * H b k = σ * (α * H a k) := by
      rcases hpattern k with hp | hp | hp
      · exact False.elim (((mul_ne_zero hαne (hne a k))) hp.1)
      · have hh : |α| = N := by simpa only [abs_mul, habs, mul_one] using hp.2
        linarith
      · exact hp.2
    have hab : a = b := by
      by_contra hn
      have hgram := congrArg (fun M => M a b) hH.2
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul, ite_eq_right hn, mul_zero] at hgram
      have hself := congrArg (fun M => M a a) hH.2
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul, ite_true, mul_one] at hself
      have hsum : (∑ k, H a k * (β * H b k)) =
          ∑ k, H a k * (σ * (α * H a k)) := by simp_rw [hrel]
      have hl : (∑ k, H a k * (β * H b k)) = β * ∑ k, H a k * H b k := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k hk; ring
      have hr : (∑ k, H a k * (σ * (α * H a k))) =
          σ * α * ∑ k, H a k * H a k := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k hk; ring
      rw [hl, hr, hgram, hself, mul_zero] at hsum
      have hm : (Fintype.card τ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      have hsne : σ ≠ 0 := by rcases hσ with h | h <;> simp [h]
      exact (mul_ne_zero (mul_ne_zero hsne hαne) hm) hsum.symm
    subst b
    have hβ : β = σ * α := by
      apply mul_right_cancel₀ (hne a k0)
      simpa only [mul_assoc] using hrel k0
    have hsquare := isSign_sq hσ
    have heq : α + σ * β = 2 * α := by
      rw [hβ]
      calc
        _ = α + σ ^ 2 * α := by ring
        _ = _ := by rw [hsquare]; ring
    rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), hα]
    ring

theorem tensor_fiber_correlation {ι κ τ : Type*}
    [Fintype κ] [Fintype τ] [DecidableEq τ]
    (P : Matrix ι κ ℝ) (H : Matrix τ τ ℝ) (hH : IsHadamard H)
    (f : (κ × τ) → ℝ) (i : ι) (a : τ) (α : ℝ)
    (hcol : ∀ b, (∑ j, P i j * f (j, b)) = α * H a b) :
    (∑ j : κ × τ, tensorFrame P H (i, a) j * f j) = α * Fintype.card τ := by
  have hself := congrArg (fun M => M a a) hH.2
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, ite_true, mul_one] at hself
  simp only [tensorFrame, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  calc
    _ = ∑ b, H a b * ∑ j, P i j * f (j, b) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ b, H a b * (α * H a b) := by simp_rw [hcol]
    _ = α * ∑ b, H a b * H a b := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b hb; ring
    _ = _ := by rw [hself]

theorem flat_half_overlap_projection {ι κ τ : Type*}
    [Fintype κ] [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (P : Matrix ι κ ℝ) (H : Matrix τ τ ℝ) (hH : IsHadamard H)
    (f : (κ × τ) → ℝ) (i j : ι) (a b : τ) (N σ α β : ℝ) (hN : 0 < N) (hσ : IsSign σ)
    (hleft : ∀ d, (∑ k, P i k * f (k, d)) = α * H a d)
    (hright : ∀ d, (∑ k, P j k * f (k, d)) = β * H b d)
    (hpattern : ∀ d, HalfCorrelationPattern N σ (α * H a d) (β * H b d)) :
    |∑ k, halfOverlapWitness (tensorFrame P H (i, a)) (tensorFrame P H (j, b)) σ k * f k| =
      (Fintype.card τ : ℝ) * N / 2 := by
  rw [halfOverlapWitness_dot, tensor_fiber_correlation P H hH f i a α hleft,
    tensor_fiber_correlation P H hH f j b β hright]
  calc
    _ = |(Fintype.card τ : ℝ) / 2| * |α + σ * β| := by
      rw [← abs_mul]
      congr 1
      ring
    _ = _ := by
      rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (by norm_num)),
        halfCorrelationPattern_flat_rows H hH a b N σ α β hN hσ hpattern]
      ring

theorem flat_half_overlap_family_card_le_two {ι κ τ ν : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ]
    [Fintype τ] [DecidableEq τ] [Nonempty τ] [Fintype ν] [DecidableEq ν]
    (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (H : Matrix τ τ ℝ) (hH : IsHadamard H)
    (i j : ι) (hij : i ≠ j) (a b : τ) (σ : ℝ) (hσ : IsSign σ)
    (V : Matrix ν (κ × τ) ℝ) (hV : IsPartialHadamard V)
    (hcorr : ∀ r, ∃ α β : ℝ,
      (∀ d, (∑ k, P i k * V r (k, d)) = α * H a d) ∧
      (∀ d, (∑ k, P j k * V r (k, d)) = β * H b d) ∧
      ∀ d, HalfCorrelationPattern (Fintype.card κ) σ (α * H a d) (β * H b d)) :
    Fintype.card ν ≤ 2 := by
  let w := halfOverlapWitness (tensorFrame P H (i, a)) (tensorFrame P H (j, b)) σ
  have hn : (0 : ℝ) < Fintype.card (κ × τ) := by exact_mod_cast Fintype.card_pos
  have hnκ : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  apply shared_half_projection_card_le_two V (Fintype.card (κ × τ)) hn hV.2 w
  · apply partial_row_pair_witness_norm (tensorFrame P H) (tensorFrame_partialHadamard P H hP hH)
      (i, a) (j, b) ?_ σ hσ
    intro h
    exact hij (Prod.mk.inj h).1
  · intro r
    obtain ⟨α, β, hl, hr, hp⟩ := hcorr r
    have h := flat_half_overlap_projection P H hH (V r) i j a b (Fintype.card κ)
      σ α β hnκ hσ hl hr hp
    simpa [w, Fintype.card_prod, Nat.cast_mul, mul_comm] using h

theorem hadamard_single_fiber_reconstruction {τ : Type*}
    [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (H : Matrix τ τ ℝ) (hH : IsHadamard H) (a : τ) (u : τ → ℝ)
    (horth : ∀ c, c ≠ a → ∑ d, H c d * u d = 0) :
    ∃ α : ℝ, ∀ d, u d = α * H a d := by
  classical
  have hn : (Fintype.card τ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcol : H.transpose * H = (Fintype.card τ : ℝ) • 1 := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using (isHadamard_mathlib hH).conjTranspose_mul
  let z : τ → ℝ := H.mulVec u
  have hz : z = Pi.single a (z a) := by
    funext c
    by_cases hc : c = a
    · subst c; simp
    · have hzero : z c = 0 := horth c hc
      simp [hc, hzero]
  have hu : H.transpose.mulVec z = (Fintype.card τ : ℝ) • u := by
    change H.transpose.mulVec (H.mulVec u) = _
    rw [Matrix.mulVec_mulVec, hcol, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hz] at hu
  refine ⟨z a / (Fintype.card τ : ℝ), ?_⟩
  intro d
  have hval : H a d * z a = (Fintype.card τ : ℝ) * u d := by
    have h := congrFun hu d
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h
  calc
    u d = (H a d * z a) / (Fintype.card τ : ℝ) :=
      (eq_div_iff hn).mpr (by linarith)
    _ = _ := by ring

theorem tensor_correlation_as_fiber {ι κ τ : Type*} [Fintype κ] [Fintype τ]
    (P : Matrix ι κ ℝ) (H : Matrix τ τ ℝ) (f : (κ × τ) → ℝ) (i : ι) (a : τ) :
    (∑ j : κ × τ, tensorFrame P H (i, a) j * f j) =
      ∑ b, H a b * ∑ j, P i j * f (j, b) := by
  simp only [tensorFrame, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem tensor_single_deleted_fiber {ι κ τ : Type*}
    [Fintype κ] [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (P : Matrix ι κ ℝ) (H : Matrix τ τ ℝ) (hH : IsHadamard H)
    (f : (κ × τ) → ℝ) (i : ι) (a : τ)
    (horth : ∀ c, c ≠ a → ∑ j, tensorFrame P H (i, c) j * f j = 0) :
    ∃ α : ℝ, ∀ d, (∑ j, P i j * f (j, d)) = α * H a d := by
  apply hadamard_single_fiber_reconstruction H hH a (fun d => ∑ j, P i j * f (j, d))
  intro c hc
  rw [← tensor_correlation_as_fiber]
  exact horth c hc

theorem two_deleted_tensor_correlations {ι κ τ : Type*}
    [Fintype κ] [Fintype τ] [DecidableEq ι] [DecidableEq τ] [Nonempty τ]
    (P : Matrix ι κ ℝ) (H : Matrix τ τ ℝ) (hH : IsHadamard H)
    (f : (κ × τ) → ℝ) (i j : ι) (hij : i ≠ j) (a b : τ)
    (horth : ∀ r, r ∉ ({(i, a), (j, b)} : Finset (ι × τ)) →
      ∑ k, tensorFrame P H r k * f k = 0) :
    ∃ α β : ℝ, (∀ d, (∑ k, P i k * f (k, d)) = α * H a d) ∧
      (∀ d, (∑ k, P j k * f (k, d)) = β * H b d) := by
  have hl : ∃ α : ℝ, ∀ d, (∑ k, P i k * f (k, d)) = α * H a d := by
    apply tensor_single_deleted_fiber P H hH f i a
    intro c hc
    apply horth (i, c)
    simp [hc, hij]
  have hr : ∃ β : ℝ, ∀ d, (∑ k, P j k * f (k, d)) = β * H b d := by
    apply tensor_single_deleted_fiber P H hH f j b
    intro c hc
    apply horth (j, c)
    simp [hc, Ne.symm hij]
  obtain ⟨α, hα⟩ := hl
  obtain ⟨β, hβ⟩ := hr
  exact ⟨α, β, hα, hβ⟩

theorem two_distinct_rows_half_overlap_bound {ι κ τ ν : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ]
    [Fintype τ] [DecidableEq τ] [Nonempty τ] [Fintype ν] [DecidableEq ν]
    (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (H : Matrix τ τ ℝ) (hH : IsHadamard H)
    (i j : ι) (hij : i ≠ j) (a b : τ) (σ : ℝ) (hσ : IsSign σ)
    (hpattern : ∀ x : κ → ℝ, IsCubeVector x →
      (∀ r, r ≠ i → r ≠ j → ∑ k, P r k * x k = 0) →
      HalfCorrelationPattern (Fintype.card κ) σ (∑ k, P i k * x k) (∑ k, P j k * x k))
    (V : Matrix ν (κ × τ) ℝ) (hV : IsPartialHadamard V)
    (hret : ∀ r, r ∉ ({(i, a), (j, b)} : Finset (ι × τ)) →
      ∀ v, ∑ k, tensorFrame P H r k * V v k = 0) : Fintype.card ν ≤ 2 := by
  apply flat_half_overlap_family_card_le_two P hP H hH i j hij a b σ hσ V hV
  intro v
  obtain ⟨α, β, hl, hr⟩ := two_deleted_tensor_correlations P H hH (V v) i j hij a b
    (fun r h => hret r h v)
  refine ⟨α, β, hl, hr, ?_⟩
  intro d
  have hcol : ∀ r, r ≠ i → r ≠ j → ∑ k, P r k * V v (k, d) = 0 := by
    intro r hri hrj
    apply tensor_fiber_orthogonal_columns P H hH (V v) r ?_ d
    intro c
    apply hret (r, c) ?_ v
    simp [hri, hrj]
  have hp := hpattern (fun k => V v (k, d)) (fun k => hV.1 v (k, d)) hcol
  rwa [hl, hr] at hp

end CompletionTheory
