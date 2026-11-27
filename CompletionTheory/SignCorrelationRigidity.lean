/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.HalfOverlapBarrier
@[expose] public section
namespace CompletionTheory
open Matrix

theorem cube_dot_eq_card_rigid {κ : Type*} [Fintype κ]
    (u x : κ → ℝ) (hu : IsCubeVector u) (hx : IsCubeVector x)
    (hdot : (∑ k, u k * x k) = Fintype.card κ) : x = u := by
  classical
  have hsq (k : κ) : (x k - u k) ^ 2 = 2 - 2 * (u k * x k) := by
    have h1 := isSign_sq (hu k)
    have h2 := isSign_sq (hx k)
    nlinarith
  have hsum : (∑ k, (x k - u k) ^ 2) = 0 := by
    simp_rw [hsq]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hdot]
    simp
    ring
  funext k
  have hk := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (x k - u k))).mp hsum k (Finset.mem_univ k)
  nlinarith

theorem cube_abs_dot_eq_card_rigid {κ : Type*} [Fintype κ]
    (u x : κ → ℝ) (hu : IsCubeVector u) (hx : IsCubeVector x)
    (hdot : |∑ k, u k * x k| = Fintype.card κ) : SameSignLine x u := by
  rcases eq_or_eq_neg_of_abs_eq hdot with h | h
  · exact Or.inl (cube_dot_eq_card_rigid u x hu hx h)
  · right
    have hneg : IsCubeVector (-u) := by
      intro k
      rcases hu k with h | h <;> simp [h]
    apply cube_dot_eq_card_rigid (-u) x hneg hx
    simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, h, neg_neg]

theorem halfCorrelationPattern_symm (N σ u v : ℝ) (hσ : IsSign σ)
    (h : HalfCorrelationPattern N σ u v) : HalfCorrelationPattern N σ v u := by
  rcases h with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · apply Or.inr ∘ Or.inr
    have hs := isSign_sq hσ
    have ha : |σ| = 1 := by rcases hσ with hs | hs <;> simp [hs]
    constructor
    · rw [h.2, abs_mul, ha, one_mul, h.1]
    · rw [h.2]
      calc
        u = σ ^ 2 * u := by rw [hs, one_mul]
        _ = σ * (σ * u) := by ring

theorem singleton_line_of_pair_patterns {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Nontrivial ι] [Fintype κ] [Nonempty κ]
    (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P)
    (hpairs : ∀ i j, i ≠ j → ∃ σ : ℝ, IsSign σ ∧ ∀ x,
      OriginalCandidate P {i,j} x → HalfCorrelationPattern (Fintype.card κ) σ
        (∑ k, P i k * x k) (∑ k, P j k * x k)) :
    ∀ i x, OriginalCandidate P {i} x → SameSignLine x (P i) := by
  intro i x hx
  obtain ⟨j, hji⟩ := exists_ne i
  obtain ⟨σ, hσ, hpattern⟩ := hpairs i j (Ne.symm hji)
  have hpair : OriginalCandidate P {i,j} x := by
    refine ⟨hx.1, ?_⟩
    intro k hk
    apply hx.2 k
    simp only [Finset.mem_singleton]
    intro hki
    exact hk (by simp [hki])
  have hz := hx.2 j (by simpa using hji)
  have hh := hpattern x hpair
  rw [hz] at hh
  have hn : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  have habs : |∑ k, P i k * x k| = Fintype.card κ := by
    rcases hh with hh | hh | hh
    · simp only [abs_zero] at hh
      linarith [hh.2]
    · exact hh.2
    · have hne : σ ≠ 0 := by rcases hσ with h | h <;> simp [h]
      have hu := (mul_eq_zero.mp hh.2.symm).resolve_left hne
      rw [hu, abs_zero] at hh
      linarith [hh.1]
  exact cube_abs_dot_eq_card_rigid (P i) x (hP.1 i) hx.1 habs

theorem correlation_conditions_tensor_cost_three {ι κ τ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ]
    [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (H : Matrix τ τ ℝ) (hH : IsHadamard H)
    (hcond : HalfOverlapCorrelationConditions P) (hupper : exchangeCost P ≤ 3) :
    exchangeCost (tensorFrame P H) = 3 := by
  classical
  have hu := (tensor_exchangeCost_le P H hH).trans hupper
  by_cases hex : ∃ k, HasAugmentingExchange (tensorFrame P H) k
  · rw [exchangeCost_eq_minimum _ hex] at hu ⊢
    have hk : Nat.find hex ≤ 3 := by exact_mod_cast hu
    have hn : ¬ Nat.find hex ≤ 2 := by
      intro h
      exact half_overlap_correlation_excludes_exchange P hP H hH hcond _ h (Nat.find_spec hex)
    have heq : Nat.find hex = 3 := by omega
    rw [heq]
    norm_num
  · rw [exchangeCost_eq_top _ hex] at hu
    simp at hu

theorem correlation_conditions_exclude_base_exchange {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ]
    (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P)
    (hcond : HalfOverlapCorrelationConditions P) (k : ℕ) (hk : k ≤ 2) :
    ¬ HasAugmentingExchange P k := by
  let H : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 1
  have hH : IsHadamard H := by
    constructor
    · intro i j; exact Or.inl rfl
    · ext i j
      fin_cases i
      fin_cases j
      rw [@Matrix.mul_apply _ _ _ ℝ (Fin.fintype 1) Real.instMul Real.instAddCommMonoid]
      norm_num [H, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
        Fin.sum_univ_succ]
      rfl
  intro hex
  exact half_overlap_correlation_excludes_exchange P hP H hH hcond k hk
    (tensor_augmenting_exchange P H hH 0 k hex)

theorem correlation_conditions_base_cost_three {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ]
    (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P)
    (hcond : HalfOverlapCorrelationConditions P) (hupper : exchangeCost P ≤ 3) :
    exchangeCost P = 3 := by
  classical
  by_cases hex : ∃ k, HasAugmentingExchange P k
  · rw [exchangeCost_eq_minimum _ hex] at hupper ⊢
    have hk : Nat.find hex ≤ 3 := by exact_mod_cast hupper
    have hn : ¬ Nat.find hex ≤ 2 := by
      intro h
      exact correlation_conditions_exclude_base_exchange P hP hcond _ h (Nat.find_spec hex)
    have heq : Nat.find hex = 3 := by omega
    rw [heq]
    norm_num
  · rw [exchangeCost_eq_top _ hex] at hupper
    simp at hupper

end CompletionTheory
