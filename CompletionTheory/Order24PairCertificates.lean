/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module

public import CompletionTheory.Order24Terminal
public import CompletionTheory.HalfOverlapBarrier
public import Mathlib.Data.Rat.Cast.Order

/-! # Exact rational pair-correlation certificate lifting -/

@[expose] public section
namespace CompletionTheory

def RationalHalfCorrelationPattern (N σ u v : ℚ) : Prop :=
  (u = 0 ∧ |v| = N) ∨ (v = 0 ∧ |u| = N) ∨ (|u| = N / 2 ∧ v = σ * u)

theorem rational_half_pattern_cast (N σ u v : ℚ) (h : RationalHalfCorrelationPattern N σ u v) :
    HalfCorrelationPattern (rationalRealCast N) (rationalRealCast σ) (rationalRealCast u) (rationalRealCast v) := by
  rcases h with hp | hp | hp
  · apply Or.inl
    constructor
    · rw [hp.1, map_zero]
    · change |(v : ℝ)| = (N : ℝ)
      exact_mod_cast hp.2
  · apply Or.inr ∘ Or.inl
    constructor
    · rw [hp.1, map_zero]
    · change |(u : ℝ)| = (N : ℝ)
      exact_mod_cast hp.2
  · apply Or.inr ∘ Or.inr
    constructor
    · change |(u : ℝ)| = (N : ℝ) / 2
      exact_mod_cast hp.1
    · change (v : ℝ) = (σ : ℝ) * (u : ℝ)
      exact_mod_cast hp.2

theorem order24_pair_certificate_lift {r q : ℕ}
    (i j : Fin 16) (ρ : Fin r → Fin 16) (a : Fin q → Fin 24)
    (A : Matrix (Fin 24) (Fin r) ℚ) (B : Matrix (Fin 24) (Fin q) ℚ) (σ : ℚ)
    (hout : ∀ k, ρ k ∉ ({i, j} : Finset (Fin 16)))
    (hcert : A * base24RationalFrame.submatrix ρ id + B * informationSelector a = 1)
    (hfinite : ∀ b : Fin q → Bool,
      IsCubeVector (B.mulVec (fun k => if b k then 1 else -1)) →
      RationalHalfCorrelationPattern 24 σ
        (∑ k, base24RationalFrame i k * B.mulVec (fun k => if b k then 1 else -1) k)
        (∑ k, base24RationalFrame j k * B.mulVec (fun k => if b k then 1 else -1) k)) :
    ∀ x : Fin 24 → ℝ, OriginalCandidate base24Frame {i, j} x →
      HalfCorrelationPattern 24 (rationalRealCast σ)
        (∑ k, base24Frame i k * x k) (∑ k, base24Frame j k * x k) := by
  intro x hx
  have hentry (s : Fin 16) (k : Fin 24) : rationalRealCast (base24RationalFrame s k) = base24Frame s k :=
    congrArg (fun M => M s k) base24RationalFrame_cast
  have hzero : ((base24RationalFrame.submatrix ρ id).map rationalRealCast).mulVec x = 0 := by
    funext s
    change (∑ k, rationalRealCast (base24RationalFrame (ρ s) k) * x k) = 0
    simp_rw [hentry]
    exact hx.2 (ρ s) (hout s)
  have hrec := rational_reconstruction_complete (base24RationalFrame.submatrix ρ id) A B a hcert x hzero
  obtain ⟨b, hb, hval⟩ := rational_seed_reconstructs B a x hx.1 hrec
  have hdot (s : Fin 16) : rationalRealCast
      (∑ k, base24RationalFrame s k * B.mulVec (fun k => if b k then 1 else -1) k) =
      ∑ k, base24Frame s k * x k := by
    simp only [map_sum, map_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hentry, hval]
  have h := rational_half_pattern_cast _ _ _ _ (hfinite b hb)
  simpa only [map_ofNat, hdot] using h

end CompletionTheory
