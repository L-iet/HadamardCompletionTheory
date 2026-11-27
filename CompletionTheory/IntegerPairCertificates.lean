/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.Order24PairCertificates
@[expose] public section
namespace CompletionTheory
open Matrix

def integerInformationSelector {n q : ℕ} (a : Fin q → Fin n) : Matrix (Fin q) (Fin n) ℤ :=
  fun i j => if a i = j then 1 else 0

theorem integer_scaled_reconstruction {n r q : ℕ}
    (P : Matrix (Fin r) (Fin n) ℤ) (A : Matrix (Fin n) (Fin r) ℤ)
    (B : Matrix (Fin n) (Fin q) ℤ) (a : Fin q → Fin n) (D : ℤ)
    (hcert : A * P + B * integerInformationSelector a = D • 1)
    (x : Fin n → ℝ) (hx : (P.map (Int.castRingHom ℝ)).mulVec x = 0) :
    (B.map (Int.castRingHom ℝ)).mulVec (fun j => x (a j)) = (D : ℝ) • x := by
  have hc : A.map (Int.castRingHom ℝ) * P.map (Int.castRingHom ℝ) +
      B.map (Int.castRingHom ℝ) * (integerInformationSelector a).map (Int.castRingHom ℝ) =
      (D : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    have h := congrArg (fun M => M i j) hcert
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul] at h ⊢
    change (∑ k, (A i k : ℝ) * (P k j : ℝ)) +
      (∑ k, (B i k : ℝ) * (integerInformationSelector a k j : ℝ)) =
        (D : ℝ) * (if i = j then 1 else 0)
    by_cases hij : i = j
    · subst j
      simp only [ite_true] at h ⊢
      exact_mod_cast h
    · simp only [ite_eq_right hij] at h ⊢
      exact_mod_cast h
  have hs : ((integerInformationSelector a).map (Int.castRingHom ℝ)).mulVec x =
      fun j => x (a j) := by
    funext j
    simp [integerInformationSelector, Matrix.mulVec, dotProduct, apply_ite]
  have hv := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M.mulVec x) hc
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero,
    zero_add, Matrix.smul_mulVec, Matrix.one_mulVec] at hv
  rwa [hs] at hv

theorem integer_scaled_seed {n q : ℕ} (B : Matrix (Fin n) (Fin q) ℤ)
    (a : Fin q → Fin n) (D : ℤ) (x : Fin n → ℝ) (hx : IsCubeVector x)
    (hrec : (B.map (Int.castRingHom ℝ)).mulVec (fun j => x (a j)) = (D : ℝ) • x) :
    ∃ b : Fin q → Bool,
      (∀ i, B.mulVec (fun j => if b j then 1 else -1) i = D ∨
        B.mulVec (fun j => if b j then 1 else -1) i = -D) ∧
      ∀ i, (B.mulVec (fun j => if b j then 1 else -1) i : ℝ) = (D : ℝ) * x i := by
  classical
  let b : Fin q → Bool := fun j => decide (x (a j) = 1)
  have harg : (Int.castRingHom ℝ) ∘ (fun j => if b j then (1 : ℤ) else -1) =
      (fun j => x (a j)) := by
    funext j
    rcases hx (a j) with hp | hn
    · norm_num [b, hp]
    · norm_num [b, hn]
  have hval (i : Fin n) : (B.mulVec (fun j => if b j then (1 : ℤ) else -1) i : ℝ) =
      (D : ℝ) * x i := by
    have h := RingHom.map_mulVec (Int.castRingHom ℝ) B (fun j => if b j then (1 : ℤ) else -1) i
    rw [harg, hrec] at h
    exact h
  refine ⟨b, ?_, hval⟩
  intro i
  have h := hval i
  rcases hx i with hp | hn
  · left
    rw [hp, mul_one] at h
    exact_mod_cast h
  · right
    rw [hn, mul_neg_one] at h
    exact_mod_cast h

def IntegerScaledHalfPattern (D σ u v : ℤ) : Prop :=
  (u = 0 ∧ |v| = 24 * D) ∨ (v = 0 ∧ |u| = 24 * D) ∨ (|u| = 12 * D ∧ v = σ * u)

theorem integer_scaled_pattern_real (D σ u v : ℤ) (hD : 0 < D)
    (α β : ℝ) (hu : (u : ℝ) = D * α) (hv : (v : ℝ) = D * β)
    (h : IntegerScaledHalfPattern D σ u v) : HalfCorrelationPattern 24 (σ : ℝ) α β := by
  have hd : (0 : ℝ) < D := by exact_mod_cast hD
  have hdne : (D : ℝ) ≠ 0 := ne_of_gt hd
  have habs (z : ℤ) (γ : ℝ) (hz : (z : ℝ) = D * γ) (N : ℤ)
      (hh : |z| = N * D) : |γ| = N := by
    have hc : |(z : ℝ)| = (N : ℝ) * D := by exact_mod_cast hh
    rw [hz, abs_mul, abs_of_pos hd] at hc
    apply mul_left_cancel₀ hdne
    calc
      (D : ℝ) * |γ| = (N : ℝ) * D := hc
      _ = (D : ℝ) * N := by ring
  rcases h with h | h | h
  · apply Or.inl
    constructor
    · have hz : (D : ℝ) * α = 0 := by rw [← hu, h.1, Int.cast_zero]
      exact (mul_eq_zero.mp hz).resolve_left hdne
    · exact_mod_cast habs v β hv 24 h.2
  · apply Or.inr ∘ Or.inl
    constructor
    · have hz : (D : ℝ) * β = 0 := by rw [← hv, h.1, Int.cast_zero]
      exact (mul_eq_zero.mp hz).resolve_left hdne
    · exact_mod_cast habs u α hu 24 h.2
  · apply Or.inr ∘ Or.inr
    constructor
    · have hh := habs u α hu 12 h.1
      norm_num at hh ⊢
      exact hh
    · have he : (v : ℝ) = (σ : ℝ) * u := by exact_mod_cast h.2
      apply mul_left_cancel₀ hdne
      calc
        (D : ℝ) * β = (σ : ℝ) * ((D : ℝ) * α) := by rw [← hv, ← hu]; exact he
        _ = (D : ℝ) * ((σ : ℝ) * α) := by ring

theorem order24_integer_pair_lift {r q : ℕ}
    (i j : Fin 16) (ρ : Fin r → Fin 16) (a : Fin q → Fin 24)
    (A : Matrix (Fin 24) (Fin r) ℤ) (B : Matrix (Fin 24) (Fin q) ℤ) (D σ : ℤ)
    (hD : 0 < D) (hout : ∀ k, ρ k ∉ ({i,j} : Finset (Fin 16)))
    (hcert : A * (encodedIntFrame (n := 24) base24Masks).submatrix ρ id +
      B * integerInformationSelector a = D • 1)
    (hfinite : ∀ b : Fin q → Bool,
      (∀ k, B.mulVec (fun t => if b t then 1 else -1) k = D ∨
        B.mulVec (fun t => if b t then 1 else -1) k = -D) →
      IntegerScaledHalfPattern D σ
        (∑ k, encodedIntFrame base24Masks i k * B.mulVec (fun t => if b t then 1 else -1) k)
        (∑ k, encodedIntFrame base24Masks j k * B.mulVec (fun t => if b t then 1 else -1) k)) :
    ∀ x : Fin 24 → ℝ, OriginalCandidate base24Frame {i,j} x →
      HalfCorrelationPattern 24 (σ : ℝ)
        (∑ k, base24Frame i k * x k) (∑ k, base24Frame j k * x k) := by
  intro x hx
  have hentry (s : Fin 16) (k : Fin 24) :
      (encodedIntFrame base24Masks s k : ℝ) = base24Frame s k := rfl
  have hz : (((encodedIntFrame (n := 24) base24Masks).submatrix ρ id).map
      (Int.castRingHom ℝ)).mulVec x = 0 := by
    funext s
    change (∑ k, (encodedIntFrame base24Masks (ρ s) k : ℝ) * x k) = 0
    simp_rw [hentry]
    exact hx.2 (ρ s) (hout s)
  have hr := integer_scaled_reconstruction _ A B a D hcert x hz
  obtain ⟨b, hb, hval⟩ := integer_scaled_seed B a D x hx.1 hr
  have hdot (s : Fin 16) :
      ((∑ k, encodedIntFrame base24Masks s k * B.mulVec (fun t => if b t then 1 else -1) k : ℤ) : ℝ) =
        (D : ℝ) * ∑ k, base24Frame s k * x k := by
    simp only [Int.cast_sum, Int.cast_mul]
    simp_rw [hentry, hval]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  exact integer_scaled_pattern_real D σ _ _ hD _ _ (hdot i) (hdot j) (hfinite b hb)

end CompletionTheory
