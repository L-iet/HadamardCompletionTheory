/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module

public import CompletionTheory.InformationCoordinates
public import CompletionTheory.EncodedFrames
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Data.Rat.BigOperators

/-! # Rational reconstruction certificates for complete finite sign searches -/

@[expose] public section
namespace CompletionTheory

noncomputable def rationalRealCast : ℚ →+* ℝ :=
  @Rat.castHom ℝ inferInstance (IsStrictOrderedRing.toCharZero (R := ℝ))

def informationSelector {n q : ℕ} (a : Fin q → Fin n) : Matrix (Fin q) (Fin n) ℚ :=
  fun i j => if a i = j then 1 else 0

theorem rational_reconstruction_complete {n r q : ℕ}
    (P : Matrix (Fin r) (Fin n) ℚ) (A : Matrix (Fin n) (Fin r) ℚ)
    (B : Matrix (Fin n) (Fin q) ℚ) (a : Fin q → Fin n)
    (hcert : A * P + B * informationSelector a = 1)
    (x : Fin n → ℝ) (hx : (P.map (rationalRealCast)).mulVec x = 0) :
    (B.map (rationalRealCast)).mulVec (fun j => x (a j)) = x := by
  have hc : A.map (rationalRealCast) * P.map (rationalRealCast) +
      B.map (rationalRealCast) * (informationSelector a).map (rationalRealCast) = 1 := by
    ext i j
    have h := congrArg (fun M => M i j) hcert
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply] at h
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply, Matrix.map_apply]
    change (∑ k, (A i k : ℝ) * (P k j : ℝ)) +
      (∑ k, (B i k : ℝ) * (informationSelector a k j : ℝ)) = (if i = j then 1 else 0)
    by_cases hij : i = j
    · subst j
      simp only [ite_true] at h ⊢
      exact_mod_cast h
    · simp only [ite_eq_right hij] at h ⊢
      exact_mod_cast h
  have hs : ((informationSelector a).map (rationalRealCast)).mulVec x = fun j => x (a j) := by
    funext j
    simp [informationSelector, Matrix.mulVec, dotProduct, apply_ite]
  have hv := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M.mulVec x) hc
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero,
    zero_add, Matrix.one_mulVec] at hv
  rwa [hs] at hv

theorem rational_seed_has_signs {n q : ℕ} (B : Matrix (Fin n) (Fin q) ℚ)
    (a : Fin q → Fin n) (x : Fin n → ℝ) (hx : IsCubeVector x)
    (hrec : (B.map (rationalRealCast)).mulVec (fun j => x (a j)) = x) :
    ∃ b : Fin q → Bool, IsCubeVector (B.mulVec (fun j => if b j then 1 else -1)) := by
  classical
  let b : Fin q → Bool := fun j => decide (x (a j) = 1)
  have harg : (rationalRealCast) ∘ (fun j => if b j then (1 : ℚ) else -1) =
      (fun j => x (a j)) := by
    funext j
    rcases hx (a j) with hp | hn
    · norm_num [b, hp]
    · norm_num [b, hn]
  refine ⟨b, ?_⟩
  intro i
  have hval := RingHom.map_mulVec (rationalRealCast) B (fun j => if b j then (1 : ℚ) else -1) i
  rw [harg, hrec] at hval
  change ((B.mulVec (fun j => if b j then (1 : ℚ) else -1) i : ℚ) : ℝ) = x i at hval
  rcases hx i with hp | hn
  · left
    exact_mod_cast hval.trans hp
  · right
    exact_mod_cast hval.trans hn

theorem rational_seed_reconstructs {n q : ℕ} (B : Matrix (Fin n) (Fin q) ℚ)
    (a : Fin q → Fin n) (x : Fin n → ℝ) (hx : IsCubeVector x)
    (hrec : (B.map rationalRealCast).mulVec (fun j => x (a j)) = x) :
    ∃ b : Fin q → Bool, IsCubeVector (B.mulVec (fun j => if b j then 1 else -1)) ∧
      ∀ i, rationalRealCast (B.mulVec (fun j => if b j then 1 else -1) i) = x i := by
  classical
  let b : Fin q → Bool := fun j => decide (x (a j) = 1)
  have harg : rationalRealCast ∘ (fun j => if b j then (1 : ℚ) else -1) =
      (fun j => x (a j)) := by
    funext j
    rcases hx (a j) with hp | hn
    · norm_num [b, hp]
    · norm_num [b, hn]
  have hval (i : Fin n) : rationalRealCast (B.mulVec (fun j => if b j then (1 : ℚ) else -1) i) = x i := by
    have h := RingHom.map_mulVec rationalRealCast B (fun j => if b j then (1 : ℚ) else -1) i
    rwa [harg, hrec] at h
  refine ⟨b, ?_, hval⟩
  intro i
  have h := hval i
  change ((B.mulVec (fun j => if b j then (1 : ℚ) else -1) i : ℚ) : ℝ) = x i at h
  rcases hx i with hp | hn
  · left; exact_mod_cast h.trans hp
  · right; exact_mod_cast h.trans hn

end CompletionTheory
