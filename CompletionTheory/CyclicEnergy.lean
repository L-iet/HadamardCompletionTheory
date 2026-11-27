/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module

public import CompletionTheory.CyclicNorms
public import Mathlib.Tactic.Linarith

/-! # Energy and augmentation of actual cyclic coefficient arrays -/

@[expose] public section
namespace CompletionTheory

theorem odd_coefficient_square_lower {z : ℤ} (hz : (z : ZMod 2) = 1) : 1 ≤ z ^ 2 := by
  have hne : z ≠ 0 := by intro h; simp [h] at hz
  have h : z ≤ -1 ∨ 1 ≤ z := by omega
  rcases h with h | h <;> nlinarith [sq_nonneg (z + 1), sq_nonneg (z - 1)]

theorem cyclicNorm_energy_lower {m : ℕ} [NeZero m] (A : Fin 4 → ZMod m → ℤ)
    (hA : ∀ i x, (A i x : ZMod 2) = 1) : 4 * (m : ℤ) ≤ cyclicNorm A 0 := by
  have hsum : (∑ x : ZMod m, ∑ i : Fin 4, (1 : ℤ)) ≤
      ∑ x : ZMod m, ∑ i : Fin 4, A i x ^ 2 := by
    exact Finset.sum_le_sum (fun x _ => Finset.sum_le_sum
      (fun i _ => odd_coefficient_square_lower (hA i x)))
  simpa [cyclicNorm, pow_two, mul_comm] using hsum

theorem cyclicNorm_solution_energy_lower {m : ℕ} [NeZero m] {t : ℤ}
    (h : CyclicNormSolution m t) : (m : ℤ) ≤ t := by
  obtain ⟨A, hA, hnorm⟩ := h
  have hlower := cyclicNorm_energy_lower A hA
  rw [hnorm] at hlower
  simp only [ite_true] at hlower
  omega

theorem cyclicNorm_augmentation {G : Type*} [Fintype G] [AddCommGroup G]
    (A : Fin 4 → G → ℤ) :
    (∑ k, cyclicNorm A k) = ∑ i, (∑ x, A i x) ^ 2 := by
  classical
  have hshift (x : G) (i : Fin 4) : (∑ k, A i (x - k)) = ∑ y, A i y := by
    let e : G ≃ G := ⟨fun k => x - k, fun k => x - k,
      fun k => by simp, fun k => by simp⟩
    exact e.sum_comp (A i)
  simp only [cyclicNorm]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun k i => A i _ * A i (_ - k)), ← Finset.mul_sum, hshift]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, pow_two]

theorem odd_coefficient_square_mod_eight {z : ℤ} (hz : (z : ZMod 2) = 1) :
    z ^ 2 % 8 = 1 := by
  have hp : z % 2 = 1 := (ZMod.intCast_eq_intCast_iff' z 1 2).mp hz
  have hr : z % 8 = 1 ∨ z % 8 = 3 ∨ z % 8 = 5 ∨ z % 8 = 7 := by omega
  rcases hr with hr | hr | hr | hr <;>
    rw [pow_two, Int.mul_emod, hr] <;> norm_num

def characterAnsatz {G : Type*} [Zero G] [DecidableEq G] (L : G → ℤ)
    (u v w : Fin 4 → ℤ) (i : Fin 4) (x : G) : ℤ :=
  u i * L x + (if x = 0 then v i else 0) + 2 * w i

theorem characterAnsatz_augmentation {m : ℕ} [NeZero m] (L : ZMod m → ℤ)
    (hL : ∑ x, L x = 0) (u v w : Fin 4 → ℤ) (i : Fin 4) :
    (∑ x, characterAnsatz L u v w i x) = v i + 2 * (m : ℤ) * w i := by
  simp [characterAnsatz, Finset.sum_add_distrib, ← Finset.mul_sum, hL]
  ring

theorem characterAnsatz_energy {m : ℕ} [NeZero m] (L : ZMod m → ℤ)
    (hzero : L 0 = 0) (hL : ∑ x, L x = 0) (henergy : ∑ x, L x ^ 2 = (m : ℤ) - 1)
    (u v w : Fin 4 → ℤ) :
    cyclicNorm (characterAnsatz L u v w) 0 =
      ∑ i, (((m : ℤ) - 1) * u i ^ 2 + v i ^ 2 + 4 * w i * v i + 4 * m * w i ^ 2) := by
  simp only [cyclicNorm, sub_zero, ← pow_two]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hpoly (x : ZMod m) : characterAnsatz L u v w i x ^ 2 =
      u i ^ 2 * L x ^ 2 + (if x = 0 then v i ^ 2 + 4 * w i * v i else 0) +
      4 * w i ^ 2 + 4 * u i * w i * L x := by
    by_cases hx : x = 0 <;> simp [characterAnsatz, hx, hzero] <;> ring
  simp_rw [hpoly]
  simp [Finset.sum_add_distrib, ← Finset.mul_sum, hL, henergy]
  ring

theorem characterAnsatz_scalar_equation {m : ℕ} [NeZero m] (hm : 1 < m)
    (L : ZMod m → ℤ) (hzero : L 0 = 0) (hL : ∑ x, L x = 0)
    (henergy : ∑ x, L x ^ 2 = (m : ℤ) - 1) (u v w : Fin 4 → ℤ) (c : ℤ)
    (hnorm : ∀ k, cyclicNorm (characterAnsatz L u v w) k = if k = 0 then c else 0) :
    (∑ i, u i ^ 2) = 4 * ∑ i, (w i * v i + (m : ℤ) * w i ^ 2) := by
  have haug := cyclicNorm_augmentation (characterAnsatz L u v w)
  simp_rw [hnorm, characterAnsatz_augmentation L hL] at haug
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at haug
  have hen := characterAnsatz_energy L hzero hL henergy u v w
  rw [hnorm] at hen
  simp only [ite_true] at hen
  have hfac : ((m : ℤ) - 1) *
      ((∑ i, u i ^ 2) - 4 * ∑ i, (w i * v i + (m : ℤ) * w i ^ 2)) = 0 := by
    simp only [Fin.sum_univ_four] at haug hen ⊢
    linear_combination haug - hen
  have hmne : (m : ℤ) - 1 ≠ 0 := by omega
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_left hmne)

theorem odd_character_scalar_equation_impossible {m : ℕ}
    (hm : (m : ZMod 2) = 1) (u v w : Fin 4 → ℤ)
    (hu : ∀ i, (u i : ZMod 2) = 1) (hv : ∀ i, (v i : ZMod 2) = 1) :
    (∑ i, u i ^ 2) ≠ 4 * ∑ i, (w i * v i + (m : ℤ) * w i ^ 2) := by
  have hsquares : (∑ i, u i ^ 2) % 8 = 4 := by
    have hc : ∀ i, ((u i ^ 2 : ℤ) : ZMod 8) = 1 := by
      intro i
      exact (ZMod.intCast_eq_intCast_iff' _ 1 8).mpr (odd_coefficient_square_mod_eight (hu i))
    have hsum : ((∑ i, u i ^ 2 : ℤ) : ZMod 8) = (4 : ℤ) := by
      simp only [Int.cast_sum, hc]
      norm_num
    exact (ZMod.intCast_eq_intCast_iff' _ 4 8).mp hsum
  have heven : (∑ i, (w i * v i + (m : ℤ) * w i ^ 2)) % 2 = 0 := by
    have hf : ∀ z : ZMod 2, z ^ 2 = z := by decide
    have hd : ∀ z : ZMod 2, z + z = 0 := by decide
    have hc (i : Fin 4) : ((w i * v i + (m : ℤ) * w i ^ 2 : ℤ) : ZMod 2) = 0 := by
      simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast, hm, hv,
        mul_one, one_mul, hf] using hd (w i : ZMod 2)
    have hsum : ((∑ i, (w i * v i + (m : ℤ) * w i ^ 2) : ℤ) : ZMod 2) = 0 := by
      simp only [Int.cast_sum, hc, Finset.sum_const_zero]
    exact (ZMod.intCast_eq_intCast_iff' _ 0 2).mp hsum
  omega

theorem zero_aligned_character_ansatz_impossible {m : ℕ} [NeZero m]
    (hm : 1 < m) (hodd : (m : ZMod 2) = 1) (L : ZMod m → ℤ)
    (hzero : L 0 = 0) (hL : ∑ x, L x = 0) (henergy : ∑ x, L x ^ 2 = (m : ℤ) - 1)
    (u v w : Fin 4 → ℤ) (hu : ∀ i, (u i : ZMod 2) = 1)
    (hv : ∀ i, (v i : ZMod 2) = 1) :
    ¬ ∃ c : ℤ, ∀ k, cyclicNorm (characterAnsatz L u v w) k = if k = 0 then c else 0 := by
  rintro ⟨c, hc⟩
  exact odd_character_scalar_equation_impossible hodd u v w hu hv
    (characterAnsatz_scalar_equation hm L hzero hL henergy u v w c hc)

theorem character_norm_moments {m : ℕ} [NeZero m] (L : ZMod m → ℤ)
    (hnorm : ∀ k, (∑ x, L x * L (x - k)) =
      (m : ℤ) * (if k = 0 then 1 else 0) - 1) :
    (∑ x, L x = 0) ∧ (∑ x, L x ^ 2 = (m : ℤ) - 1) := by
  have henergy := hnorm 0
  simp only [sub_zero, ite_true, mul_one, ← pow_two] at henergy
  have haug := cyclicNorm_augmentation
    (fun (i : Fin 4) (x : ZMod m) => if i = 0 then L x else 0)
  have hcorr (k : ZMod m) :
      cyclicNorm (fun (i : Fin 4) (x : ZMod m) => if i = 0 then L x else 0) k =
      ∑ x, L x * L (x - k) := by
    simp [cyclicNorm]
  simp_rw [hcorr, hnorm] at haug
  simp [Finset.sum_sub_distrib] at haug
  exact ⟨by nlinarith [sq_nonneg (∑ x, L x)], henergy⟩

theorem zero_aligned_norm_obstruction {m : ℕ} [NeZero m]
    (hm : 1 < m) (hodd : (m : ZMod 2) = 1) (L : ZMod m → ℤ) (hzero : L 0 = 0)
    (hcharacter : ∀ k, (∑ x, L x * L (x - k)) =
      (m : ℤ) * (if k = 0 then 1 else 0) - 1)
    (u v w : Fin 4 → ℤ) (hu : ∀ i, (u i : ZMod 2) = 1)
    (hv : ∀ i, (v i : ZMod 2) = 1) :
    ¬ ∃ c : ℤ, ∀ k, cyclicNorm (characterAnsatz L u v w) k = if k = 0 then c else 0 := by
  have h := character_norm_moments L hcharacter
  exact zero_aligned_character_ansatz_impossible hm hodd L hzero h.1 h.2 u v w hu hv

theorem cyclicNorm_solution_parity {m : ℕ} [NeZero m] {t : ℤ}
    (h : CyclicNormSolution m t) : (t : ZMod 2) = (m : ZMod 2) := by
  obtain ⟨A, hA, hnorm⟩ := h
  have hc (i : Fin 4) (x : ZMod m) : ((A i x ^ 2 : ℤ) : ZMod 8) = 1 :=
    (ZMod.intCast_eq_intCast_iff' _ 1 8).mpr (odd_coefficient_square_mod_eight (hA i x))
  have hmod : ((4 * t : ℤ) : ZMod 8) = ((4 * (m : ℤ) : ℤ) : ZMod 8) := by
    calc
      _ = ((cyclicNorm A 0 : ℤ) : ZMod 8) := by rw [hnorm]; simp
      _ = _ := by
        simp only [cyclicNorm, sub_zero, ← pow_two, Int.cast_sum, hc]
        simp
        ring
  have hres := (ZMod.intCast_eq_intCast_iff' (4 * t) (4 * m) 8).mp hmod
  apply (ZMod.intCast_eq_intCast_iff' t m 2).mpr
  omega

theorem cyclicNorm_boundary_signs {m : ℕ} [NeZero m]
    (A : Fin 4 → ZMod m → ℤ) (hA : ∀ i x, (A i x : ZMod 2) = 1)
    (henergy : cyclicNorm A 0 = 4 * (m : ℤ)) :
    ∀ i x, A i x = 1 ∨ A i x = -1 := by
  have hnonneg (x : ZMod m) (i : Fin 4) : 0 ≤ A i x ^ 2 - 1 := by
    have hh := odd_coefficient_square_lower (hA i x)
    omega
  have hsum : (∑ x : ZMod m, ∑ i : Fin 4, (A i x ^ 2 - 1)) = 0 := by
    simp only [Finset.sum_sub_distrib]
    have he : (∑ x : ZMod m, ∑ i : Fin 4, A i x ^ 2) = 4 * (m : ℤ) := by
      simpa only [cyclicNorm, sub_zero, ← pow_two] using henergy
    simp [he]
    ring
  have houter := (Finset.sum_eq_zero_iff_of_nonneg
    (fun x _ => Finset.sum_nonneg (fun i _ => hnonneg x i))).mp hsum
  intro i x
  have hinner := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => hnonneg x j)).mp (houter x (Finset.mem_univ x)) i (Finset.mem_univ i)
  have hsq : A i x ^ 2 = 1 := by omega
  by_cases hp : 0 ≤ A i x
  · left; nlinarith
  · right; nlinarith

end CompletionTheory
