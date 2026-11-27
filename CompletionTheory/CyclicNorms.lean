/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module

public import Mathlib.NumberTheory.SumFourSquares
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring

/-! # Integer cyclic Hermitian norms and constant orthogonal mixing -/

@[expose] public section
namespace CompletionTheory

def quaternionMix {G : Type*} (a b c d : ℤ) (A : Fin 4 → G → ℤ) : Fin 4 → G → ℤ :=
  ![fun x => a * A 0 x + b * A 1 x + c * A 2 x + d * A 3 x,
    fun x => -b * A 0 x + a * A 1 x - d * A 2 x + c * A 3 x,
    fun x => -c * A 0 x + d * A 1 x + a * A 2 x - b * A 3 x,
    fun x => -d * A 0 x - c * A 1 x + b * A 2 x + a * A 3 x]

theorem quaternionMix_pair {G : Type*} (a b c d : ℤ) (A : Fin 4 → G → ℤ) (x y : G) :
    (∑ i, quaternionMix a b c d A i x * quaternionMix a b c d A i y) =
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * ∑ i, A i x * A i y := by
  simp [Fin.sum_univ_succ, quaternionMix]
  ring

def cyclicNorm {G : Type*} [Fintype G] [Sub G] (A : Fin 4 → G → ℤ) (k : G) : ℤ :=
  ∑ x, ∑ i, A i x * A i (x - k)

theorem cyclicNorm_mix {G : Type*} [Fintype G] [Sub G]
    (a b c d : ℤ) (A : Fin 4 → G → ℤ) (k : G) :
    cyclicNorm (quaternionMix a b c d A) k =
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * cyclicNorm A k := by
  simp only [cyclicNorm, quaternionMix_pair, Finset.mul_sum]

theorem quaternionMix_odd {G : Type*} (a b c d : ℤ) (A : Fin 4 → G → ℤ)
    (hA : ∀ i x, (A i x : ZMod 2) = 1)
    (hodd : (a + b + c + d : ZMod 2) = 1) :
    ∀ i x, (quaternionMix a b c d A i x : ZMod 2) = 1 := by
  intro i x
  have hn : ∀ z : ZMod 2, -z = z := by decide
  fin_cases i <;> simp [quaternionMix, hA, sub_eq_add_neg, hn] <;>
    convert hodd using 1 <;> ring

def CyclicNormSolution (m : ℕ) [NeZero m] (t : ℤ) : Prop :=
  ∃ A : Fin 4 → ZMod m → ℤ, (∀ i x, (A i x : ZMod 2) = 1) ∧
    ∀ k, cyclicNorm A k = if k = 0 then 4 * t else 0

theorem cyclicNorm_odd_multiplier {m : ℕ} [NeZero m] {t : ℤ}
    (h : CyclicNormSolution m t) (s : ℕ) (hs : (s : ZMod 2) = 1) :
    CyclicNormSolution m ((s : ℤ) * t) := by
  obtain ⟨a, b, c, d, habcd⟩ := Nat.sum_four_squares s
  have hz : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2 = s := by
    exact_mod_cast habcd
  have hf : ∀ x : ZMod 2, x ^ 2 = x := by decide
  have hp : ((a : ℤ) + b + c + d : ZMod 2) = 1 := by
    have hh := congrArg (fun n : ℕ => (n : ZMod 2)) habcd
    simpa only [Nat.cast_add, Nat.cast_pow, hf, hs, Int.cast_add, Int.cast_natCast] using hh
  obtain ⟨A, hA, hnorm⟩ := h
  refine ⟨quaternionMix a b c d A, quaternionMix_odd _ _ _ _ A hA hp, ?_⟩
  intro k
  rw [cyclicNorm_mix, hz, hnorm]
  split_ifs <;> ring

end CompletionTheory
