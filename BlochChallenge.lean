/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Data.Fin.VecNotation
@[expose] public section
namespace CompletionTheory.Bloch
noncomputable section
open scoped BigOperators

def dot3 (s t : Fin 3 → ℝ) : ℝ := ∑ i,s i*t i

def complexResidualGram {n : ℕ} (V : Matrix (Fin n) (Fin (n-2)) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (n:ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)-V*V.conjTranspose

def residualBlochGram {n : ℕ} (V : Matrix (Fin n) (Fin (n-2)) ℂ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => Complex.normSq (complexResidualGram V i j)/2-1

def appendComplexColumns {n : ℕ} (V : Matrix (Fin n) (Fin (n-2)) ℂ)
    (R : Matrix (Fin n) (Fin 2) ℂ) : Matrix (Fin n) (Fin (n-2) ⊕ Fin 2) ℂ :=
  fun i j => Sum.elim (V i) (R i) j

def HasTwoFlatCompletingColumns {n : ℕ} (V : Matrix (Fin n) (Fin (n-2)) ℂ) : Prop :=
  ∃ R : Matrix (Fin n) (Fin 2) ℂ,(∀ i j,Complex.normSq (R i j)=1) ∧
    (appendComplexColumns V R).conjTranspose*appendComplexColumns V R=
      (n:ℂ) • (1 : Matrix (Fin (n-2) ⊕ Fin 2) (Fin (n-2) ⊕ Fin 2) ℂ)

theorem residual_bloch_unit_gram {n : ℕ} (hn : 2≤n)
    (V : Matrix (Fin n) (Fin (n-2)) ℂ)
    (hflat : ∀ i j,Complex.normSq (V i j)=1)
    (hgram : V.conjTranspose*V=(n:ℂ) • (1 : Matrix (Fin (n-2)) (Fin (n-2)) ℂ)) :
    ∃ b : Matrix (Fin n) (Fin 3) ℝ,
      (∀ i,dot3 (b i) (b i)=1) ∧ residualBlochGram V=b*b.transpose := by sorry

theorem complex_defect_two_rank_criterion {n : ℕ} (hn : 2≤n)
    (V : Matrix (Fin n) (Fin (n-2)) ℂ)
    (hflat : ∀ i j,Complex.normSq (V i j)=1)
    (hgram : V.conjTranspose*V=(n:ℂ) • (1 : Matrix (Fin (n-2)) (Fin (n-2)) ℂ)) :
    HasTwoFlatCompletingColumns V ↔ (residualBlochGram V).rank≤2 := by sorry

end
end CompletionTheory.Bloch
