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

def HasTwoFourthRootCompletingColumns {n : ℕ} (V : Matrix (Fin n) (Fin (n-2)) ℂ) : Prop :=
  ∃ R : Matrix (Fin n) (Fin 2) ℂ,(∀ i j,(R i j)^4=1) ∧
    (appendComplexColumns V R).conjTranspose*appendComplexColumns V R=
      (n:ℂ) • (1 : Matrix (Fin (n-2) ⊕ Fin 2) (Fin (n-2) ⊕ Fin 2) ℂ)

theorem quaternary_bloch_discreteness {n : ℕ} (hn : 2≤n) (heven : Even n)
    (V : Matrix (Fin n) (Fin (n-2)) ℂ) (hfour : ∀ i j,(V i j)^4=1)
    (hgram : V.conjTranspose*V=(n:ℂ) • (1 : Matrix (Fin (n-2)) (Fin (n-2)) ℂ)) :
    (∀ i j,residualBlochGram V i j= -1 ∨ residualBlochGram V i j=0 ∨ residualBlochGram V i j=1) ∧
      (residualBlochGram V).rank≤3 := by sorry

theorem quaternary_defect_two_completion_equivalence {n : ℕ} (hn : 2≤n) (heven : Even n)
    (V : Matrix (Fin n) (Fin (n-2)) ℂ) (hfour : ∀ i j,(V i j)^4=1)
    (hgram : V.conjTranspose*V=(n:ℂ) • (1 : Matrix (Fin (n-2)) (Fin (n-2)) ℂ)) :
    (HasTwoFourthRootCompletingColumns V ↔ HasTwoFlatCompletingColumns V) ∧
      (HasTwoFourthRootCompletingColumns V ↔ (residualBlochGram V).rank≤2) := by sorry

theorem automatic_quaternary_bloch_rank {n : ℕ} (hn : 2≤n) (heven : Even n)
    (V : Matrix (Fin n) (Fin (n-2)) ℂ) (hfour : ∀ i j,(V i j)^4=1)
    (hgram : V.conjTranspose*V=(n:ℂ) • (1 : Matrix (Fin (n-2)) (Fin (n-2)) ℂ)) :
    (residualBlochGram V).rank≤2 := by sorry

theorem automatic_quaternary_defect_two_completion {n : ℕ} (hn : 2≤n) (heven : Even n)
    (V : Matrix (Fin n) (Fin (n-2)) ℂ) (hfour : ∀ i j,(V i j)^4=1)
    (hgram : V.conjTranspose*V=(n:ℂ) • (1 : Matrix (Fin (n-2)) (Fin (n-2)) ℂ)) :
    HasTwoFourthRootCompletingColumns V := by sorry

end
end CompletionTheory.Bloch
