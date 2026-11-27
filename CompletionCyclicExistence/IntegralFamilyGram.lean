/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCyclicExistence.IntegralPositiveCongruence
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory.ThreeSquares
open scoped BigOperators Matrix

 theorem integral_family_gram_congruence {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (x : κ → ι → ℤ) :
    (Matrix.of (fun i j => Matrix.toBilin' A (x i) (x j)))=
      (Matrix.of (fun i j => x j i))ᵀ*A*(Matrix.of (fun i j => x j i)) := by
  ext i j
  simp only [Matrix.of_apply]
  rw [Matrix.toBilin'_apply]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.of_apply,Finset.sum_mul]
  exact Finset.sum_comm

 theorem integral_family_gram_positive {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (A : Matrix ι ι ℤ) (x : κ → ι → ℤ)
    (hA : (A.map (fun a : ℤ => (a:ℝ))).PosSemidef)
    (hdet : Matrix.det (Matrix.of (fun i j => Matrix.toBilin' A (x i) (x j)))=1) :
    (Matrix.of (fun i j => Matrix.toBilin' A (x i) (x j))).map
      (fun a : ℤ => (a:ℝ)) |>.PosDef := by
  have he := integral_family_gram_congruence A x
  rw [he] at hdet ⊢
  exact integral_positive_congruence A (fun i j => x j i) hA hdet

end CompletionTheory.ThreeSquares
