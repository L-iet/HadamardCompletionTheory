/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
@[expose] public section
namespace CompletionTheory.Bloch
noncomputable section
open scoped BigOperators ComplexConjugate

def rowNormSq (r : Fin 2 → ℂ) : ℝ := Complex.normSq (r 0)+Complex.normSq (r 1)
def rowInner (r s : Fin 2 → ℂ) : ℂ := r 0*conj (s 0)+r 1*conj (s 1)
def blochVector (r : Fin 2 → ℂ) : Fin 3 → ℝ :=
  ![(r 0*conj (r 1)).re,(r 0*conj (r 1)).im,(Complex.normSq (r 0)-Complex.normSq (r 1))/2]
def dot3 (s t : Fin 3 → ℝ) : ℝ := ∑ i,s i*t i

theorem bloch_gram_identity (r s : Fin 2 → ℂ) :
    dot3 (blochVector r) (blochVector s)=
      Complex.normSq (rowInner r s)/2-rowNormSq r*rowNormSq s/4 := by
  simp [dot3,blochVector,rowInner,rowNormSq,Fin.sum_univ_succ,Complex.normSq_apply,
    Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im]
  ring

theorem bloch_norm_identity (r : Fin 2 → ℂ) :
    dot3 (blochVector r) (blochVector r)=(rowNormSq r)^2/4 := by
  simp [dot3,blochVector,rowNormSq,Fin.sum_univ_succ,Complex.normSq_apply,
    Complex.mul_re,Complex.mul_im]
  ring

theorem bloch_unit_of_row_norm_two (r : Fin 2 → ℂ) (hr : rowNormSq r=2) :
    dot3 (blochVector r) (blochVector r)=1 := by
  rw [bloch_norm_identity,hr]
  norm_num

theorem bloch_gram_of_row_norm_two (r s : Fin 2 → ℂ)
    (hr : rowNormSq r=2) (hs : rowNormSq s=2) :
    dot3 (blochVector r) (blochVector s)=Complex.normSq (rowInner r s)/2-1 := by
  rw [bloch_gram_identity,hr,hs]
  ring

def axisMatrix (s : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(s 2:ℂ),(s 0:ℂ)-Complex.I*(s 1:ℂ);
     (s 0:ℂ)+Complex.I*(s 1:ℂ),-(s 2:ℂ)]

theorem axisMatrix_hermitian (s : Fin 3 → ℝ) : (axisMatrix s).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [axisMatrix,Matrix.conjTranspose_apply] <;> ring

theorem axisMatrix_square (s : Fin 3 → ℝ) :
    axisMatrix s*axisMatrix s=(dot3 s s:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [axisMatrix,Matrix.mul_apply,Fin.sum_univ_succ,dot3,Matrix.smul_apply,
      smul_eq_mul,Matrix.one_apply,Complex.mul_re,Complex.mul_im] <;> ring

theorem axis_expectation (r : Fin 2 → ℂ) (s : Fin 3 → ℝ) :
    (∑ i : Fin 2,∑ j : Fin 2,r i*axisMatrix s i j*conj (r j))=
      (2*dot3 (blochVector r) s:ℂ) := by
  apply Complex.ext <;>
    simp [axisMatrix,dot3,blochVector,Fin.sum_univ_succ,Complex.normSq_apply,
      Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im] <;> ring

end
end CompletionTheory.Bloch
