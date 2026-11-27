/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionBloch.AxisDiagonalization
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory.Bloch
noncomputable section
open scoped BigOperators ComplexConjugate

def rowMatrix (r : Fin 2 → ℂ) : Matrix Unit (Fin 2) ℂ := fun _ j => r j
def rowRight (r : Fin 2 → ℂ) (U : Matrix (Fin 2) (Fin 2) ℂ) : Fin 2 → ℂ :=
  fun j => ∑ i,r i*U i j
def rowQuadratic (r : Fin 2 → ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  ∑ i,∑ j,r i*A i j*conj (r j)

theorem rowMatrix_right (r : Fin 2 → ℂ) (U : Matrix (Fin 2) (Fin 2) ℂ) :
    rowMatrix (rowRight r U)=rowMatrix r*U := rfl

theorem rowMatrix_gram (r : Fin 2 → ℂ) :
    (rowMatrix r*(rowMatrix r).conjTranspose) () ()=(rowNormSq r:ℂ) := by
  simp [rowMatrix,rowNormSq,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Fin.sum_univ_succ,Complex.mul_conj]

theorem rowMatrix_quadratic (r : Fin 2 → ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (rowMatrix r*A*(rowMatrix r).conjTranspose) () ()=rowQuadratic r A := by
  simp [rowMatrix,rowQuadratic,Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_succ]
  ring

theorem rowRight_norm (r : Fin 2 → ℂ) (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U*U.conjTranspose=1) : rowNormSq (rowRight r U)=rowNormSq r := by
  have hh : rowMatrix (rowRight r U)*(rowMatrix (rowRight r U)).conjTranspose=
      rowMatrix r*(rowMatrix r).conjTranspose := by
    rw [rowMatrix_right,Matrix.conjTranspose_mul]
    calc
      _ = rowMatrix r*(U*U.conjTranspose)*(rowMatrix r).conjTranspose := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU,Matrix.mul_one]
  have he := congrArg (fun M : Matrix Unit Unit ℂ => M () ()) hh
  rw [rowMatrix_gram,rowMatrix_gram] at he
  exact_mod_cast he

theorem rowRight_quadratic (r : Fin 2 → ℂ) (U A D : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A=U*D*U.conjTranspose) :
    rowQuadratic (rowRight r U) D=rowQuadratic r A := by
  have hh : rowMatrix (rowRight r U)*D*(rowMatrix (rowRight r U)).conjTranspose=
      rowMatrix r*A*(rowMatrix r).conjTranspose := by
    rw [rowMatrix_right,Matrix.conjTranspose_mul,hA]
    simp only [Matrix.mul_assoc]
  have he := congrArg (fun M : Matrix Unit Unit ℂ => M () ()) hh
  simpa only [rowMatrix_quadratic] using he

theorem rowQuadratic_opposite_diagonal (r : Fin 2 → ℂ) (a : ℝ) :
    rowQuadratic r (Matrix.diagonal ![(a:ℂ),-(a:ℂ)])=
      (a*(Complex.normSq (r 0)-Complex.normSq (r 1)):ℂ) := by
  apply Complex.ext <;>
    simp [rowQuadratic,Matrix.diagonal_apply,Fin.sum_univ_succ,Complex.normSq_apply,
      Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im] <;> ring

theorem flat_rows_after_axis_rotation (s : Fin 3 → ℝ) (hs : dot3 s s=1) :
    ∃ U : Matrix (Fin 2) (Fin 2) ℂ,
      U*U.conjTranspose=1 ∧ U.conjTranspose*U=1 ∧
      ∀ r : Fin 2 → ℂ,rowNormSq r=2 → dot3 (blochVector r) s=0 →
        ∀ j,Complex.normSq (rowRight r U j)=1 := by
  obtain ⟨U,hU,hUc,a,ha,hdiag⟩ := unit_axis_diagonalization s hs
  let D : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![(a:ℂ),-(a:ℂ)]
  have hA : axisMatrix s=U*D*U.conjTranspose := by
    calc
      _ = (U*U.conjTranspose)*axisMatrix s*(U*U.conjTranspose) := by rw [hU]; simp
      _ = U*(U.conjTranspose*axisMatrix s*U)*U.conjTranspose := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hdiag]
  refine ⟨U,hU,hUc,?_⟩
  intro r hr hperp j
  have hnorm : rowNormSq (rowRight r U)=2 := (rowRight_norm r U hU).trans hr
  have hzero : rowQuadratic r (axisMatrix s)=0 := by
    change (∑ i,∑ j,r i*axisMatrix s i j*conj (r j))=0
    rw [axis_expectation,hperp]
    simp
  have he := rowRight_quadratic r U (axisMatrix s) D hA
  rw [hzero] at he
  change rowQuadratic (rowRight r U) (Matrix.diagonal ![(a:ℂ),-(a:ℂ)])=0 at he
  rw [rowQuadratic_opposite_diagonal] at he
  have hz : a*(Complex.normSq (rowRight r U 0)-Complex.normSq (rowRight r U 1))=0 := by exact_mod_cast he
  have heq := (mul_eq_zero.mp hz).resolve_left ha
  unfold rowNormSq at hnorm
  have h0 : Complex.normSq (rowRight r U 0)=1 := by linarith
  have h1 : Complex.normSq (rowRight r U 1)=1 := by linarith
  fin_cases j
  · exact h0
  · exact h1

end
end CompletionTheory.Bloch
