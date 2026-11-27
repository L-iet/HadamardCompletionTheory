/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionBloch.BlochAlgebra
public import Mathlib.Analysis.Matrix.Spectrum
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory.Bloch
noncomputable section

theorem unit_axis_diagonalization (s : Fin 3 → ℝ) (hs : dot3 s s=1) :
    ∃ U : Matrix (Fin 2) (Fin 2) ℂ,
      U*U.conjTranspose=1 ∧ U.conjTranspose*U=1 ∧
      ∃ a : ℝ,a≠0 ∧ U.conjTranspose*axisMatrix s*U=Matrix.diagonal ![(a:ℂ),-(a:ℂ)] := by
  let A := axisMatrix s
  have hA : A.IsHermitian := axisMatrix_hermitian s
  let U : Matrix (Fin 2) (Fin 2) ℂ := hA.eigenvectorUnitary
  have hU : U*U.conjTranspose=1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hUc : U.conjTranspose*U=1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  let D : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal fun i => (hA.eigenvalues i:ℂ)
  have hD : U.conjTranspose*A*U=D := by
    have hh := hA.conjStarAlgAut_star_eigenvectorUnitary
    simp only [Unitary.conjStarAlgAut_star_apply,Matrix.star_eq_conjTranspose] at hh
    convert hh using 1 <;> ext i j <;> simp [U,D,Function.comp_def]
  have hA2 : A*A=1 := by
    change axisMatrix s*axisMatrix s=1
    rw [axisMatrix_square,hs]
    simp
  have hD2 : D*D=1 := by
    rw [←hD]
    calc
      _ = U.conjTranspose*(A*(U*U.conjTranspose)*A)*U := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU,Matrix.mul_one,hA2,Matrix.mul_one,hUc]
  have he0 : (hA.eigenvalues 0)^2=1 := by
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hD2
    have hh' : (hA.eigenvalues 0:ℂ)^2=1 := by
      simpa [D,Matrix.mul_apply,Fin.sum_univ_succ,pow_two] using hh
    exact_mod_cast hh'
  have htr : A.trace=0 := by simp [A,axisMatrix,Matrix.trace,Fin.sum_univ_succ]
  have hOpposite : hA.eigenvalues 1= -hA.eigenvalues 0 := by
    have hh := hA.trace_eq_sum_eigenvalues
    rw [htr] at hh
    have hr := congrArg Complex.re hh
    simp [Fin.sum_univ_succ] at hr
    linarith
  refine ⟨U,hU,hUc,hA.eigenvalues 0,?_,?_⟩
  · intro hz
    rw [hz] at he0
    norm_num at he0
  · rw [hD]
    change Matrix.diagonal (fun i => (hA.eigenvalues i:ℂ))=Matrix.diagonal ![(hA.eigenvalues 0:ℂ),-(hA.eigenvalues 0:ℂ)]
    congr 1
    funext i
    fin_cases i <;> simp [hOpposite]

end
end CompletionTheory.Bloch
