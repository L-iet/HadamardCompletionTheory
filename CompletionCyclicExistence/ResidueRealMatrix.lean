/-
Reference construction: AFP Three_Squares, by Anna Danilkin and Loic Chevalier.
Lean translation and additional real-form algebra: Copyright (c) 2026 Joshua Mark.
Released under BSD-3-Clause; see AFP-LICENSE-BSD.txt in this directory.
This is a checked-support development, not the three-square theorem.
-/
module
public import CompletionCyclicExistence.ResidueMatrix
public import Mathlib.LinearAlgebra.Matrix.PosDef
@[expose] public section
namespace CompletionTheory.ThreeSquares
open scoped BigOperators Matrix

def residueRealMatrix (n d x y : ℤ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (residueMatrix n d x y i j:ℝ)

 theorem residue_real_determinant (n d x y : ℤ) (h : x^2+d=y*(d*n-1)) :
    (residueRealMatrix n d x y).det=1 := by
  have he : ((residueMatrix n d x y).det:ℝ)=(residueRealMatrix n d x y).det := by
    refine (Int.cast_det (R:=ℝ) (residueMatrix n d x y)).trans ?_
    apply congrArg Matrix.det
    ext i j
    rfl
  rw [←he,residueMatrix_determinant n d x y h,Int.cast_one]

 theorem residue_real_quadratic_identity (n d x y : ℤ) (h : x^2+d=y*(d*n-1))
    (v : Fin 3 → ℝ) :
    (y:ℝ)*(d:ℝ)*(v ⬝ᵥ ((residueRealMatrix n d x y)*ᵥv))=
      (d:ℝ)*((y:ℝ)*v 0+(x:ℝ)*v 1+v 2)^2+
      ((d:ℝ)*v 1-(x:ℝ)*v 2)^2+(y:ℝ)*(v 2)^2 := by
  have hR : (x:ℝ)^2+(d:ℝ)=(y:ℝ)*((d:ℝ)*(n:ℝ)-1) := by exact_mod_cast h
  have he :
      (d:ℝ)*((y:ℝ)*v 0+(x:ℝ)*v 1+v 2)^2+
      ((d:ℝ)*v 1-(x:ℝ)*v 2)^2+(y:ℝ)*(v 2)^2-
      (y:ℝ)*(d:ℝ)*(v ⬝ᵥ ((residueRealMatrix n d x y)*ᵥv))=
      ((x:ℝ)^2+(d:ℝ)-(y:ℝ)*((d:ℝ)*(n:ℝ)-1))*((d:ℝ)*(v 1)^2+(v 2)^2) := by
    simp [residueRealMatrix,residueMatrix,dotProduct,Matrix.mulVec,Fin.sum_univ_three]
    push_cast
    ring
  rw [sub_eq_zero.mpr hR,zero_mul] at he
  exact (sub_eq_zero.mp he).symm

 theorem residue_real_positive_definite (n d x y : ℤ) (hn : 2≤n) (hd : 0<d)
    (h : x^2+d=y*(d*n-1)) : (residueRealMatrix n d x y).PosDef := by
  have ha : 0<d*n-1 := by nlinarith
  have hy : 0<y := by
    by_contra hy
    have hy0 : y≤0 := by omega
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hy0 ha.le,sq_nonneg x]
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hyR : (0:ℝ)<y := by exact_mod_cast hy
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  constructor
  · change (residueRealMatrix n d x y).conjTranspose=residueRealMatrix n d x y
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro v hv
    have hA : 0≤(d:ℝ)*((y:ℝ)*v 0+(x:ℝ)*v 1+v 2)^2 := mul_nonneg hdR.le (sq_nonneg _)
    have hB : 0≤((d:ℝ)*v 1-(x:ℝ)*v 2)^2 := sq_nonneg _
    have hC : 0≤(y:ℝ)*(v 2)^2 := mul_nonneg hyR.le (sq_nonneg _)
    have hpos : 0<(d:ℝ)*((y:ℝ)*v 0+(x:ℝ)*v 1+v 2)^2+
        ((d:ℝ)*v 1-(x:ℝ)*v 2)^2+(y:ℝ)*(v 2)^2 := by
      by_cases h2 : v 2=0
      · by_cases h1 : v 1=0
        · have h0 : v 0≠0 := by
            intro h0
            apply hv
            funext i
            fin_cases i <;> simp [h0,h1,h2]
          have hf : 0<(d:ℝ)*((y:ℝ)*v 0+(x:ℝ)*v 1+v 2)^2 := by
            apply mul_pos hdR
            apply sq_pos_of_ne_zero
            simpa [h1,h2] using mul_ne_zero hyR.ne' h0
          exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hf hB) hC
        · have hm : 0<((d:ℝ)*v 1-(x:ℝ)*v 2)^2 := by
            apply sq_pos_of_ne_zero
            simpa [h2] using mul_ne_zero hdR.ne' h1
          exact add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos hA hm) hC
      · exact add_pos_of_nonneg_of_pos (add_nonneg hA hB) (mul_pos hyR (sq_pos_of_ne_zero h2))
    have hm : 0<(y:ℝ)*(d:ℝ)*(v ⬝ᵥ ((residueRealMatrix n d x y)*ᵥv)) := by
      rw [residue_real_quadratic_identity n d x y h v]
      exact hpos
    have hq : 0<v ⬝ᵥ ((residueRealMatrix n d x y)*ᵥv) := by
      by_contra he
      have hn : v ⬝ᵥ ((residueRealMatrix n d x y)*ᵥv)≤0 := le_of_not_gt he
      have he := mul_nonpos_of_nonneg_of_nonpos (mul_pos hyR hdR).le hn
      linarith
    simpa only [star_trivial] using hq

end CompletionTheory.ThreeSquares
