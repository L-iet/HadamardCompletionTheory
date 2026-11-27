/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCyclicExistence.UnitKernelDeterminant
public import CompletionCyclicExistence.IntegralFamilyGram
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory.ThreeSquares
open Module

 theorem integral_positive_unit_kernel (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hpos : (A.map (fun a : ℤ => (a:ℝ))).PosDef) (hdet : A.det=1)
    (v : Fin n → ℤ) (hv : Matrix.toBilin' A v v=1) :
    ∃ k : Basis (Fin (n-1)) ℤ (LinearMap.ker (Matrix.toBilin' A v)),
      Matrix.det (fun i j => Matrix.toBilin' A (k i) (k j))=1 ∧
      ((Matrix.of (fun i j => Matrix.toBilin' A (k i) (k j))).map
        (fun a : ℤ => (a:ℝ))).PosDef := by
  classical
  have hsym : A.IsSymm := by
    ext i j
    have hi := congrFun (congrFun hpos.isHermitian.eq i) j
    have hr : (A j i:ℝ)=(A i j:ℝ) := by simpa using hi
    exact_mod_cast hr
  have hB := Matrix.isSymm_toBilin'_iff_isSymm.mpr hsym
  have hstd : (LinearMap.BilinForm.toMatrix (Pi.basisFun ℤ (Fin n))
      (Matrix.toBilin' A)).det=1 := by
    simpa only [LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin'] using hdet
  obtain ⟨k,hk⟩ := unit_kernel_unimodular n (Matrix.toBilin' A) v hv
    (fun x y => by simpa using hB.eq x y) hstd
  refine ⟨k,hk,?_⟩
  exact integral_family_gram_positive A (fun i => (k i:Fin n → ℤ)) hpos.posSemidef hk

end CompletionTheory.ThreeSquares
