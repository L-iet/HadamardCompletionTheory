/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCyclicExistence.BinaryUnimodularNormalForm
public import CompletionCyclicExistence.KernelGramCoordinates
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory.ThreeSquares
open Module

 theorem positive_ternary_orthonormal_basis_of_unit (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hpos : (A.map (fun a : ℤ => (a:ℝ))).PosDef) (hdet : A.det=1)
    (v : Fin 3 → ℤ) (hv : Matrix.toBilin' A v v=1) :
    ∃ b : Basis (Fin 3) ℤ (Fin 3 → ℤ),∀ i j,
      Matrix.toBilin' A (b i) (b j)=if i=j then 1 else 0 := by
  classical
  obtain ⟨k,hkDet,hkPos⟩ := integral_positive_unit_kernel 3 A hpos hdet v hv
  let K : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of (fun i j => Matrix.toBilin' A (k i) (k j))
  obtain ⟨c,hc⟩ := positive_binary_unimodular_orthonormal_basis K hkPos hkDet
  let k' : Basis (Fin 2) ℤ (LinearMap.ker (Matrix.toBilin' A v)) := c.map k.equivFun.symm
  have hk' : ∀ i j,Matrix.toBilin' A (k' i) (k' j)=if i=j then 1 else 0 := by
    intro i j
    have he := kernel_gram_coordinates (Matrix.toBilin' A) (Matrix.toBilin' A v) k (c i) (c j)
    have hh := he.symm.trans (hc i j)
    simpa only [k',Basis.map_apply] using hh
  have hsym : A.IsSymm := by
    ext i j
    have hi := congrFun (congrFun hpos.isHermitian.eq i) j
    have hr : (A j i:ℝ)=(A i j:ℝ) := by simpa using hi
    exact_mod_cast hr
  have hB := Matrix.isSymm_toBilin'_iff_isSymm.mpr hsym
  let b := unitAdaptedBasis (Matrix.toBilin' A v) v hv k'
  have hb := unit_adapted_basis_orthonormal (Matrix.toBilin' A) v hv
    (fun x y => by simpa using hB.eq x y) k' hk'
  let e : (Unit ⊕ Fin 2) ≃ Fin 3 := Fintype.equivOfCardEq (by simp)
  exact ⟨b.reindex e,integral_orthonormal_basis_reindex (Matrix.toBilin' A) b e hb⟩

end CompletionTheory.ThreeSquares
