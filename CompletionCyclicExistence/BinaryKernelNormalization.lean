/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCyclicExistence.PositiveUnitKernel
public import CompletionCyclicExistence.UnitOrthonormalBasis
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory.ThreeSquares
open Module

 theorem positive_binary_orthonormal_basis_of_unit (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hpos : (A.map (fun a : ℤ => (a:ℝ))).PosDef) (hdet : A.det=1)
    (v : Fin 2 → ℤ) (hvB : Matrix.toBilin' A v v=1) :
    ∃ b : Basis (Fin 2) ℤ (Fin 2 → ℤ),∀ i j,
      Matrix.toBilin' A (b i) (b j)=if i=j then 1 else 0 := by
  classical
  obtain ⟨k,hkDet,_⟩ := integral_positive_unit_kernel 2 A hpos hdet v hvB
  have h00 : Matrix.toBilin' A (k 0) (k 0)=1 := by
    have he := Matrix.det_fin_one (Matrix.of (fun i j : Fin 1 => Matrix.toBilin' A (k i) (k j)))
    exact he.symm.trans hkDet
  have hk : ∀ i j,Matrix.toBilin' A (k i) (k j)=if i=j then 1 else 0 := by
    intro i j
    have hi : i=0 := by apply Fin.ext; have h := i.isLt; omega
    have hj : j=0 := by apply Fin.ext; have h := j.isLt; omega
    subst i
    subst j
    simpa using h00
  have hsym : A.IsSymm := by
    ext i j
    have hi := congrFun (congrFun hpos.isHermitian.eq i) j
    have hr : (A j i:ℝ)=(A i j:ℝ) := by simpa using hi
    exact_mod_cast hr
  have hB := Matrix.isSymm_toBilin'_iff_isSymm.mpr hsym
  let b := unitAdaptedBasis (Matrix.toBilin' A v) v hvB k
  have hb := unit_adapted_basis_orthonormal (Matrix.toBilin' A) v hvB
    (fun x y => by simpa using hB.eq x y) k hk
  let e : (Unit ⊕ Fin (2-1)) ≃ Fin 2 := Fintype.equivOfCardEq (by simp)
  exact ⟨b.reindex e,integral_orthonormal_basis_reindex (Matrix.toBilin' A) b e hb⟩

end CompletionTheory.ThreeSquares
