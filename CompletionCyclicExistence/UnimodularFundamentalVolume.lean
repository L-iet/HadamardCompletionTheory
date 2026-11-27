/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Tactic.Linarith
@[expose] public section
namespace CompletionTheory.ThreeSquares
open Module MeasureTheory

 theorem unimodular_gram_fundamental_volume {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b : Basis ι ℝ E)
    (hdet : (Matrix.gram ℝ b).det=1) : volume (ZSpan.fundamentalDomain b)=1 := by
  classical
  have hcard : Fintype.card (Fin (finrank ℝ E))=Fintype.card ι := by
    simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis b
  let o : OrthonormalBasis ι ℝ E :=
    (stdOrthonormalBasis ℝ E).reindex (Fintype.equivOfCardEq hcard)
  let Y : Matrix ι ι ℝ := o.toBasis.toMatrix b
  have hg : Matrix.gram ℝ b=Y.transpose*Y := by
    have hh := Matrix.gram_eq_conjTranspose_mul o b
    dsimp only at hh
    have hm : (Matrix.of (fun i j : ι => o.repr (b j) i))=Y := by
      ext i j
      rfl
    rw [hm,Matrix.conjTranspose_eq_transpose_of_trivial] at hh
    exact hh
  have hsq : Y.det^2=1 := by
    have hh := congrArg Matrix.det hg
    rw [Matrix.det_mul,Matrix.det_transpose,hdet] at hh
    nlinarith
  have habs : |o.toBasis.det b|=1 := by
    rw [Module.Basis.det_apply]
    change |Y.det|=1
    nlinarith [sq_abs Y.det,abs_nonneg Y.det]
  rw [ZSpan.measure_fundamentalDomain b volume o.toBasis,habs,
    ENNReal.ofReal_one,one_mul]
  rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume)]
  exact o.volume_parallelepiped

end CompletionTheory.ThreeSquares
