/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionBloch.ResidualFactor
public import CompletionBloch.GramAxis
@[expose] public section
namespace CompletionTheory.Bloch
noncomputable section
open scoped BigOperators

def complexResidualGram {n : ℕ} (V : Matrix (Fin n) (Fin (n-2)) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (n:ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)-V*V.conjTranspose

def residualBlochGram {n : ℕ} (V : Matrix (Fin n) (Fin (n-2)) ℂ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => Complex.normSq (complexResidualGram V i j)/2-1

theorem residual_bloch_unit_gram {n : ℕ} (hn : 2≤n)
    (V : Matrix (Fin n) (Fin (n-2)) ℂ)
    (hflat : ∀ i j,Complex.normSq (V i j)=1)
    (hgram : V.conjTranspose*V=(n:ℂ) • (1 : Matrix (Fin (n-2)) (Fin (n-2)) ℂ)) :
    ∃ b : Matrix (Fin n) (Fin 3) ℝ,
      (∀ i,dot3 (b i) (b i)=1) ∧ residualBlochGram V=b*b.transpose := by
  obtain ⟨R,hRg,hres⟩ := complex_residual_factor hn V hgram
  have hnorm := complex_residual_row_norm_two hn V R hflat hres
  let b : Matrix (Fin n) (Fin 3) ℝ := fun i => blochVector (R i)
  refine ⟨b,fun i => bloch_unit_of_row_norm_two (R i) (hnorm i),?_⟩
  ext i j
  have he : rowInner (R i) (R j)=complexResidualGram V i j := by
    have hh := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) hres
    simpa [rowInner,complexResidualGram,Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_succ] using hh
  change Complex.normSq (complexResidualGram V i j)/2-1=dot3 (blochVector (R i)) (blochVector (R j))
  rw [←he]
  exact (bloch_gram_of_row_norm_two (R i) (R j) (hnorm i) (hnorm j)).symm

theorem residual_bloch_rank_le_three {n : ℕ} (hn : 2≤n)
    (V : Matrix (Fin n) (Fin (n-2)) ℂ)
    (hflat : ∀ i j,Complex.normSq (V i j)=1)
    (hgram : V.conjTranspose*V=(n:ℂ) • (1 : Matrix (Fin (n-2)) (Fin (n-2)) ℂ)) :
    (residualBlochGram V).rank≤3 := by
  obtain ⟨b,_,hb⟩ := residual_bloch_unit_gram hn V hflat hgram
  rw [hb,Matrix.rank_self_mul_transpose]
  exact Matrix.rank_le_width b

end
end CompletionTheory.Bloch
