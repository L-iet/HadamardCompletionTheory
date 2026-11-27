/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionQuaternary.EquatorialPhases
public import CompletionQuaternary.QuaternaryEdge
@[expose] public section
namespace CompletionTheory.Bloch
noncomputable section
open scoped ComplexConjugate

theorem quantize_flat_rows {ι : Type*} [Nonempty ι] (R : ι → Fin 2 → ℂ)
    (hflat : ∀ i j,Complex.normSq (R i j)=1)
    (hB : ∀ i j,dot3 (blochVector (R i)) (blochVector (R j))= -1 ∨
      dot3 (blochVector (R i)) (blochVector (R j))=0 ∨
      dot3 (blochVector (R i)) (blochVector (R j))=1)
    (hGaussian : ∀ i j,GaussianEven (rowInner (R i) (R j))) :
    ∃ Q : ι → Fin 2 → ℂ,(∀ i j,(Q i j)^4=1) ∧
      ∀ i j,rowInner (Q i) (Q j)=rowInner (R i) (R j) := by
  obtain ⟨a,d,ha,hd,hform⟩ := flat_rows_quantized_equator R hflat hB
  have hedge (i j : ι) (hne : rowInner (R i) (R j)≠0) : (a i*conj (a j))^4=1 :=
    quaternary_edge_phase (hGaussian i j) hne (ha i) (ha j) (hd i) (hd j) (hform i j)
  obtain ⟨b,hb,hgram⟩ := rephase_by_fourth_power a d (fun i j => rowInner (R i) (R j)) ha hform hedge
  let Q (i : ι) : Fin 2 → ℂ := ![b i,b i*d i]
  refine ⟨Q,?_,?_⟩
  · intro i j
    fin_cases j
    · exact hb i
    · change (b i*d i)^4=1
      rw [mul_pow,hb i,hd i,mul_one]
  · intro i j
    calc
      _ = b i*conj (b j)*(1+d i*conj (d j)) := by
        simp [Q,rowInner,map_mul] <;> ring
      _ = _ := hgram i j

end
end CompletionTheory.Bloch
