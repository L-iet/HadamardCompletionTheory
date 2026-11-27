/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionQuaternary.PhaseRephasing
public import CompletionQuaternary.GaussianParity
@[expose] public section
namespace CompletionTheory.Bloch
noncomputable section
open scoped ComplexConjugate

theorem unit_discrete_real_fourth {z : ℂ} (hz : Complex.normSq z=1)
    (hr : z.re= -1 ∨ z.re=0 ∨ z.re=1) : z^4=1 := by
  have hn : z.re^2+z.im^2=1 := by simpa [Complex.normSq_apply,pow_two] using hz
  rcases hr with hr|hr|hr
  · have hi : z.im=0 := sq_eq_zero_iff.mp (by nlinarith)
    have he : z= -1 := by apply Complex.ext <;> simp [hr,hi]
    rw [he]
    norm_num [pow_succ,Complex.ext_iff,Complex.mul_re,Complex.mul_im]
  · have hi : z.im^2=(1:ℝ)^2 := by nlinarith
    rcases eq_or_eq_neg_of_sq_eq_sq z.im 1 hi with hi|hi
    · have he : z=Complex.I := by apply Complex.ext <;> simp [hr,hi]
      rw [he]
      norm_num [pow_succ,Complex.ext_iff,Complex.mul_re,Complex.mul_im]
    · have he : z= -Complex.I := by apply Complex.ext <;> simp [hr,hi]
      rw [he]
      norm_num [pow_succ,Complex.ext_iff,Complex.mul_re,Complex.mul_im]
  · have hi : z.im=0 := sq_eq_zero_iff.mp (by nlinarith)
    have he : z=1 := by apply Complex.ext <;> simp [hr,hi]
    rw [he]
    norm_num [pow_succ,Complex.ext_iff,Complex.mul_re,Complex.mul_im]

def rowPhase (r : Fin 2 → ℂ) : ℂ := r 1*conj (r 0)

theorem rowPhase_unit (r : Fin 2 → ℂ) (hr : ∀ j,Complex.normSq (r j)=1) :
    Complex.normSq (rowPhase r)=1 := by
  rw [rowPhase,Complex.normSq_mul,Complex.normSq_conj,hr 1,hr 0]
  norm_num

theorem flat_bloch_phase_dot (r s : Fin 2 → ℂ)
    (hr : ∀ j,Complex.normSq (r j)=1) (hs : ∀ j,Complex.normSq (s j)=1) :
    dot3 (blochVector r) (blochVector s)=(rowPhase r*conj (rowPhase s)).re := by
  simp [dot3,blochVector,Fin.sum_univ_succ,hr 0,hr 1,hs 0,hs 1,
    rowPhase,Complex.mul_re,Complex.mul_im]
  ring

theorem flat_row_phase_gram (r s : Fin 2 → ℂ)
    (hr : ∀ j,Complex.normSq (r j)=1) (hs : ∀ j,Complex.normSq (s j)=1) :
    rowInner r s=r 0*conj (s 0)*(1+rowPhase r*conj (rowPhase s)) := by
  calc
    _ = r 0*conj (s 0)+r 1*conj (s 1)*(r 0*conj (r 0))*(s 0*conj (s 0)) := by
      rw [unit_mul_conj (hr 0),unit_mul_conj (hs 0)]
      simp [rowInner]
    _ = _ := by simp only [rowPhase,map_mul,Complex.conj_conj]; ring

theorem flat_rows_quantized_equator {ι : Type*} [Nonempty ι] (R : ι → Fin 2 → ℂ)
    (hflat : ∀ i j,Complex.normSq (R i j)=1)
    (hB : ∀ i j,dot3 (blochVector (R i)) (blochVector (R j))= -1 ∨
      dot3 (blochVector (R i)) (blochVector (R j))=0 ∨
      dot3 (blochVector (R i)) (blochVector (R j))=1) :
    ∃ a d : ι → ℂ,(∀ i,Complex.normSq (a i)=1) ∧ (∀ i,(d i)^4=1) ∧
      ∀ i j,rowInner (R i) (R j)=a i*conj (a j)*(1+d i*conj (d j)) := by
  classical
  let k : ι := Classical.arbitrary ι
  let p (i : ι) := rowPhase (R i)
  let g : ℂ := conj (p k)
  let d (i : ι) := p i*g
  have hp (i : ι) : Complex.normSq (p i)=1 := rowPhase_unit (R i) (hflat i)
  have hg : Complex.normSq g=1 := by simpa only [g,Complex.normSq_conj] using hp k
  have hd (i : ι) : (d i)^4=1 := by
    apply unit_discrete_real_fourth
    · change Complex.normSq (p i*g)=1
      rw [Complex.normSq_mul,hp i,hg]
      norm_num
    · have hh := hB i k
      rw [flat_bloch_phase_dot (R i) (R k) (hflat i) (hflat k)] at hh
      exact hh
  have hrel (i j : ι) : d i*conj (d j)=p i*conj (p j) := by
    calc
      _ = p i*conj (p j)*(g*conj g) := by simp only [d,map_mul]; ring
      _ = _ := by rw [unit_mul_conj hg,mul_one]
  refine ⟨fun i => R i 0,d,fun i => hflat i 0,hd,?_⟩
  intro i j
  rw [hrel]
  exact flat_row_phase_gram (R i) (R j) (hflat i) (hflat j)

end
end CompletionTheory.Bloch
