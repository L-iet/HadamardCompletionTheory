/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionQuaternary.GaussianParity
public import Mathlib.Tactic.FieldSimp
@[expose] public section
namespace CompletionTheory.Bloch
noncomputable section
open scoped ComplexConjugate

theorem gaussian_unit_coefficient_phase {z u c : ℂ} (hz : GaussianEven z)
    (hu : Complex.normSq u=1) (hform : z=u*c)
    (hc : c=2 ∨ c=1+Complex.I ∨ c=1-Complex.I) : u^4=1 := by
  rcases hc with rfl|rfl|rfl
  · have hn : Complex.normSq z=4 := by rw [hform,Complex.normSq_mul,hu]; norm_num [Complex.normSq_apply]
    have hp := gaussian_norm_four_phase hz hn
    have hd : z/2=u := by rw [hform]; ring
    rw [hd] at hp
    exact hp
  · have hn : Complex.normSq z=2 := by rw [hform,Complex.normSq_mul,hu]; norm_num [Complex.normSq_apply]
    have hp := (gaussian_norm_two_phase hz hn).1
    have hnz : (1+Complex.I:ℂ)≠0 := by norm_num [Complex.ext_iff]
    have hd : z/(1+Complex.I)=u := by rw [hform]; field_simp
    rw [hd] at hp
    exact hp
  · have hn : Complex.normSq z=2 := by rw [hform,Complex.normSq_mul,hu]; norm_num [Complex.normSq_apply]
    have hp := (gaussian_norm_two_phase hz hn).2
    have hnz : (1-Complex.I:ℂ)≠0 := by norm_num [Complex.ext_iff]
    have hd : z/(1-Complex.I)=u := by rw [hform]; field_simp
    rw [hd] at hp
    exact hp

theorem quaternary_edge_phase {z a b d e : ℂ} (hz : GaussianEven z) (hz0 : z≠0)
    (ha : Complex.normSq a=1) (hb : Complex.normSq b=1) (hd : d^4=1) (he : e^4=1)
    (hform : z=a*conj b*(1+d*conj e)) : (a*conj b)^4=1 := by
  have hu : Complex.normSq (a*conj b)=1 := by
    rw [Complex.normSq_mul,Complex.normSq_conj,ha,hb]
    norm_num
  have hp : (d*conj e)^4=1 := by
    rw [mul_pow,hd,one_mul,←map_pow,he,map_one]
  rcases fourth_root_cases hp with hp|hp|hp|hp
  · apply gaussian_unit_coefficient_phase hz hu hform
    left
    rw [hp]
    norm_num
  · have hz' : z=0 := by rw [hform,hp]; ring
    exact False.elim (hz0 hz')
  · apply gaussian_unit_coefficient_phase hz hu hform
    right;left
    rw [hp]
  · apply gaussian_unit_coefficient_phase hz hu hform
    right;right
    rw [hp]
    ring

end
end CompletionTheory.Bloch
