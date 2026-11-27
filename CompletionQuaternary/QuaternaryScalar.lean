/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionBloch.BlochAlgebra
public import Mathlib.Tactic.IntervalCases
@[expose] public section
namespace CompletionTheory.Bloch
noncomputable section

def GaussianEven (z : ℂ) : Prop := ∃ a b : ℤ,z=(a:ℂ)+(b:ℂ)*Complex.I ∧ Even (a+b)

theorem gaussian_even_norm_classification {z : ℂ} (hz : GaussianEven z)
    (hn : Complex.normSq z≤4) : Complex.normSq z=0 ∨ Complex.normSq z=2 ∨ Complex.normSq z=4 := by
  obtain ⟨a,b,rfl,hparity⟩ := hz
  have habR : (a:ℝ)^2+(b:ℝ)^2≤4 := by simpa [Complex.normSq_apply,pow_two] using hn
  have hab : a^2+b^2≤4 := by exact_mod_cast habR
  have ha : -2≤a ∧ a≤2 := by constructor <;> nlinarith [sq_nonneg (a-2),sq_nonneg (a+2),sq_nonneg b]
  have hb : -2≤b ∧ b≤2 := by constructor <;> nlinarith [sq_nonneg (b-2),sq_nonneg (b+2),sq_nonneg a]
  obtain ⟨ha0,ha1⟩ := ha
  obtain ⟨hb0,hb1⟩ := hb
  interval_cases a <;> interval_cases b <;> norm_num [Complex.normSq_apply] at *

theorem gaussian_norm_four_phase {z : ℂ} (hz : GaussianEven z)
    (hn : Complex.normSq z=4) : (z/2)^4=1 := by
  obtain ⟨a,b,rfl,hparity⟩ := hz
  have habR : (a:ℝ)^2+(b:ℝ)^2=4 := by simpa [Complex.normSq_apply,pow_two] using hn
  have hab : a^2+b^2=4 := by exact_mod_cast habR
  have ha : -2≤a ∧ a≤2 := by constructor <;> nlinarith [sq_nonneg (a-2),sq_nonneg (a+2),sq_nonneg b]
  have hb : -2≤b ∧ b≤2 := by constructor <;> nlinarith [sq_nonneg (b-2),sq_nonneg (b+2),sq_nonneg a]
  obtain ⟨ha0,ha1⟩ := ha
  obtain ⟨hb0,hb1⟩ := hb
  interval_cases a <;> interval_cases b <;> norm_num [Complex.normSq_apply,Complex.ext_iff,pow_succ,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im] at *

theorem gaussian_norm_two_phase {z : ℂ} (hz : GaussianEven z)
    (hn : Complex.normSq z=2) : (z/(1+Complex.I))^4=1 ∧ (z/(1-Complex.I))^4=1 := by
  obtain ⟨a,b,rfl,hparity⟩ := hz
  have habR : (a:ℝ)^2+(b:ℝ)^2=2 := by simpa [Complex.normSq_apply,pow_two] using hn
  have hab : a^2+b^2=2 := by exact_mod_cast habR
  have ha : -2≤a ∧ a≤2 := by constructor <;> nlinarith [sq_nonneg (a-2),sq_nonneg (a+2),sq_nonneg b]
  have hb : -2≤b ∧ b≤2 := by constructor <;> nlinarith [sq_nonneg (b-2),sq_nonneg (b+2),sq_nonneg a]
  obtain ⟨ha0,ha1⟩ := ha
  obtain ⟨hb0,hb1⟩ := hb
  interval_cases a <;> interval_cases b <;>
    norm_num [Complex.normSq_apply,Complex.ext_iff,pow_succ,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im] at *

end
end CompletionTheory.Bloch
