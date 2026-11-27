/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionQuaternary.GaussianParity
@[expose] public section
namespace CompletionTheory.Bloch
noncomputable section
open scoped BigOperators ComplexConjugate

def GaussianRealParity (z : ℂ) (e : ℤ) : Prop :=
  ∃ a b : ℤ,z=(a:ℂ)+(b:ℂ)*Complex.I ∧ Even (a-e)

theorem gaussianRealParity_add {z w : ℂ} {e f : ℤ}
    (hz : GaussianRealParity z e) (hw : GaussianRealParity w f) : GaussianRealParity (z+w) (e+f) := by
  obtain ⟨a,b,rfl,t,ht⟩ := hz
  obtain ⟨c,d,rfl,u,hu⟩ := hw
  refine ⟨a+c,b+d,?_,t+u,by omega⟩
  push_cast
  ring

theorem gaussianRealParity_neg {z : ℂ} {e : ℤ}
    (hz : GaussianRealParity z e) : GaussianRealParity (-z) (-e) := by
  obtain ⟨a,b,rfl,t,ht⟩ := hz
  refine ⟨-a,-b,?_, -t,by omega⟩
  push_cast
  ring

theorem gaussianRealParity_zero_of_even {z : ℂ} {e : ℤ}
    (hz : GaussianRealParity z e) (he : Even e) : GaussianRealParity z 0 := by
  obtain ⟨a,b,hz,t,ht⟩ := hz
  obtain ⟨u,hu⟩ := he
  exact ⟨a,b,hz,t+u,by omega⟩

theorem gaussianRealParity_unique {z : ℂ} {e f : ℤ}
    (he : GaussianRealParity z e) (hf : GaussianRealParity z f) : Even (e-f) := by
  obtain ⟨a,b,hz,t,ht⟩ := he
  obtain ⟨c,d,hz',u,hu⟩ := hf
  have hh := congrArg Complex.re (hz.symm.trans hz')
  have hhR : (a:ℝ)=(c:ℝ) := by simpa using hh
  have hac : a=c := by exact_mod_cast hhR
  exact ⟨u-t,by omega⟩

theorem gaussianRealParity_sum {ι : Type*} [DecidableEq ι] (S : Finset ι) (z : ι → ℂ)
    (hz : ∀ i∈S,GaussianRealParity (z i) 1) : GaussianRealParity (∑ i∈S,z i) (S.card:ℤ) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0,0,by simp,0,by simp⟩
  | @insert a S ha ih =>
    have hh := gaussianRealParity_add (hz a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hz i (Finset.mem_insert_of_mem hi)))
    simpa [Finset.sum_insert,ha,Finset.card_insert_of_notMem ha,add_comm] using hh

theorem gaussian_odd_triple_real {z0 z1 z2 : ℂ}
    (h0 : GaussianParity z0 1) (h1 : GaussianParity z1 1) (h2 : GaussianParity z2 1) :
    GaussianRealParity (z0*conj z1+z1*conj z2+z2*conj z0) 1 := by
  obtain ⟨a0,b0,rfl,t0,ht0⟩ := h0
  obtain ⟨a1,b1,rfl,t1,ht1⟩ := h1
  obtain ⟨a2,b2,rfl,t2,ht2⟩ := h2
  refine ⟨a0*a1+b0*b1+a1*a2+b1*b2+a2*a0+b2*b0,
    b0*a1-a0*b1+b1*a2-a1*b2+b2*a0-a2*b0,?_,
    1-(a0+a1+a2)+(a0*a1+a1*a2+a2*a0)+t0*(2-a1-a2)+t1*(2-a0-a2)+t2*(2-a0-a1)+
      2*(t0*t1+t1*t2+t2*t0),?_⟩
  · apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> ring
  · have hb0 : b0=1+(t0+t0)-a0 := by omega
    have hb1 : b1=1+(t1+t1)-a1 := by omega
    have hb2 : b2=1+(t2+t2)-a2 := by omega
    rw [hb0,hb1,hb2]
    ring

theorem gaussian_norm_two_real_odd {z : ℂ} (hz : GaussianEven z)
    (hn : Complex.normSq z=2) : GaussianRealParity z 1 := by
  obtain ⟨a,b,rfl,hparity⟩ := hz
  have habR : (a:ℝ)^2+(b:ℝ)^2=2 := by simpa [Complex.normSq_apply,pow_two] using hn
  have hab : a^2+b^2=2 := by exact_mod_cast habR
  have ha : -2≤a ∧ a≤2 := by constructor <;> nlinarith [sq_nonneg (a-2),sq_nonneg (a+2),sq_nonneg b]
  have hb : -2≤b ∧ b≤2 := by constructor <;> nlinarith [sq_nonneg (b-2),sq_nonneg (b+2),sq_nonneg a]
  refine ⟨a,b,rfl,?_⟩
  obtain ⟨ha0,ha1⟩ := ha
  obtain ⟨hb0,hb1⟩ := hb
  interval_cases a <;> interval_cases b <;> norm_num [Complex.normSq_apply] at *

end
end CompletionTheory.Bloch
