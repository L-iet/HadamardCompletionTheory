/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionQuaternary.QuaternaryScalar
@[expose] public section
namespace CompletionTheory.Bloch
noncomputable section
open scoped BigOperators ComplexConjugate

def GaussianParity (z : ℂ) (e : ℤ) : Prop :=
  ∃ a b : ℤ,z=(a:ℂ)+(b:ℂ)*Complex.I ∧ Even (a+b-e)

theorem gaussianParity_add {z w : ℂ} {e f : ℤ}
    (hz : GaussianParity z e) (hw : GaussianParity w f) : GaussianParity (z+w) (e+f) := by
  obtain ⟨a,b,rfl,t,ht⟩ := hz
  obtain ⟨c,d,rfl,u,hu⟩ := hw
  refine ⟨a+c,b+d,?_,t+u,by omega⟩
  push_cast
  ring

theorem gaussianParity_neg {z : ℂ} {e : ℤ} (hz : GaussianParity z e) : GaussianParity (-z) (-e) := by
  obtain ⟨a,b,rfl,t,ht⟩ := hz
  refine ⟨-a,-b,?_, -t,by omega⟩
  push_cast
  ring

theorem gaussianParity_conj {z : ℂ} {e : ℤ} (hz : GaussianParity z e) : GaussianParity (conj z) e := by
  obtain ⟨a,b,rfl,t,ht⟩ := hz
  refine ⟨a,-b,?_,t-b,by omega⟩
  simp

theorem gaussianParity_mul {z w : ℂ} {e f : ℤ}
    (hz : GaussianParity z e) (hw : GaussianParity w f) : GaussianParity (z*w) (e*f) := by
  obtain ⟨a,b,rfl,t,ht⟩ := hz
  obtain ⟨c,d,rfl,u,hu⟩ := hw
  refine ⟨a*c-b*d,a*d+b*c,?_,e*u+f*t+2*t*u-b*d,?_⟩
  · apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> ring
  · have ha : a=e+(t+t)-b := by omega
    have hc : c=f+(u+u)-d := by omega
    rw [ha,hc]
    ring

theorem gaussianEven_of_parity_even {z : ℂ} {e : ℤ}
    (hz : GaussianParity z e) (he : Even e) : GaussianEven z := by
  obtain ⟨a,b,hz,t,ht⟩ := hz
  obtain ⟨u,hu⟩ := he
  exact ⟨a,b,hz,t+u,by omega⟩

theorem gaussianParity_sum {ι : Type*} [DecidableEq ι] (S : Finset ι) (z : ι → ℂ)
    (hz : ∀ i∈S,GaussianParity (z i) 1) : GaussianParity (∑ i∈S,z i) (S.card:ℤ) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0,0,by simp,0,by simp⟩
  | @insert a S ha ih =>
    have hza := hz a (Finset.mem_insert_self _ _)
    have hzs := ih (fun i hi => hz i (Finset.mem_insert_of_mem hi))
    have hh := gaussianParity_add hza hzs
    simpa [Finset.sum_insert,ha,Finset.card_insert_of_notMem ha,add_comm] using hh

theorem fourth_root_cases {z : ℂ} (hz : z^4=1) :
    z=1 ∨ z= -1 ∨ z=Complex.I ∨ z= -Complex.I := by
  have hh : (z^2)^2=(1:ℂ)^2 := by calc
    _ = z^4 := by ring
    _ = _ := by simpa using hz
  rcases eq_or_eq_neg_of_sq_eq_sq (z^2) 1 hh with hp|hn
  · rcases eq_or_eq_neg_of_sq_eq_sq z 1 (by simpa using hp) with h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases eq_or_eq_neg_of_sq_eq_sq z Complex.I (by simpa only [Complex.I_sq] using hn) with h|h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

theorem fourth_root_gaussianParity {z : ℂ} (hz : z^4=1) : GaussianParity z 1 := by
  rcases fourth_root_cases hz with rfl|rfl|rfl|rfl
  · exact ⟨1,0,by norm_num,0,by norm_num⟩
  · exact ⟨-1,0,by norm_num,-1,by norm_num⟩
  · exact ⟨0,1,by norm_num,0,by norm_num⟩
  · exact ⟨0,-1,by norm_num,-1,by norm_num⟩

end
end CompletionTheory.Bloch
