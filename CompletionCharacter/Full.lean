/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCharacter.Template
public import CompletionCharacter.SymmetricScalar
@[expose] public section
namespace CompletionTheory.CharacterFloor
open scoped BigOperators

def IsCharacterData {m : ℕ} [NeZero m] (L : ZMod m → ℤ) (η : ℤ) : Prop :=
  L 0=0 ∧ (∀ x,x≠0 → L x=1 ∨ L x= -1) ∧
  (∀ k,(∑ x,L x*L (x-k))=if k=0 then (m : ℤ)-1 else -1) ∧
  (∀ k,L (-k)=η*L k)

def CharacterTemplateEnergy {m : ℕ} [NeZero m] (L : ZMod m → ℤ) (t : ℤ) : Prop :=
  ∃ u v w : Fin 4 → ℤ,∃ r : Fin 4 → ZMod m,
    (∀ i x,fullCharacterAnsatz L u v w i (x-r i)%2=1) ∧
    (∀ k,cyclicNorm (fun i x => fullCharacterAnsatz L u v w i (x-r i)) k=
      if k=0 then 4*t else 0)

def IsSharpCharacterFloor {m : ℕ} [NeZero m] (L : ZMod m → ℤ) (T : ℤ) : Prop :=
  CharacterTemplateEnergy L T ∧ (∀ t,CharacterTemplateEnergy L t → T≤t) ∧ T%2=1

def skewThreshold (m : ℕ) : ℤ := ((m : ℤ)^2+6*m+21)/16

def symmetricThreshold (m : ℕ) : ℤ := ((m : ℤ)^2+2*m+5)/8

theorem energy_parameters {m : ℕ} [NeZero m] (hm : 1<m) (hmod : m%2=1)
    (L : ZMod m → ℤ) (η : ℤ) (hD : IsCharacterData L η)
    (t : ℤ) (hE : CharacterTemplateEnergy L t) :
    ∃ u v w : Fin 4 → ℤ,(∀ i,(u i+w i)%2=1) ∧ (∀ i,(v i+w i)%2=1) ∧
      2*scalarDot w v=squareSum u-(m : ℤ)*squareSum w ∧
      4*t=(m : ℤ)*squareSum u+squareSum v ∧ t%2=1 ∧ (1+η)*scalarDot u v=0 := by
  obtain ⟨hzero,hs,hcor,hreflect⟩ := hD
  obtain ⟨u,v,w,r,hA,hn⟩ := hE
  have hL := character_augmentation_zero L hcor
  obtain ⟨⟨a,ha⟩,⟨b,hb⟩⟩ := character_both_signs hm L hzero hL hs hcor
  have hAbase := (shifted_odd_iff (fullCharacterAnsatz L u v w) r).mp hA
  have hnbase : ∀ k,cyclicNorm (fullCharacterAnsatz L u v w) k=if k=0 then 4*t else 0 := by
    intro k
    exact (cyclicNorm_independent_shift (fullCharacterAnsatz L u v w) r k).symm.trans (hn k)
  have hp := full_template_parities L hzero a ha u v w hAbase
  have hc := full_template_scalarity L hzero hL hcor η hreflect a b ha hb u v w t hnbase
  have ho := cyclicNorm_odd_energy hmod (fullCharacterAnsatz L u v w) hAbase t (by simpa using hnbase 0)
  exact ⟨u,v,w,hp.1,hp.2,hc.1,hc.2.1,ho,hc.2.2⟩

theorem full_template_odd_of_parities {m : ℕ} [NeZero m] (L : ZMod m → ℤ)
    (hzero : L 0=0) (hs : ∀ x,x≠0 → L x=1 ∨ L x= -1)
    (u v w : Fin 4 → ℤ) (hu : ∀ i,(u i+w i)%2=1) (hv : ∀ i,(v i+w i)%2=1) :
    ∀ i x,fullCharacterAnsatz L u v w i x%2=1 := by
  intro i x
  by_cases hx : x=0
  · simpa [fullCharacterAnsatz,hx,hzero] using hv i
  · rcases hs x hx with h|h
    · simpa [fullCharacterAnsatz,hx,h] using hu i
    · have hp : (-u i+w i)%2=1 := by have := hu i; omega
      simpa [fullCharacterAnsatz,hx,h] using hp

theorem skew_template_attainment {m : ℕ} [NeZero m] (q : ℤ)
    (hM : (m : ℤ)=4*q+3) (L : ZMod m → ℤ) (hD : IsCharacterData L (-1)) :
    CharacterTemplateEnergy L (q^2+3*q+3) := by
  obtain ⟨hzero,hs,hcor,hreflect⟩ := hD
  have hL := character_augmentation_zero L hcor
  let u : Fin 4 → ℤ := ![1,1,1,0]
  let v : Fin 4 → ℤ := ![1,1,1,-2*q]
  let w : Fin 4 → ℤ := ![0,0,0,1]
  refine ⟨u,v,w,fun _ => 0,?_,?_⟩
  · simp only [sub_zero]
    apply full_template_odd_of_parities L hzero hs u v w
    · intro i; fin_cases i <;> simp [u,v,w] <;> omega
    · intro i; fin_cases i <;> simp [u,v,w] <;> omega
  · intro z
    simp only [sub_zero]
    rw [fullCharacterAnsatz_norm L hzero hL hcor (-1) hreflect u v w]
    by_cases hz : z=0 <;> simp [hz,squareSum,scalarDot,Fin.sum_univ_four,u,v,w,hM] <;> ring

theorem symmetric_template_attainment {m : ℕ} [NeZero m] (q : ℤ)
    (hM : (m : ℤ)=4*q+1) (L : ZMod m → ℤ) (hD : IsCharacterData L 1) :
    CharacterTemplateEnergy L (2*q^2+2*q+1) := by
  obtain ⟨hzero,hs,hcor,hreflect⟩ := hD
  have hL := character_augmentation_zero L hcor
  let u : Fin 4 → ℤ := ![1,1,0,0]
  let v : Fin 4 → ℤ := ![1,-1,-2*q,-2*q]
  let w : Fin 4 → ℤ := ![0,0,1,1]
  refine ⟨u,v,w,fun _ => 0,?_,?_⟩
  · simp only [sub_zero]
    apply full_template_odd_of_parities L hzero hs u v w
    · intro i; fin_cases i <;> simp [u,v,w] <;> omega
    · intro i; fin_cases i <;> simp [u,v,w] <;> omega
  · intro z
    simp only [sub_zero]
    rw [fullCharacterAnsatz_norm L hzero hL hcor 1 hreflect u v w]
    by_cases hz : z=0 <;> simp [hz,squareSum,scalarDot,Fin.sum_univ_four,u,v,w,hM] <;> ring

theorem skew_template_lower {m : ℕ} [NeZero m] (hm : 1<m) (hmod : m%2=1)
    (q : ℤ) (hq : 0≤q) (hM : (m : ℤ)=4*q+3)
    (L : ZMod m → ℤ) (hD : IsCharacterData L (-1))
    (t : ℤ) (hE : CharacterTemplateEnergy L t) : q^2+3*q+3≤t := by
  obtain ⟨u,v,w,hu,hv,he,ht,ho,_⟩ := energy_parameters hm hmod L (-1) hD t hE
  rw [hM] at he ht
  exact skew_scalar_floor q t hq u v w hu hv he ht ho

theorem symmetric_template_lower {m : ℕ} [NeZero m] (hm : 1<m) (hmod : m%2=1)
    (q : ℤ) (hq : 1≤q) (hM : (m : ℤ)=4*q+1)
    (L : ZMod m → ℤ) (hD : IsCharacterData L 1)
    (t : ℤ) (hE : CharacterTemplateEnergy L t) : 2*q^2+2*q+1≤t := by
  obtain ⟨u,v,w,hu,hv,he,ht,ho,hc⟩ := energy_parameters hm hmod L 1 hD t hE
  have huv : scalarDot u v=0 := by linarith
  rw [hM] at he ht
  exact symmetric_scalar_floor q t hq u v w hu hv huv he ht ho

theorem character_span_sharp_energy_floors {m : ℕ} [NeZero m] (hm : 1<m) (hmod : m%2=1)
    (L : ZMod m → ℤ) :
    (m%4=3 → IsCharacterData L (-1) → IsSharpCharacterFloor L (skewThreshold m)) ∧
    (m%4=1 → 5≤m → IsCharacterData L 1 → IsSharpCharacterFloor L (symmetricThreshold m)) := by
  constructor
  · intro hm3 hD
    let q : ℤ := (m/4 : ℕ)
    have hq : 0≤q := by dsimp [q]; omega
    have hMnat : m=4*(m/4)+3 := by have := Nat.mod_add_div m 4; omega
    have hM : (m : ℤ)=4*q+3 := by dsimp [q]; exact_mod_cast hMnat
    have hT : skewThreshold m=q^2+3*q+3 := by
      unfold skewThreshold
      have he : (m : ℤ)^2+6*m+21=16*(q^2+3*q+3) := by rw [hM]; ring
      rw [he]
      omega
    refine ⟨?_,?_,?_⟩
    · rw [hT]
      exact skew_template_attainment q hM L hD
    · intro t ht
      rw [hT]
      exact skew_template_lower hm hmod q hq hM L hD t ht
    · rw [hT]
      exact odd_skew_threshold q
  · intro hm1 hm5 hD
    let q : ℤ := (m/4 : ℕ)
    have hMnat : m=4*(m/4)+1 := by have := Nat.mod_add_div m 4; omega
    have hq : 1≤q := by dsimp [q]; omega
    have hM : (m : ℤ)=4*q+1 := by dsimp [q]; exact_mod_cast hMnat
    have hT : symmetricThreshold m=2*q^2+2*q+1 := by
      unfold symmetricThreshold
      have he : (m : ℤ)^2+2*m+5=8*(2*q^2+2*q+1) := by rw [hM]; ring
      rw [he]
      omega
    refine ⟨?_,?_,?_⟩
    · rw [hT]
      exact symmetric_template_attainment q hM L hD
    · intro t ht
      rw [hT]
      exact symmetric_template_lower hm hmod q hq hM L hD t ht
    · rw [hT]
      exact odd_symmetric_threshold q

end CompletionTheory.CharacterFloor
