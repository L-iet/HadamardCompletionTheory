/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCharacter.SkewScalar
public import Mathlib.Tactic.Abel
@[expose] public section
namespace CompletionTheory.CharacterFloor
open scoped BigOperators

def fullCharacterAnsatz {G : Type*} [Zero G] [DecidableEq G] (L : G → ℤ)
    (u v w : Fin 4 → ℤ) (i : Fin 4) (x : G) : ℤ :=
  u i*L x+(if x=0 then v i else 0)+w i

theorem fullChannel_norm {m : ℕ} [NeZero m] (L : ZMod m → ℤ)
    (hL : (∑ x,L x)=0) (u v w : Fin 4 → ℤ) (i : Fin 4) (k : ZMod m) :
    (∑ x,fullCharacterAnsatz L u v w i x*fullCharacterAnsatz L u v w i (x-k))=
      u i^2*(∑ x,L x*L (x-k))+(if k=0 then v i^2 else 0)+
      u i*v i*(L k+L (-k))+2*v i*w i+(m : ℤ)*w i^2 := by
  let e : ZMod m ≃ ZMod m := ⟨fun x => x-k,fun x => x+k,
    by intro x; simp,by intro x; simp⟩
  have hshift : (∑ x,L (x-k))=0 := (Equiv.sum_comp e L).trans hL
  have hpoly (x : ZMod m) :
      fullCharacterAnsatz L u v w i x*fullCharacterAnsatz L u v w i (x-k)=
      u i^2*L x*L (x-k)+
      u i*v i*((if x=k then L x else 0)+(if x=0 then L (x-k) else 0))+
      u i*w i*(L x+L (x-k))+
      (if x=0 then (if k=0 then v i^2 else 0) else 0)+
      v i*w i*((if x=0 then 1 else 0)+(if x=k then 1 else 0))+w i^2 := by
    by_cases hx : x=0
    · subst x
      by_cases hk : k=0
      · subst k; simp [fullCharacterAnsatz]; ring
      · simp [fullCharacterAnsatz,hk,Ne.symm hk,neg_ne_zero.mpr hk]; ring
    · by_cases hxk : x=k
      · subst x; simp [fullCharacterAnsatz,hx]; ring
      · simp [fullCharacterAnsatz,hx,hxk,sub_eq_zero]; ring
  simp_rw [hpoly]
  simp [Finset.sum_add_distrib,← Finset.mul_sum,mul_assoc,hL,hshift]
  ring

theorem fullCharacterAnsatz_norm {m : ℕ} [NeZero m] (L : ZMod m → ℤ)
    (hzero : L 0=0) (hL : (∑ x,L x)=0)
    (hcor : ∀ k,(∑ x,L x*L (x-k))=if k=0 then (m : ℤ)-1 else -1)
    (η : ℤ) (hreflect : ∀ k,L (-k)=η*L k)
    (u v w : Fin 4 → ℤ) (k : ZMod m) :
    cyclicNorm (fullCharacterAnsatz L u v w) k=
      (if k=0 then (m : ℤ)*squareSum u+squareSum v else 0)+
      (-squareSum u+2*scalarDot w v+(m : ℤ)*squareSum w)+
      (1+η)*scalarDot u v*L k := by
  unfold cyclicNorm
  rw [Finset.sum_comm]
  simp_rw [fullChannel_norm L hL u v w,hcor,hreflect]
  by_cases hk : k=0
  · subst k
    simp only [ite_true,hzero,zero_mul,mul_zero,add_zero,scalarDot,squareSum,Fin.sum_univ_four]
    ring
  · simp only [hk,ite_false,scalarDot,squareSum,Fin.sum_univ_four]
    ring

theorem cyclicNorm_independent_shift {G : Type*} [Fintype G] [AddCommGroup G]
    (A : Fin 4 → G → ℤ) (r : Fin 4 → G) (k : G) :
    cyclicNorm (fun i x => A i (x-r i)) k=cyclicNorm A k := by
  unfold cyclicNorm
  rw [Finset.sum_comm,Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ)
    (f:=fun x i => A i x*A i (x-k))]
  apply Finset.sum_congr rfl
  intro i _
  let e : G ≃ G := ⟨fun x => x-r i,fun x => x+r i,
    by intro x; simp,by intro x; simp⟩
  calc
    (∑ x,A i (x-r i)*A i (x-k-r i))=
      ∑ x,A i (x-r i)*A i ((x-r i)-k) := by
      apply Finset.sum_congr rfl
      intro x _
      congr 2
      abel
    _=∑ x,A i x*A i (x-k) := Equiv.sum_comp e (fun x => A i x*A i (x-k))

theorem shifted_odd_iff {G : Type*} [AddCommGroup G]
    (A : Fin 4 → G → ℤ) (r : Fin 4 → G) :
    (∀ i x,(A i (x-r i))%2=1) ↔ ∀ i x,A i x%2=1 := by
  constructor
  · intro h i x
    simpa using h i (x+r i)
  · intro h i x
    exact h i (x-r i)


theorem full_template_parities {m : ℕ} [NeZero m] (L : ZMod m → ℤ)
    (hzero : L 0=0) (a : ZMod m) (ha : L a=1)
    (u v w : Fin 4 → ℤ)
    (hA : ∀ i x,fullCharacterAnsatz L u v w i x%2=1) :
    (∀ i,(u i+w i)%2=1) ∧ (∀ i,(v i+w i)%2=1) := by
  have hane : a≠0 := by intro h; subst a; omega
  constructor
  · intro i
    simpa [fullCharacterAnsatz,ha,hane] using hA i a
  · intro i
    simpa [fullCharacterAnsatz,hzero] using hA i 0

theorem full_template_scalarity {m : ℕ} [NeZero m] (L : ZMod m → ℤ)
    (hzero : L 0=0) (hL : (∑ x,L x)=0)
    (hcor : ∀ k,(∑ x,L x*L (x-k))=if k=0 then (m : ℤ)-1 else -1)
    (η : ℤ) (hreflect : ∀ k,L (-k)=η*L k)
    (a b : ZMod m) (ha : L a=1) (hb : L b= -1)
    (u v w : Fin 4 → ℤ) (t : ℤ)
    (hn : ∀ k,cyclicNorm (fullCharacterAnsatz L u v w) k=if k=0 then 4*t else 0) :
    2*scalarDot w v=squareSum u-(m : ℤ)*squareSum w ∧
    4*t=(m : ℤ)*squareSum u+squareSum v ∧ (1+η)*scalarDot u v=0 := by
  have hane : a≠0 := by intro h; subst a; omega
  have hbne : b≠0 := by intro h; subst b; omega
  have hp := hn a
  have hm := hn b
  have hz := hn 0
  rw [fullCharacterAnsatz_norm L hzero hL hcor η hreflect u v w] at hp hm hz
  simp only [hane,hbne,ite_false,ha,hb,mul_one,mul_neg_one,zero_add] at hp hm
  simp only [ite_true,hzero,mul_zero,add_zero] at hz
  constructor
  · linarith
  constructor <;> linarith

theorem cyclicNorm_odd_energy {m : ℕ} [NeZero m] (hm : m%2=1)
    (A : Fin 4 → ZMod m → ℤ) (hA : ∀ i x,A i x%2=1)
    (t : ℤ) (ht : cyclicNorm A 0=4*t) : t%2=1 := by
  have hsquare : ∀ i x,(A i x : ZMod 8)^2=1 := by
    intro i x
    have htwo : (A i x : ZMod 2)=1 :=
      (ZMod.intCast_eq_intCast_iff' (A i x) 1 2).mpr (by simpa using hA i x)
    have hh := odd_coefficient_square_mod_eight htwo
    have hc := (ZMod.intCast_eq_intCast_iff' (A i x^2) 1 8).mpr (by simpa using hh)
    simpa using hc
  have hsum : (cyclicNorm A 0 : ZMod 8)=4*(m : ZMod 8) := by
    simp only [cyclicNorm,sub_zero,Int.cast_sum,Int.cast_mul]
    simp_rw [← pow_two,hsquare]
    simp [mul_comm]
  rw [ht] at hsum
  have hmod : (4*t)%8=(4*(m : ℤ))%8 :=
    (ZMod.intCast_eq_intCast_iff' (4*t) (4*(m : ℤ)) 8).mp (by simpa using hsum)
  have hm4 : (4*(m : ℤ))%8=4 := by omega
  rw [hm4] at hmod
  omega


theorem character_augmentation_zero {m : ℕ} [NeZero m] (L : ZMod m → ℤ)
    (hcor : ∀ k,(∑ x,L x*L (x-k))=if k=0 then (m : ℤ)-1 else -1) :
    (∑ x,L x)=0 := by
  have hshift (x : ZMod m) : (∑ k,L (x-k))=∑ y,L y := by
    let e : ZMod m ≃ ZMod m := ⟨fun k => x-k,fun k => x-k,
      by intro k; simp,by intro k; simp⟩
    exact Equiv.sum_comp e L
  have he : (∑ k,∑ x,L x*L (x-k))=(∑ x,L x)^2 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum,hshift]
    rw [← Finset.sum_mul,pow_two]
  have hc : ∀ k,(∑ x,L x*L (x-k))=(if k=0 then (m : ℤ) else 0)-1 := by
    intro k
    rw [hcor]
    by_cases hk : k=0 <;> simp [hk]
  simp_rw [hc] at he
  have hz : (∑ x,L x)^2=0 := by
    symm
    simpa [Finset.sum_sub_distrib] using he
  nlinarith

theorem character_both_signs {m : ℕ} [NeZero m] (hm : 1<m) (L : ZMod m → ℤ)
    (hzero : L 0=0) (hL : (∑ x,L x)=0)
    (hs : ∀ x,x≠0 → L x=1 ∨ L x= -1)
    (hcor : ∀ k,(∑ x,L x*L (x-k))=if k=0 then (m : ℤ)-1 else -1) :
    (∃ a,L a=1) ∧ (∃ b,L b= -1) := by
  have henergy : (∑ x,L x^2)=(m : ℤ)-1 := by
    simpa [pow_two] using hcor 0
  have hex : ∃ a,L a≠0 := by
    by_contra! h
    simp [h] at henergy
    omega
  obtain ⟨a,ha⟩ := hex
  constructor
  · by_contra! hn
    have hnonpos : ∀ x,L x≤0 := by
      intro x
      by_cases hx : x=0
      · simp [hx,hzero]
      · rcases hs x hx with h|h
        · exact False.elim (hn x h)
        · omega
    have hneg : (∑ x,-L x)=0 := by rw [Finset.sum_neg_distrib,hL,neg_zero]
    have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => neg_nonneg.mpr (hnonpos x))).mp hneg a (Finset.mem_univ _)
    exact ha (by omega)
  · by_contra! hn
    have hnonneg : ∀ x,0≤L x := by
      intro x
      by_cases hx : x=0
      · simp [hx,hzero]
      · rcases hs x hx with h|h
        · omega
        · exact False.elim (hn x h)
    have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hnonneg x)).mp hL a (Finset.mem_univ _)
    exact ha hh

end CompletionTheory.CharacterFloor
