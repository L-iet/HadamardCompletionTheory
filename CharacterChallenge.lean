/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Fin
@[expose] public section
namespace CompletionTheory
open scoped BigOperators

def cyclicNorm {G : Type*} [Fintype G] [Sub G] (A : Fin 4 → G → ℤ) (k : G) : ℤ :=
  ∑ x, ∑ i, A i x * A i (x - k)
namespace CharacterFloor
def fullCharacterAnsatz {G : Type*} [Zero G] [DecidableEq G] (L : G → ℤ)
    (u v w : Fin 4 → ℤ) (i : Fin 4) (x : G) : ℤ :=
  u i*L x+(if x=0 then v i else 0)+w i

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

theorem skew_template_attainment {m : ℕ} [NeZero m] (q : ℤ)
    (hM : (m : ℤ)=4*q+3) (L : ZMod m → ℤ) (hD : IsCharacterData L (-1)) :
    CharacterTemplateEnergy L (q^2+3*q+3) := by
  sorry

theorem symmetric_template_attainment {m : ℕ} [NeZero m] (q : ℤ)
    (hM : (m : ℤ)=4*q+1) (L : ZMod m → ℤ) (hD : IsCharacterData L 1) :
    CharacterTemplateEnergy L (2*q^2+2*q+1) := by
  sorry

theorem character_span_sharp_energy_floors {m : ℕ} [NeZero m] (hm : 1<m) (hmod : m%2=1)
    (L : ZMod m → ℤ) :
    (m%4=3 → IsCharacterData L (-1) → IsSharpCharacterFloor L (skewThreshold m)) ∧
    (m%4=1 → 5≤m → IsCharacterData L 1 → IsSharpCharacterFloor L (symmetricThreshold m)) := by
  sorry

def PrimeCharacterEnergy (p : ℕ) [Fact p.Prime] (t : ℤ) : Prop :=
  CharacterTemplateEnergy (quadraticChar (ZMod p)) t

theorem prime_character_binary_boundary (p : ℕ) [Fact p.Prime] (hodd : p%2=1) :
    PrimeCharacterEnergy p (p : ℤ) ↔ p=3 ∨ p=5 ∨ p=7 := by
  sorry

end CharacterFloor
end CompletionTheory
