/- Independent concrete mathematical specification. Apache-2.0, Joshua Mark.
Intentional Challenge proof placeholders are isolated from Solution. -/
module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Basic
@[expose] public section
open scoped BigOperators
namespace CompletionTheory
def cyclicNorm {G : Type*} [Fintype G] [Sub G] (A : Fin 4 → G → ℤ) (k : G) : ℤ :=
  ∑ x, ∑ i, A i x * A i (x - k)

def CyclicNormSolution (m : ℕ) [NeZero m] (t : ℤ) : Prop :=
  ∃ A : Fin 4 → ZMod m → ℤ, (∀ i x, (A i x : ZMod 2) = 1) ∧
    ∀ k, cyclicNorm A k = if k = 0 then 4 * t else 0
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
end CharacterFloor
namespace ThreeSquares
open CharacterFloor
def uniformFamilyArray {m : ℕ} (x : Fin 4 → ℤ) (i : Fin 4) (z : ZMod m) : ℤ :=
  1+2*x i*(if z=0 then 1 else 0)

def UniformFamilySolution (m : ℕ) [NeZero m] (t : ℤ) : Prop :=
  ∃ x : Fin 4 → ℤ,∀ k,cyclicNorm (uniformFamilyArray (m:=m) x) k=
    if k=0 then 4*t else 0

 theorem large_prime_in_progression (a m bound : ℕ) (hm : m≠0) (hcop : a.Coprime m) :
    ∃ q : ℕ,bound<q ∧ q.Prime ∧ Nat.ModEq m q a := by sorry

 theorem residue_data_exists_three_mod_eight_api (n : ℕ) (hn : n%8=3) :
    ∃ d x y : ℤ,0<d ∧ x^2+d=y*(d*(n:ℤ)-1) := by sorry

 theorem three_squares_of_three_mod_eight_api (n : ℕ) (hn : n%8=3) :
    ∃ a b c : ℤ,(n:ℤ)=a^2+b^2+c^2 := by sorry

 theorem four_squares_fixed_sum_api (m t : ℤ) (hm : Odd m) (ht : Odd t)
    (hlarge : m^2+3≤4*t) :
    ∃ x : Fin 4 → ℤ,(∑ i,x i)=-m ∧ (∑ i,(x i)^2)=t := by sorry

 theorem uniform_family_iff_threshold {m : ℕ} [NeZero m] (hm : Odd m) (t : ℤ) (ht : Odd t) :
    UniformFamilySolution m t ↔ (m:ℤ)^2+3≤4*t := by sorry

 theorem uniform_large_energy_existence {m : ℕ} [NeZero m] (hm : Odd m) (t : ℤ)
    (ht : Odd t) (hlarge : (m:ℤ)^2+3≤4*t) :
    UniformFamilySolution m t ∧ CyclicNormSolution m t := by sorry

 theorem small_cyclic_orders_all_odd_energy {m : ℕ} [NeZero m]
    (hm : m=1 ∨ m=3) (t : ℤ) (ht : Odd t) (hT : (m:ℤ)≤t) :
    CyclicNormSolution m t := by sorry

 theorem skew_template_all_odd_energies {m : ℕ} [NeZero m] (q : ℤ)
    (hM : (m:ℤ)=4*q+3) (L : ZMod m → ℤ) (hD : IsCharacterData L (-1))
    (t : ℤ) (ht : Odd t) (hT : q^2+3*q+3≤t) : CharacterTemplateEnergy L t := by sorry

 theorem skew_character_large_energy_region {m : ℕ} [NeZero m] (hm : m%4=3)
    (L : ZMod m → ℤ) (hD : IsCharacterData L (-1)) (t : ℤ) (ht : Odd t)
    (hT : skewThreshold m≤t) : CharacterTemplateEnergy L t ∧ CyclicNormSolution m t := by sorry

 theorem skew_character_threshold_sharp {m : ℕ} [NeZero m] (hm : m%4=3)
    (L : ZMod m → ℤ) (hD : IsCharacterData L (-1)) :
    IsSharpCharacterFloor L (skewThreshold m) := by sorry

 theorem prime_skew_large_energy_region (p : ℕ) [Fact p.Prime] (hp : p%4=3)
    (t : ℤ) (ht : Odd t) (hT : skewThreshold p≤t) : CyclicNormSolution p t := by sorry
end ThreeSquares
end CompletionTheory
