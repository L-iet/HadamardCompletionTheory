/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0.
The elementary Mobius correlation proof and reflection lemmas are adapted
from this author's Apache-2.0 EntropyDesigns/Paley.lean and PaleySecond.lean.
This standalone specialization imports no sibling project. -/
module
public import CompletionCharacter.Full
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
@[expose] public section
namespace CompletionTheory.CharacterFloor
open scoped BigOperators
set_option maxHeartbeats 1000000
theorem mobius_forward_ne_one {F : Type*} [Field F] {a b x : F} (hab : a≠b) (hxb : x≠b) :
    (x-a)/(x-b) ≠ 1 := by
  intro h
  have hh := (div_eq_iff (sub_ne_zero.mpr hxb)).mp h
  apply hab
  linear_combination -hh

theorem mobius_backward_ne_base {F : Type*} [Field F] {a b y : F} (hab : a≠b) (hy : y≠1) :
    (b*y-a)/(y-1) ≠ b := by
  intro h
  have hh := (div_eq_iff (sub_ne_zero.mpr hy)).mp h
  apply hab
  linear_combination -hh

def completedMobius {F : Type*} [Field F] [DecidableEq F] (a b : F) (hab : a≠b) : F ≃ F where
  toFun x := if x=b then 1 else (x-a)/(x-b)
  invFun y := if y=1 then b else (b*y-a)/(y-1)
  left_inv x := by
    by_cases hx : x=b
    · simp [hx]
    · have hy := mobius_forward_ne_one hab hx
      simp only [if_neg hx,if_neg hy]
      apply (div_eq_iff (sub_ne_zero.mpr hy)).mpr
      field_simp [sub_ne_zero.mpr hx] <;> ring
  right_inv y := by
    by_cases hy : y=1
    · simp [hy]
    · have hx := mobius_backward_ne_base hab hy
      simp only [if_neg hy,if_neg hx]
      apply (div_eq_iff (sub_ne_zero.mpr hx)).mpr
      field_simp [sub_ne_zero.mpr hy] <;> ring

theorem quadratic_char_ratio {F : Type*} [Field F] [Fintype F] [DecidableEq F] (u v : F) (hv : v≠0) :
    quadraticChar F u*quadraticChar F v=quadraticChar F (u/v) := by
  have hh : quadraticChar F (u/v)*quadraticChar F v=quadraticChar F u := by
    rw [← map_mul,div_mul_cancel₀ u hv]
  calc
    _ = (quadraticChar F (u/v)*quadraticChar F v)*quadraticChar F v := by rw [hh]
    _ = quadraticChar F (u/v)*(quadraticChar F v)^2 := by ring
    _ = _ := by rw [quadraticChar_sq_one hv,mul_one]

theorem quadratic_char_correlation {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hchar : ringChar F≠2) (a b : F) (hab : a≠b) :
    (∑ x : F,quadraticChar F (x-a)*quadraticChar F (x-b))= -1 := by
  let e := completedMobius a b hab
  have ht (x : F) : quadraticChar F (x-a)*quadraticChar F (x-b)=
      quadraticChar F (e x)-(if x=b then (1 : ℤ) else 0) := by
    by_cases hx : x=b
    · subst x
      simp [e,completedMobius,quadraticChar_zero]
    · simp only [e,completedMobius,Equiv.coe_fn_mk,if_neg hx,sub_zero]
      exact quadratic_char_ratio _ _ (sub_ne_zero.mpr hx)
  simp_rw [ht]
  rw [Finset.sum_sub_distrib,Equiv.sum_comp e (quadraticChar F),quadraticChar_sum_zero hchar]
  simp

theorem paley_character_neg {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hres : Fintype.card F%4=3) (x : F) : quadraticChar F (-x)= -quadraticChar F x := by
  have hs : ¬IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff]
    exact not_ne_iff.mpr hres
  have hn : quadraticChar F (-1)= -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hs
  calc
    _ = quadraticChar F ((-1)*x) := by rw [neg_one_mul]
    _ = quadraticChar F (-1)*quadraticChar F x := map_mul _ _ _
    _ = _ := by rw [hn,neg_one_mul]

theorem square_character_neg {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hres : Fintype.card F%4=1) (x : F) : quadraticChar F (-x)=quadraticChar F x := by
  have hs : IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff]
    omega
  have hn : quadraticChar F (-1)=1 := (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr one_ne_zero)).mpr hs
  rw [show -x=(-1)*x by ring, map_mul, hn, one_mul]


theorem prime_character_data {p : ℕ} [Fact p.Prime] (hodd : p%2=1) :
    (p%4=3 → IsCharacterData (quadraticChar (ZMod p)) (-1)) ∧
    (p%4=1 → IsCharacterData (quadraticChar (ZMod p)) 1) := by
  have hc : ringChar (ZMod p)≠2 := by
    intro h
    have he := FiniteField.even_card_of_char_two h
    simp only [ZMod.card] at he
    omega
  have hcor (k : ZMod p) :
      (∑ x,quadraticChar (ZMod p) x*quadraticChar (ZMod p) (x-k))=
        if k=0 then (p : ℤ)-1 else -1 := by
    by_cases hk : k=0
    · subst k
      have ht (x : ZMod p) : quadraticChar (ZMod p) x*quadraticChar (ZMod p) x=
          1-(if x=0 then (1 : ℤ) else 0) := by
        by_cases hx : x=0
        · simp [hx,quadraticChar_zero]
        · simpa [pow_two,hx] using quadraticChar_sq_one hx
      simp_rw [sub_zero,ht]
      simp [Finset.sum_sub_distrib]
    · have hh := quadratic_char_correlation hc (0 : ZMod p) k (Ne.symm hk)
      simpa [hk] using hh
  constructor
  · intro hp
    refine ⟨quadraticChar_zero,?_,hcor,?_⟩
    · intro x hx
      exact (sq_eq_one_iff).mp (quadraticChar_sq_one hx)
    · intro k
      simpa using paley_character_neg (F:=ZMod p) (by simpa using hp) k
  · intro hp
    refine ⟨quadraticChar_zero,?_,hcor,?_⟩
    · intro x hx
      exact (sq_eq_one_iff).mp (quadraticChar_sq_one hx)
    · intro k
      simpa using square_character_neg (F:=ZMod p) (by simpa using hp) k

def PrimeCharacterEnergy (p : ℕ) [Fact p.Prime] (t : ℤ) : Prop :=
  CharacterTemplateEnergy (quadraticChar (ZMod p)) t

theorem prime_character_binary_boundary (p : ℕ) [Fact p.Prime] (hodd : p%2=1) :
    PrimeCharacterEnergy p (p : ℤ) ↔ p=3 ∨ p=5 ∨ p=7 := by
  have hp : p.Prime := Fact.out
  have hlarge : 1<p := hp.one_lt
  have hres : p%4=3 ∨ p%4=1 := by omega
  obtain ⟨hsk,hsym⟩ := prime_character_data (p:=p) hodd
  constructor
  · intro hE
    change CharacterTemplateEnergy (quadraticChar (ZMod p)) (p : ℤ) at hE
    rcases hres with hr|hr
    · let q : ℤ := (p/4 : ℕ)
      have hq : 0≤q := by dsimp [q]; omega
      have hM : (p : ℤ)=4*q+3 := by dsimp [q]; omega
      have hb := skew_template_lower hlarge hodd q hq hM _ (hsk hr) _ hE
      have hbound : q≤1 := by nlinarith [sq_nonneg (q-1)]
      have hcases : q=0 ∨ q=1 := by omega
      rcases hcases with h|h <;> omega
    · have hp5 : 5≤p := by omega
      let q : ℤ := (p/4 : ℕ)
      have hq : 1≤q := by dsimp [q]; omega
      have hM : (p : ℤ)=4*q+1 := by dsimp [q]; omega
      have hb := symmetric_template_lower hlarge hodd q hq hM _ (hsym hr) _ hE
      have hq1 : q=1 := by nlinarith [sq_nonneg (q-1)]
      omega
  · intro h
    rcases h with h|h|h
    · subst p
      exact skew_template_attainment 0 (by norm_num) _ (hsk (by decide))
    · subst p
      exact symmetric_template_attainment 1 (by norm_num) _ (hsym (by decide))
    · subst p
      exact skew_template_attainment 1 (by norm_num) _ (hsk (by decide))

end CompletionTheory.CharacterFloor
