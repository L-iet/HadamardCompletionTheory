/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCyclicExistence.SkewCyclicAllEnergy
public import CompletionCharacter.PrimeCharacter
@[expose] public section
namespace CompletionTheory.ThreeSquares
open CharacterFloor

 theorem skew_character_large_energy_region {m : ℕ} [NeZero m] (hm : m%4=3)
    (L : ZMod m → ℤ) (hD : IsCharacterData L (-1)) (t : ℤ) (ht : Odd t)
    (hT : skewThreshold m≤t) : CharacterTemplateEnergy L t ∧ CyclicNormSolution m t := by
  let q : ℤ := (m/4:ℕ)
  have hMnat : m=4*(m/4)+3 := by omega
  have hM : (m:ℤ)=4*q+3 := by dsimp [q];exact_mod_cast hMnat
  have hThreshold : skewThreshold m=q^2+3*q+3 := by
    unfold skewThreshold
    have he : (m:ℤ)^2+6*m+21=16*(q^2+3*q+3) := by rw [hM];ring
    rw [he]
    omega
  have hTq : q^2+3*q+3≤t := by rw [←hThreshold];exact hT
  have hE := skew_template_all_odd_energies q hM L hD t ht hTq
  exact ⟨hE,character_template_actual_solution L t hE⟩

 theorem skew_character_threshold_sharp {m : ℕ} [NeZero m] (hm : m%4=3)
    (L : ZMod m → ℤ) (hD : IsCharacterData L (-1)) :
    IsSharpCharacterFloor L (skewThreshold m) := by
  exact (character_span_sharp_energy_floors (by omega : 1<m)
    (by omega : m%2=1) L).1 hm hD

 theorem prime_skew_large_energy_region (p : ℕ) [Fact p.Prime] (hp : p%4=3)
    (t : ℤ) (ht : Odd t) (hT : skewThreshold p≤t) : CyclicNormSolution p t := by
  have hD := (prime_character_data (p:=p) (by omega : p%2=1)).1 hp
  exact (skew_character_large_energy_region hp (quadraticChar (ZMod p)) hD t ht hT).2

end CompletionTheory.ThreeSquares
