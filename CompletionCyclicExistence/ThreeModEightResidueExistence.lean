/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCyclicExistence.DirichletPrimeSupport
public import CompletionCyclicExistence.PrimeProgressionArithmetic
public import CompletionCyclicExistence.PrimeProgressionResidueData
@[expose] public section
namespace CompletionTheory.ThreeSquares

 theorem residue_data_exists_eight_mul_add_three (k : ℕ) :
    ∃ d x y : ℤ,0<d ∧ x^2+d=y*(d*((8*k+3:ℕ):ℤ)-1) := by
  obtain ⟨q,hlarge,hprime,hmod⟩ := large_prime_in_progression (4*k+1) (4*(8*k+3))
    (4*k+1) (by omega) (three_mod_eight_progression_coprime k)
  letI : Fact q.Prime := ⟨hprime⟩
  obtain ⟨j,hj⟩ := three_mod_eight_progression_parameter k q hmod hlarge.le
  have hp := three_mod_eight_progression_data k j q hj
  have hD : (8*(j:ℤ)+1)*((8*k+3:ℕ):ℤ)=2*(q:ℤ)+1 := by simpa using hp.2
  obtain ⟨x,y,hxy⟩ := prime_progression_residue_data (8*k+3) q (8*(j:ℤ)+1)
    (by omega) hp.1 hD
  exact ⟨8*(j:ℤ)+1,x,y,by omega,hxy⟩

 theorem residue_data_exists_three_mod_eight (n : ℕ) (hn : n%8=3) :
    ∃ d x y : ℤ,0<d ∧ x^2+d=y*(d*(n:ℤ)-1) := by
  obtain ⟨k,rfl⟩ : ∃ k : ℕ,n=8*k+3 := ⟨n/8,by omega⟩
  exact residue_data_exists_eight_mul_add_three k

end CompletionTheory.ThreeSquares
