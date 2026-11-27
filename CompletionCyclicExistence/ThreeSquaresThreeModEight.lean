/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCyclicExistence.ResidueExistenceInterface
public import CompletionCyclicExistence.ResidueThreeSquareRepresentation
@[expose] public section
namespace CompletionTheory.ThreeSquares

 theorem three_squares_of_three_mod_eight (n : ℕ) (hn : n%8=3) :
    ∃ a b c : ℤ,(n:ℤ)=a^2+b^2+c^2 := by
  obtain ⟨d,x,y,hd,hxy⟩ := residue_data_exists_three_mod_eight_api n hn
  exact residue_data_three_square_representation n d x y (by omega) hd hxy

end CompletionTheory.ThreeSquares
