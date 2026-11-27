/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCharacter.Scalar
@[expose] public section
namespace CompletionTheory.CharacterFloor
open scoped BigOperators

theorem odd_away_square_lower (a w : Fin 4 → ℤ) (i : Fin 4)
    (hp : ∀ j,(a j+w j)%2=1) (hw : ∀ j,j≠i → w j=0) :
    3≤∑ j∈Finset.univ.erase i,a j^2 := by
  have hcard : (Finset.univ.erase i : Finset (Fin 4)).card=3 := by simp
  calc
    (3 : ℤ)=∑ _∈Finset.univ.erase i,(1 : ℤ) := by simp [hcard]
    _≤∑ j∈Finset.univ.erase i,a j^2 := by
      apply Finset.sum_le_sum
      intro j hj
      have hji := (Finset.mem_erase.mp hj).1
      have hpar := hp j
      rw [hw j hji,add_zero] at hpar
      apply integer_square_positive
      intro hz
      norm_num [hz] at hpar

theorem squareSum_one_bounds (u v w : Fin 4 → ℤ)
    (hpu : ∀ i,(u i+w i)%2=1) (hpv : ∀ i,(v i+w i)%2=1)
    (hw : squareSum w=1) :
    3≤squareSum u ∧ scalarDot w v^2+3≤squareSum v := by
  obtain ⟨i,hi,hzero⟩ := squareSum_one_unique w hw
  have hu := odd_away_square_lower u w i hpu hzero
  have hv := odd_away_square_lower v w i hpv hzero
  have hdu := Finset.sum_erase_add (s:=Finset.univ) (f:=fun k => u k^2) (Finset.mem_univ i)
  have hdv := Finset.sum_erase_add (s:=Finset.univ) (f:=fun k => v k^2) (Finset.mem_univ i)
  change _=squareSum u at hdu
  change _=squareSum v at hdv
  have hdot : scalarDot w v=w i*v i := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [hzero j hji,zero_mul]
    · intro h
      simp at h
  have hdsq : scalarDot w v^2=v i^2 := by rw [hdot,mul_pow,hi,one_mul]
  constructor
  · nlinarith [sq_nonneg (u i)]
  · nlinarith

theorem odd_skew_threshold (k : ℤ) : (k^2+3*k+3)%2=1 := by
  have hk : k%2=0 ∨ k%2=1 := by omega
  rcases hk with hk|hk <;> simp [pow_two,Int.add_emod,Int.mul_emod,hk]

theorem skew_scalar_floor (k t : ℤ) (hk : 0≤k) (u v w : Fin 4 → ℤ)
    (hpu : ∀ i,(u i+w i)%2=1) (hpv : ∀ i,(v i+w i)%2=1)
    (he : 2*scalarDot w v=squareSum u-(4*k+3)*squareSum w)
    (ht : 4*t=(4*k+3)*squareSum u+squareSum v) (hodd : t%2=1) :
    k^2+3*k+3≤t := by
  have hWpos := scalar_constant_nonzero u v w hpu he
  have hS := squareSum_nonnegative u
  by_cases hW : squareSum w=1
  · obtain ⟨hS3,hV⟩ := squareSum_one_bounds u v w hpu hpv hW
    have he2 := congrArg (fun z : ℤ => z^2) he
    rw [hW] at he2
    have hprod : 0≤(4*k+3)*(squareSum u-3) := mul_nonneg (by omega) (by omega)
    nlinarith [sq_nonneg (squareSum u-3)]
  · have hW2 : 2≤squareSum w := by omega
    have hcs := scalar_energy_cauchy u v w he ht
    have hcross : 0≤squareSum u*(2*(4*k+3)*squareSum w+squareSum u) :=
      mul_nonneg hS (by positivity)
    have hmul : 0≤(16*t-(4*k+3)^2*squareSum w)*squareSum w := by nlinarith
    have hbase : (4*k+3)^2*squareSum w≤16*t := by
      by_contra! hbad
      have hh := mul_neg_of_neg_of_pos (by omega : 16*t-(4*k+3)^2*squareSum w<0) hWpos
      omega
    have h8 : (4*k+3)^2≤8*t := by
      have hh := mul_nonneg (sq_nonneg (4*k+3)) (by omega : 0≤squareSum w-2)
      nlinarith
    have hTod := odd_skew_threshold k
    by_contra! hbad
    have htlow : t≤k^2+3*k+3-2 := by omega
    nlinarith [sq_nonneg k]

end CompletionTheory.CharacterFloor
