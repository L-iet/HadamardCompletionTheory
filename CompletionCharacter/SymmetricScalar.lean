/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCharacter.SkewScalar
@[expose] public section
namespace CompletionTheory.CharacterFloor
open scoped BigOperators

def scalarSupport (w : Fin 4 → ℤ) : Finset (Fin 4) := Finset.univ.filter (fun i => w i≠0)

theorem square_le_two_discrete {z : ℤ} (hz : z^2≤2) : z^2=0 ∨ z^2=1 := by
  have hlo : -1≤z := by
    by_contra! h
    have : z≤ -2 := by omega
    nlinarith [sq_nonneg (z+2)]
  have hhi : z≤1 := by
    by_contra! h
    have : 2≤z := by omega
    nlinarith [sq_nonneg (z-2)]
  interval_cases z <;> norm_num

theorem squareSum_two_support_card (w : Fin 4 → ℤ) (hw : squareSum w=2) :
    (scalarSupport w).card=2 := by
  have hs : ∀ i,w i≠0 → w i^2=1 := by
    intro i hi
    have hb : w i^2≤squareSum w := Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    rw [hw] at hb
    rcases square_le_two_discrete hb with h|h
    · exfalso; apply hi; nlinarith
    · exact h
  have hsum : squareSum w=((scalarSupport w).card : ℤ) := by
    calc
      squareSum w=∑ i∈scalarSupport w,w i^2 := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro i _ hi
        have hz : w i=0 := by simpa [scalarSupport] using hi
        simp [hz]
      _=∑ _∈scalarSupport w,(1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hs i (Finset.mem_filter.mp hi).2
      _=((scalarSupport w).card : ℤ) := by simp
  exact_mod_cast (hw.symm.trans hsum).symm

theorem squareSum_two_bounds (u v w : Fin 4 → ℤ)
    (hpu : ∀ i,(u i+w i)%2=1) (hpv : ∀ i,(v i+w i)%2=1)
    (hw : squareSum w=2) :
    2≤squareSum u ∧ scalarDot w v^2+4≤2*squareSum v := by
  classical
  let S := scalarSupport w
  have hScard : S.card=2 := squareSum_two_support_card w hw
  have hCcard : (Sᶜ).card=2 := by simp [Finset.card_compl,hScard]
  have hcount : (∑ i : Fin 4,if i∈Sᶜ then (1 : ℤ) else 0)=2 := by
    rw [← Finset.sum_filter]
    have he : Finset.univ.filter (fun i : Fin 4 => i∈Sᶜ)=Sᶜ := by ext i; simp
    rw [he]
    simp [hCcard]
  have hodd (a : Fin 4 → ℤ) (hp : ∀ i,(a i+w i)%2=1) :
      ∀ i,i∈Sᶜ → 1≤a i^2 := by
    intro i hi
    have hwi : w i=0 := by simpa [S,scalarSupport] using hi
    have ha := hp i
    rw [hwi,add_zero] at ha
    apply integer_square_positive
    intro hz
    norm_num [hz] at ha
  have hU : 2≤squareSum u := by
    have hh : ∀ i,(if i∈Sᶜ then (1 : ℤ) else 0)≤u i^2 := by
      intro i
      split_ifs with hi
      · exact hodd u hpu i hi
      · exact sq_nonneg _
    have he := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hh i)
    rw [hcount] at he
    exact he
  let v' : Fin 4 → ℤ := fun i => if i∈S then v i else 0
  have hV : squareSum v'+2≤squareSum v := by
    have hh : ∀ i,v' i^2+(if i∈Sᶜ then (1 : ℤ) else 0)≤v i^2 := by
      intro i
      by_cases hi : i∈S
      · simp [v',hi]
      · simp only [v',hi,ite_false,Finset.mem_compl,not_false_eq_true,ite_true,zero_pow (by decide : 2≠0),zero_add]
        exact hodd v hpv i (Finset.mem_compl.mpr hi)
    have he := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hh i)
    rw [Finset.sum_add_distrib,hcount] at he
    exact he
  have hdot : scalarDot w v'=scalarDot w v := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i∈S
    · simp [v',hi]
    · have hz : w i=0 := by simpa [S,scalarSupport] using hi
      simp [hz]
  have hcs := scalar_cauchy w v'
  rw [hw,hdot] at hcs
  exact ⟨hU,by nlinarith⟩

theorem symmetric_squareSum_even (u v w : Fin 4 → ℤ)
    (hpu : ∀ i,(u i+w i)%2=1) (hpv : ∀ i,(v i+w i)%2=1)
    (huv : scalarDot u v=0) : squareSum w%2=0 := by
  have hsquare : ∀ a : ZMod 2,a^2=a := by decide
  have hu : ∀ i,(u i : ZMod 2)+(w i : ZMod 2)=1 := by
    intro i
    have hh := (ZMod.intCast_eq_intCast_iff' (u i+w i) 1 2).mpr (by simpa using hpu i)
    simpa using hh
  have hv : ∀ i,(v i : ZMod 2)+(w i : ZMod 2)=1 := by
    intro i
    have hh := (ZMod.intCast_eq_intCast_iff' (v i+w i) 1 2).mpr (by simpa using hpv i)
    simpa using hh
  have hprod : ∀ i,(u i : ZMod 2)*(v i : ZMod 2)=1-(w i : ZMod 2) := by
    intro i
    have hui : (u i : ZMod 2)=1-(w i : ZMod 2) := by linear_combination hu i
    have hvi : (v i : ZMod 2)=1-(w i : ZMod 2) := by linear_combination hv i
    rw [hui,hvi,← pow_two]
    exact hsquare _
  have hdot : (∑ i,(u i : ZMod 2)*(v i : ZMod 2))=0 := by
    have hh := congrArg (fun z : ℤ => (z : ZMod 2)) huv
    simpa [scalarDot] using hh
  have he : (squareSum w : ZMod 2)=0 := by
    calc
      (squareSum w : ZMod 2)=∑ i,(w i : ZMod 2)^2 := by simp [squareSum]
      _=∑ i,(w i : ZMod 2) := Finset.sum_congr rfl (fun i _ => hsquare _)
      _=∑ i,(1-(u i : ZMod 2)*(v i : ZMod 2)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hprod]
        ring
      _=0 := by rw [Finset.sum_sub_distrib,hdot]; norm_num <;> decide
  exact (ZMod.intCast_eq_intCast_iff' (squareSum w) 0 2).mp he

theorem odd_symmetric_threshold (k : ℤ) : (2*k^2+2*k+1)%2=1 := by omega

theorem symmetric_scalar_floor (k t : ℤ) (hk : 1≤k) (u v w : Fin 4 → ℤ)
    (hpu : ∀ i,(u i+w i)%2=1) (hpv : ∀ i,(v i+w i)%2=1)
    (huv : scalarDot u v=0)
    (he : 2*scalarDot w v=squareSum u-(4*k+1)*squareSum w)
    (ht : 4*t=(4*k+1)*squareSum u+squareSum v) (hodd : t%2=1) :
    2*k^2+2*k+1≤t := by
  have hWpos := scalar_constant_nonzero u v w hpu he
  have hWeven := symmetric_squareSum_even u v w hpu hpv huv
  have hS := squareSum_nonnegative u
  by_cases hW : squareSum w=2
  · obtain ⟨hS2,hV⟩ := squareSum_two_bounds u v w hpu hpv hW
    have he2 := congrArg (fun z : ℤ => z^2) he
    rw [hW] at he2
    have hprod : 0≤(4*k+1)*(squareSum u-2) := mul_nonneg (by omega) (by omega)
    nlinarith [sq_nonneg (squareSum u-2)]
  · have hW4 : 4≤squareSum w := by omega
    have hcs := scalar_energy_cauchy u v w he ht
    have hcross : 0≤squareSum u*(2*(4*k+1)*squareSum w+squareSum u) :=
      mul_nonneg hS (by positivity)
    have hmul : 0≤(16*t-(4*k+1)^2*squareSum w)*squareSum w := by nlinarith
    have hbase : (4*k+1)^2*squareSum w≤16*t := by
      by_contra! hbad
      have hh := mul_neg_of_neg_of_pos (by omega : 16*t-(4*k+1)^2*squareSum w<0) hWpos
      omega
    have h4 : (4*k+1)^2≤4*t := by
      have hh := mul_nonneg (sq_nonneg (4*k+1)) (by omega : 0≤squareSum w-4)
      nlinarith
    have hTod := odd_symmetric_threshold k
    by_contra! hbad
    have htlow : t≤2*k^2+2*k+1-2 := by omega
    nlinarith [sq_nonneg k]

end CompletionTheory.CharacterFloor
