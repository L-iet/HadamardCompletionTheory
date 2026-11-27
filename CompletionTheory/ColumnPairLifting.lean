/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Data.Finset.Powerset
public import CompletionTheory.ModularRowCorrection
@[expose] public section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory
open Matrix
theorem near_modular_sign_sum_values {q : ℕ} (hq : 3≤q) (hodd : q%2=1)
    (f : Fin (4*(q+1)) → ℤ) (hf : ∀ i,f i=1 ∨ f i= -1)
    (hdiv : (q : ℤ)∣∑ i,f i) :
    (∑ i,f i)= -(4*q : ℤ) ∨ (∑ i,f i)= -(2*q : ℤ) ∨ (∑ i,f i)=0 ∨
      (∑ i,f i)=(2*q : ℤ) ∨ (∑ i,f i)=(4*q : ℤ) := by
  have hsum := integer_sign_sum_mod_four Finset.univ f (fun i _ => hf i)
  have hprod := integer_prod_sign Finset.univ f (fun i _ => hf i)
  simp only [Finset.card_univ,Fintype.card_fin,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at hsum
  have heven : (∑ i,f i)%2=0 := by rcases hprod with hp|hp <;> rw [hp] at hsum <;> omega
  obtain ⟨z,hz⟩ := hdiv
  have hq3 : (3 : ℤ)≤q := by exact_mod_cast hq
  have hqZ : (0 : ℤ)<q := by omega
  have hqmod : (q : ℤ)%2=1 := by exact_mod_cast hodd
  have hzeven : z%2=0 := by rw [hz,Int.mul_emod,hqmod,one_mul,Int.emod_emod] at heven; exact heven
  obtain ⟨hl,hu⟩ := integer_sign_sum_bounds f hf
  simp only [Fintype.card_fin,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at hl hu
  rw [hz] at hl hu
  have hzl : -5≤z := by
    by_contra hh
    have hz6 : z≤ -6 := by omega
    have hm := mul_le_mul_of_nonneg_left hz6 hqZ.le
    nlinarith
  have hzu : z≤5 := by
    by_contra hh
    have hz6 : 6≤z := by omega
    have hm := mul_le_mul_of_nonneg_left hz6 hqZ.le
    nlinarith
  have hzvalues : z= -4 ∨ z= -2 ∨ z=0 ∨ z=2 ∨ z=4 := by omega
  rcases hzvalues with hh|hh|hh|hh|hh <;> rw [hz,hh] <;> omega

theorem near_modular_no_half_inner {r q : ℕ} (hr : 4*(q+1)^2<r*q^2) (hq : 3≤q) (hodd : q%2=1)
    (P : Matrix (Fin r) (Fin (4*(q+1))) ℤ)
    (hs : ∀ i j,P i j=1 ∨ P i j= -1)
    (hg : ∀ i j,(∑ k,P i k*P j k)=if i=j then (4*(q+1) : ℤ) else 0)
    (v : Fin (4*(q+1)) → ℤ) (hv : ∀ k,v k=1 ∨ v k= -1)
    (hm : ∀ i,(q : ℤ)∣∑ k,P i k*v k) :
    ∀ i,(∑ k,P i k*v k)= -(4*q : ℤ) ∨ (∑ k,P i k*v k)=0 ∨
      (∑ k,P i k*v k)=(4*q : ℤ) := by
  classical
  have hprod (i : Fin r) (k : Fin (4*(q+1))) : P i k*v k=1 ∨ P i k*v k= -1 := by
    rcases hs i k with hh|hh <;> rcases hv k with gg|gg <;> simp [hh,gg]
  have hvalues (i : Fin r) := near_modular_sign_sum_values hq hodd _ (hprod i) (hm i)
  have hgq : ∀ i j,(∑ k,P i k*P j k)=if i=j then 4*((q+1 : ℕ) : ℤ) else 0 := by
    intro i j
    simpa only [Nat.cast_add,Nat.cast_one] using hg i j
  have hgN : ∀ i j,(∑ k,P i k*P j k)=if i=j then ((4*(q+1) : ℕ) : ℤ) else 0 := by
    intro i j
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using hg i j
  have hcommon (i j : Fin r) : (∑ k,P i k*v k)%4=(∑ k,P j k*v k)%4 := by
    have hi := integer_sign_sum_mod_four Finset.univ (fun k => P i k*v k) (fun k _ => hprod i k)
    have hj := integer_sign_sum_mod_four Finset.univ (fun k => P j k*v k) (fun k _ => hprod j k)
    rw [Finset.prod_mul_distrib] at hi hj
    rw [integer_frame_row_parity P hs hgq i j] at hi
    exact hi.trans hj.symm
  have hq3 : (3 : ℤ)≤q := by exact_mod_cast hq
  have hqZ : (0 : ℤ)<q := by omega
  have hq3R : (3 : ℝ)≤q := by exact_mod_cast hq
  have hqR : (0 : ℝ)<q := by linarith
  have hoddZ : (q : ℤ)%2=1 := by exact_mod_cast hodd
  have hhalfmod : (2*(q : ℤ))%4=2 ∧ (-(2*(q : ℤ)))%4=2 := by omega
  have hNmod : (4*(q : ℤ))%4=0 ∧ (-(4*(q : ℤ)))%4=0 := by omega
  have hbad (i : Fin r) (hres : (∑ k,P i k*v k)%4=2) : False := by
    have hall (j : Fin r) : (∑ k,P j k*v k)^2=4*(q : ℤ)^2 := by
      have hc := hcommon j i
      rw [hres] at hc
      rcases hvalues j with hj|hj|hj|hj|hj <;> rw [hj] at hc ⊢ <;> first | nlinarith | omega
    have hpartial := integer_frame_partial P hs hgN
    have hgram : modularFrameReal P*(modularFrameReal P)ᵀ=(4*((q : ℝ)+1)) • 1 := by
      simpa only [Fintype.card_fin,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using hpartial.2
    have hb := rowGram_bessel (modularFrameReal P) (4*((q : ℝ)+1)) (by positivity) hgram (fun k => (v k : ℝ))
    have hnorm (k : Fin (4*(q+1))) : (v k : ℝ)^2=1 := by rcases hv k with hvv|hvv <;> simp [hvv]
    have hinner (j : Fin r) : (∑ k,modularFrameReal P j k*(v k : ℝ))^2=4*(q : ℝ)^2 := by
      have hhR : ((∑ k,P j k*v k : ℤ) : ℝ)^2=4*(q : ℝ)^2 := by exact_mod_cast hall j
      simpa only [Int.cast_sum,Int.cast_mul,modularFrameReal] using hhR
    simp only [hinner,hnorm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at hb
    have hrR : 4*((q : ℝ)+1)^2<(r : ℝ)*(q : ℝ)^2 := by exact_mod_cast hr
    nlinarith
  intro i
  rcases hvalues i with hh|hh|hh|hh|hh
  · exact Or.inl hh
  · exact (hbad i (by rw [hh]; exact hhalfmod.2)).elim
  · exact Or.inr (Or.inl hh)
  · exact (hbad i (by rw [hh]; exact hhalfmod.1)).elim
  · exact Or.inr (Or.inr hh)



theorem integer_sign_frame_bessel {r N : ℕ} (hN : 0<N)
    (P : Matrix (Fin r) (Fin N) ℤ) (hs : ∀ i j,P i j=1 ∨ P i j= -1)
    (hg : ∀ i k,(∑ j,P i j*P k j)=if i=k then (N : ℤ) else 0)
    (v : Fin N → ℤ) (hv : ∀ j,v j=1 ∨ v j= -1) :
    (∑ i,(∑ j,P i j*v j)^2)≤(N : ℤ)^2 := by
  have hpartial := integer_frame_partial P hs hg
  have hNR : (0 : ℝ)<N := by exact_mod_cast hN
  have hgram : modularFrameReal P*(modularFrameReal P)ᵀ=(N : ℝ) • 1 := by
    simpa only [Fintype.card_fin] using hpartial.2
  have hb := rowGram_bessel (modularFrameReal P) (N : ℝ) hNR hgram (fun j => (v j : ℝ))
  have hnorm (j : Fin N) : (v j : ℝ)^2=1 := by rcases hv j with h|h <;> simp [h]
  simp only [modularFrameReal,hnorm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hb
  have hh : (∑ i,(∑ j,(P i j : ℝ)*(v j : ℝ))^2)≤(N : ℝ)^2 := by nlinarith
  exact_mod_cast hh

theorem near_modular_nonzero_unique {r q : ℕ} (hr : 4*(q+1)^2<r*q^2) (hq : 3≤q) (hodd : q%2=1)
    (P : Matrix (Fin r) (Fin (4*(q+1))) ℤ)
    (hs : ∀ i j,P i j=1 ∨ P i j= -1)
    (hg : ∀ i k,(∑ j,P i j*P k j)=if i=k then (4*(q+1) : ℤ) else 0)
    (v : Fin (4*(q+1)) → ℤ) (hv : ∀ j,v j=1 ∨ v j= -1)
    (hm : ∀ i,(q : ℤ)∣∑ j,P i j*v j) :
    ∀ i k,(∑ j,P i j*v j)≠0 → (∑ j,P k j*v j)≠0 → i=k := by
  classical
  have hvals := near_modular_no_half_inner hr hq hodd P hs hg v hv hm
  have hgN : ∀ i k,(∑ j,P i j*P k j)=if i=k then ((4*(q+1) : ℕ) : ℤ) else 0 := by
    intro i k
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using hg i k
  have hb := integer_sign_frame_bessel (show 0<4*(q+1) from Nat.mul_pos (Nat.zero_lt_succ 3) (Nat.succ_pos q)) P hs hgN v hv
  simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at hb
  have hsq (i : Fin r) (hi : (∑ j,P i j*v j)≠0) : (∑ j,P i j*v j)^2=16*(q : ℤ)^2 := by
    rcases hvals i with hh|hh|hh
    · rw [hh]
      ring
    · exact (hi hh).elim
    · rw [hh]
      ring
  intro i k hi hk
  by_contra hne
  have hsub : ({i,k} : Finset (Fin r))⊆Finset.univ := Finset.subset_univ _
  have hh := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun a (_ : a∈Finset.univ) _ => sq_nonneg (∑ j,P a j*v j))
  rw [Finset.sum_pair hne,hsq i hi,hsq k hk] at hh
  have hqZ : (3 : ℤ)≤q := by exact_mod_cast hq
  have hp : 0≤(q : ℤ)*((q : ℤ)-3) := mul_nonneg (by omega) (by omega)
  nlinarith

noncomputable def signDisagreement {N : ℕ} (u v : Fin N → ℤ) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun j => u j≠v j)

theorem sign_inner_disagreement {N : ℕ} (u v : Fin N → ℤ)
    (hu : ∀ j,u j=1 ∨ u j= -1) (hv : ∀ j,v j=1 ∨ v j= -1) :
    (∑ j,u j*v j)=(N : ℤ)-2*((signDisagreement u v).card : ℤ) := by
  classical
  have he (j : Fin N) : u j*v j=1-2*(if u j≠v j then (1 : ℤ) else 0) := by
    rcases hu j with h|h <;> rcases hv j with g|g <;> norm_num [h,g]
  have hh : (∑ j,u j*v j)=∑ j,(1-2*(if u j≠v j then (1 : ℤ) else 0)) :=
    Finset.sum_congr rfl (fun j _ => he j)
  rw [hh,Finset.sum_sub_distrib,← Finset.mul_sum]
  simp only [signDisagreement,Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]

theorem near_extreme_two_disagreements {q : ℕ}
    (u v : Fin (4*(q+1)) → ℤ)
    (hu : ∀ j,u j=1 ∨ u j= -1) (hv : ∀ j,v j=1 ∨ v j= -1)
    (hdot : (∑ j,u j*v j)=4*(q : ℤ)) : (signDisagreement u v).card=2 := by
  have hh := sign_inner_disagreement u v hu hv
  simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,hdot] at hh
  omega


theorem two_sign_sum_zero_iff_products_opposite {N : ℕ} (T : Finset (Fin N)) (hT : T.card=2)
    (u v : Fin N → ℤ) (hu : ∀ j,u j=1 ∨ u j= -1) (hv : ∀ j,v j=1 ∨ v j= -1) :
    (∑ j∈T,u j*v j)=0 ↔ (∏ j∈T,u j)= -(∏ j∈T,v j) := by
  have hsg (j : Fin N) : u j*v j=1 ∨ u j*v j= -1 := by
    rcases hu j with h|h <;> rcases hv j with g|g <;> simp [h,g]
  have hm := integer_sign_sum_mod_four T (fun j => u j*v j) (fun j _ => hsg j)
  rw [Finset.prod_mul_distrib] at hm
  have hl := Finset.sum_le_sum (s := T) (fun j _ => show (-1 : ℤ)≤u j*v j from by rcases hsg j with h|h <;> omega)
  have hh := Finset.sum_le_sum (s := T) (fun j _ => show u j*v j≤(1 : ℤ) from by rcases hsg j with h|h <;> omega)
  simp only [Finset.sum_const,nsmul_eq_mul,hT] at hl hh hm
  norm_num at hl hh hm
  have hp := integer_prod_sign T u (fun j _ => hu j)
  have hq := integer_prod_sign T v (fun j _ => hv j)
  rcases hp with hp|hp <;> rcases hq with hq|hq <;> rw [hp,hq] at hm ⊢ <;> omega

theorem one_negative_of_near_max_sum {r : ℕ} (f : Fin r → ℤ)
    (hf : ∀ i,f i=1 ∨ f i= -1) (hsum : (∑ i,f i)=(r : ℤ)-2) :
    ∃ i,f i= -1 ∧ ∀ k,k≠i → f k=1 := by
  classical
  let T := Finset.univ.filter (fun i => f i= -1)
  have hcount : (∑ i : Fin r,if f i= -1 then (1 : ℤ) else 0)=(T.card : ℤ) := by
    simp only [T,Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.sum_const,nsmul_eq_mul,mul_one]
  have he (i : Fin r) : f i=1-2*(if f i= -1 then (1 : ℤ) else 0) := by
    rcases hf i with h|h <;> simp [h]
  have hh : (∑ i,f i)=(r : ℤ)-2*(T.card : ℤ) := by
    calc
      (∑ i,f i)=(∑ i,(1-2*(if f i= -1 then (1 : ℤ) else 0))) :=
        Finset.sum_congr rfl (fun i _ => he i)
      _=(r : ℤ)-2*(T.card : ℤ) := by
        rw [Finset.sum_sub_distrib,← Finset.mul_sum,hcount]
        simp
  have hc : T.card=1 := by omega
  obtain ⟨i,hi⟩ := Finset.card_eq_one.mp hc
  have him : i∈T := by rw [hi]; simp
  refine ⟨i,(Finset.mem_filter.mp him).2,?_⟩
  intro k hki
  have hn : k∉T := by rw [hi]; simp [hki]
  have hkn : f k≠ -1 := by intro h; exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  exact (hf k).resolve_right hkn

theorem abs_sign_sum_outlier_iff {r : ℕ} (hr : 2<r) (f : Fin r → ℤ)
    (hf : ∀ i,f i=1 ∨ f i= -1) :
    |∑ i,f i|=(r : ℤ)-2 ↔ ∃! i,∀ k,k≠i → f k= -f i := by
  classical
  have huni (i k : Fin r) (hi : ∀ a,a≠i → f a= -f i)
      (hk : ∀ a,a≠k → f a= -f k) : i=k := by
    by_contra hne
    obtain ⟨a,hai,hak⟩ := Fin.exists_ne_and_ne_of_two_lt i k hr
    have h1 := hi a hai
    have h2 := hk a hak
    have h3 := hi k (Ne.symm hne)
    rcases hf i with h|h <;> omega
  constructor
  · intro hs
    have hvalues := eq_or_eq_neg_of_abs_eq hs
    have hex : ∃ i,∀ k,k≠i → f k= -f i := by
      rcases hvalues with hh|hh
      · obtain ⟨i,hi,hk⟩ := one_negative_of_near_max_sum f hf hh
        refine ⟨i,?_⟩
        intro k hki
        rw [hi,hk k hki]
        norm_num
      · have hneg (i : Fin r) : -f i=1 ∨ -f i= -1 := by rcases hf i with h|h <;> simp [h]
        have hsum : (∑ i,-f i)=(r : ℤ)-2 := by rw [Finset.sum_neg_distrib,hh]; ring
        obtain ⟨i,hi,hk⟩ := one_negative_of_near_max_sum (fun i => -f i) hneg hsum
        refine ⟨i,?_⟩
        intro k hki
        have hh := hk k hki
        omega
    obtain ⟨i,hi⟩ := hex
    exact ⟨i,hi,fun k hk => (huni i k hi hk).symm⟩
  · rintro ⟨i,hi,_⟩
    have he (k : Fin r) : f k= -f i+(if k=i then 2*f i else 0) := by
      by_cases hki : k=i
      · subst k
        simp only [ite_true]
        ring
      · rw [hi k hki,if_neg hki,add_zero]
    have hsum : (∑ k,f k)=(2-(r : ℤ))*f i := by
      calc
        (∑ k,f k)=(∑ k,(-f i+(if k=i then 2*f i else 0))) := Finset.sum_congr rfl (fun k _ => he k)
        _=(2-(r : ℤ))*f i := by rw [Finset.sum_add_distrib]; simp; ring
    have hrZ : (0 : ℤ)≤(r : ℤ)-2 := by
      have hrI : (2 : ℤ)<r := by exact_mod_cast hr
      omega
    rw [hsum]
    rcases hf i with hh|hh
    · rw [hh,mul_one,show (2-(r : ℤ))= -((r : ℤ)-2) by ring,abs_neg,abs_of_nonneg (by omega)]
    · rw [hh,mul_neg_one,show -(2-(r : ℤ))=(r : ℤ)-2 by ring,abs_of_nonneg (by omega)]


def coordinateFlipSign {N : ℕ} (T : Finset (Fin N)) (j : Fin N) : ℤ := if j∈T then -1 else 1

def flipSignVector {N : ℕ} (T : Finset (Fin N)) (u : Fin N → ℤ) : Fin N → ℤ :=
  fun j => u j*coordinateFlipSign T j

def normalizeSignCode {N : ℕ} (hN : 0<N) (u : Fin N → ℤ) : Fin N → Bool :=
  fun j => decide (u j*u ⟨0,hN⟩= -1)

noncomputable def modularCandidatesAt {r N : ℕ} (q : ℕ) (P : Matrix (Fin r) (Fin N) ℤ) :
    Finset (Fin N → Bool) := by
  classical
  exact Finset.univ.filter (fun x => positiveFirstBit x ∧ ∀ i,(q : ℤ)∣∑ j,P i j*modularBitSign (x j))

noncomputable def columnPairCandidates {r N : ℕ} (P : Matrix (Fin r) (Fin N) ℤ) :
    Finset (Finset (Fin N)) := by
  classical
  exact (Finset.univ.powersetCard 2).filter (fun T => |∑ i,∏ j∈T,P i j|=(r : ℤ)-2)

theorem coordinateFlipSign_sign {N : ℕ} (T : Finset (Fin N)) (j : Fin N) :
    coordinateFlipSign T j=1 ∨ coordinateFlipSign T j= -1 := by
  unfold coordinateFlipSign
  split_ifs <;> simp

theorem flipSignVector_sign {N : ℕ} (T : Finset (Fin N)) (u : Fin N → ℤ)
    (hu : ∀ j,u j=1 ∨ u j= -1) (j : Fin N) :
    flipSignVector T u j=1 ∨ flipSignVector T u j= -1 := by
  rcases hu j with h|h <;> rcases coordinateFlipSign_sign T j with g|g <;> simp [flipSignVector,h,g]

theorem normalizeSignCode_sign {N : ℕ} (hN : 0<N) (u : Fin N → ℤ)
    (hu : ∀ j,u j=1 ∨ u j= -1) (j : Fin N) :
    modularBitSign (normalizeSignCode hN u j)=u j*u ⟨0,hN⟩ := by
  rcases hu j with h|h <;> rcases hu ⟨0,hN⟩ with g|g <;>
    simp [normalizeSignCode,modularBitSign,h,g]

theorem normalizeSignCode_first {N : ℕ} (hN : 0<N) (u : Fin N → ℤ)
    (hu : ∀ j,u j=1 ∨ u j= -1) : positiveFirstBit (normalizeSignCode hN u) := by
  intro j hj
  have hj0 : j=(⟨0,hN⟩ : Fin N) := Fin.ext hj
  rw [hj0]
  rcases hu ⟨0,hN⟩ with h|h <;> simp [normalizeSignCode,h]

theorem flipSignVector_inner {N : ℕ} (T : Finset (Fin N)) (u v : Fin N → ℤ) :
    (∑ j,v j*flipSignVector T u j)=(∑ j,v j*u j)-2*(∑ j∈T,v j*u j) := by
  classical
  have he (j : Fin N) : v j*flipSignVector T u j=v j*u j-2*(if j∈T then v j*u j else 0) := by
    unfold flipSignVector coordinateFlipSign
    split_ifs <;> ring
  calc
    (∑ j,v j*flipSignVector T u j)=∑ j,(v j*u j-2*(if j∈T then v j*u j else 0)) :=
      Finset.sum_congr rfl (fun j _ => he j)
    _=(∑ j,v j*u j)-2*(∑ j∈T,v j*u j) := by
      rw [Finset.sum_sub_distrib,← Finset.mul_sum]
      simp

theorem flip_pair_inner_profile {r q : ℕ} (P : Matrix (Fin r) (Fin (4*(q+1))) ℤ)
    (hs : ∀ i j,P i j=1 ∨ P i j= -1)
    (hg : ∀ i k,(∑ j,P i j*P k j)=if i=k then (4*(q+1) : ℤ) else 0)
    (T : Finset (Fin (4*(q+1)))) (hT : T.card=2) (i : Fin r)
    (hout : ∀ k,k≠i → (∏ j∈T,P k j)= -(∏ j∈T,P i j)) :
    ∀ k,(∑ j,P k j*flipSignVector T (P i) j)=if k=i then 4*(q : ℤ) else 0 := by
  intro k
  rw [flipSignVector_inner,hg]
  by_cases hki : k=i
  · subst k
    simp only [if_pos rfl]
    have hsquare (j : Fin (4*(q+1))) : P i j*P i j=1 := by rcases hs i j with h|h <;> simp [h]
    simp [hsquare,hT] <;> ring
  · simp only [if_neg hki]
    have hz := (two_sign_sum_zero_iff_products_opposite T hT (P k) (P i) (hs k) (hs i)).mpr (hout k hki)
    rw [hz]
    ring

theorem normalized_flip_pair_modular {r q : ℕ} (hq : 0<q)
    (P : Matrix (Fin r) (Fin (4*(q+1))) ℤ)
    (hs : ∀ i j,P i j=1 ∨ P i j= -1)
    (hg : ∀ i k,(∑ j,P i j*P k j)=if i=k then (4*(q+1) : ℤ) else 0)
    (T : Finset (Fin (4*(q+1)))) (hT : T.card=2) (i : Fin r)
    (hout : ∀ k,k≠i → (∏ j∈T,P k j)= -(∏ j∈T,P i j)) :
    normalizeSignCode (show 0<4*(q+1) from Nat.mul_pos (Nat.zero_lt_succ 3) (Nat.succ_pos q)) (flipSignVector T (P i))∈modularCandidatesAt q P ∧
      normalizeSignCode (show 0<4*(q+1) from Nat.mul_pos (Nat.zero_lt_succ 3) (Nat.succ_pos q)) (flipSignVector T (P i))∉exactSignCandidates P := by
  classical
  let hN : 0<4*(q+1) := by omega
  let w := flipSignVector T (P i)
  have hw (j : Fin (4*(q+1))) : w j=1 ∨ w j= -1 := flipSignVector_sign T (P i) (hs i) j
  have hprofile (k : Fin r) := flip_pair_inner_profile P hs hg T hT i hout k
  have hinner (k : Fin r) : (∑ j,P k j*modularBitSign (normalizeSignCode hN w j))=
      (if k=i then 4*(q : ℤ) else 0)*w ⟨0,hN⟩ := by
    calc
      (∑ j,P k j*modularBitSign (normalizeSignCode hN w j))=
          ∑ j,(P k j*w j)*w ⟨0,hN⟩ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [normalizeSignCode_sign hN w hw j]
        ring
      _=(∑ j,P k j*w j)*w ⟨0,hN⟩ := by rw [Finset.sum_mul]
      _=(if k=i then 4*(q : ℤ) else 0)*w ⟨0,hN⟩ :=
        congrArg (fun z : ℤ => z*w ⟨0,hN⟩) (hprofile k)
  constructor
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,normalizeSignCode_first hN w hw,?_⟩
    intro k
    rw [hinner]
    by_cases hki : k=i
    · rw [if_pos hki]
      exact ⟨4*w ⟨0,hN⟩,by ring⟩
    · rw [if_neg hki,zero_mul]
      exact dvd_zero _
  · intro hx
    have hz := (Finset.mem_filter.mp hx).2.2 i
    rw [hinner,if_pos rfl] at hz
    have hqZ : (0 : ℤ)<q := by exact_mod_cast hq
    rcases hw ⟨0,hN⟩ with h|h <;> rw [h] at hz <;> omega


theorem normalizeSignCode_neg {N : ℕ} (hN : 0<N) (u : Fin N → ℤ) :
    normalizeSignCode hN (-u)=normalizeSignCode hN u := by
  funext j
  simp only [normalizeSignCode,Pi.neg_apply,neg_mul_neg]

theorem normalizeSignCode_positive {N : ℕ} (hN : 0<N) (x : Fin N → Bool)
    (hx : positiveFirstBit x) : normalizeSignCode hN (fun j => modularBitSign (x j))=x := by
  funext j
  apply modularBitSign_injective
  rw [normalizeSignCode_sign hN _ (fun k => modularBitSign_sign _) j]
  have h0 := hx ⟨0,hN⟩ rfl
  simp only [h0,modularBitSign,Bool.false_eq_true,ite_false,mul_one]

theorem normalized_two_flips_injective {N : ℕ} (hN : 4<N) (u : Fin N → ℤ)
    (hu : ∀ j,u j=1 ∨ u j= -1) (T U : Finset (Fin N)) (hT : T.card=2) (hU : U.card=2)
    (hcode : normalizeSignCode (by omega : 0<N) (flipSignVector T u)=
      normalizeSignCode (by omega : 0<N) (flipSignVector U u)) : T=U := by
  classical
  let hNp : 0<N := by omega
  let j0 : Fin N := ⟨0,hNp⟩
  let a := flipSignVector T u j0
  let b := flipSignVector U u j0
  have hunz (j : Fin N) : u j≠0 := by rcases hu j with h|h <;> simp [h]
  have hb0 : b≠0 := by
    rcases flipSignVector_sign U u hu j0 with h|h <;> dsimp [b] <;> rw [h] <;> norm_num
  have hnorm (j : Fin N) : (u j*coordinateFlipSign T j)*a=(u j*coordinateFlipSign U j)*b := by
    have hc := congrArg (fun x => modularBitSign (x j)) hcode
    rw [normalizeSignCode_sign hNp _ (flipSignVector_sign T u hu) j,
      normalizeSignCode_sign hNp _ (flipSignVector_sign U u hu) j] at hc
    exact hc
  have hsmall : (T∪U).card≤4 := by have := Finset.card_union_le T U; omega
  have hlt : (T∪U).card<(Finset.univ : Finset (Fin N)).card := by simp only [Finset.card_univ,Fintype.card_fin]; omega
  obtain ⟨j,_,hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hjT : j∉T := fun hh => hj (Finset.mem_union_left _ hh)
  have hjU : j∉U := fun hh => hj (Finset.mem_union_right _ hh)
  have hc := hnorm j
  simp only [coordinateFlipSign,if_neg hjT,if_neg hjU,mul_one] at hc
  have hab : a=b := mul_left_cancel₀ (hunz j) hc
  apply Finset.ext
  intro k
  have hk := hnorm k
  rw [hab] at hk
  have hh := mul_right_cancel₀ hb0 hk
  have hflip := mul_left_cancel₀ (hunz k) hh
  by_cases hkT : k∈T <;> by_cases hkU : k∈U <;>
    simpa [coordinateFlipSign,hkT,hkU] using hflip


theorem signDisagreement_flip {N : ℕ} (u v : Fin N → ℤ)
    (hu : ∀ j,u j=1 ∨ u j= -1) (hv : ∀ j,v j=1 ∨ v j= -1) :
    v=flipSignVector (signDisagreement u v) u := by
  classical
  funext j
  rcases hu j with h|h <;> rcases hv j with g|g <;>
    simp [flipSignVector,coordinateFlipSign,signDisagreement,h,g]

theorem normalizeSignCode_sign_mul {N : ℕ} (hN : 0<N) (ε : ℤ) (hε : ε=1 ∨ ε= -1)
    (u : Fin N → ℤ) : normalizeSignCode hN (fun j => ε*u j)=normalizeSignCode hN u := by
  funext j
  rcases hε with h|h <;> simp [normalizeSignCode,h]


theorem columnPairCandidates_outlier {r N : ℕ} (hr : 2<r) (P : Matrix (Fin r) (Fin N) ℤ)
    (hs : ∀ i j,P i j=1 ∨ P i j= -1) (T : Finset (Fin N)) :
    T∈columnPairCandidates P ↔ T.card=2 ∧
      ∃! i,∀ k,k≠i → (∏ j∈T,P k j)= -(∏ j∈T,P i j) := by
  classical
  have hsg (i : Fin r) : (∏ j∈T,P i j)=1 ∨ (∏ j∈T,P i j)= -1 :=
    integer_prod_sign T (P i) (fun j _ => hs i j)
  simp only [columnPairCandidates,Finset.mem_filter,Finset.mem_powersetCard,Finset.subset_univ,true_and]
  exact and_congr_right (fun _ => abs_sign_sum_outlier_iff hr (fun i => ∏ j∈T,P i j) hsg)

theorem near_modular_spurious_pair_exists {r q : ℕ} (hr : 4*(q+1)^2<r*q^2)
    (hq : 3≤q) (hodd : q%2=1) (P : Matrix (Fin r) (Fin (4*(q+1))) ℤ)
    (hs : ∀ i j,P i j=1 ∨ P i j= -1)
    (hg : ∀ i k,(∑ j,P i j*P k j)=if i=k then (4*(q+1) : ℤ) else 0)
    (x : Fin (4*(q+1)) → Bool) (hx : x∈modularCandidatesAt q P) (hne : x∉exactSignCandidates P) :
    ∃ (T : Finset (Fin (4*(q+1)))) (i : Fin r),T∈columnPairCandidates P ∧
      (∀ k,k≠i → (∏ j∈T,P k j)= -(∏ j∈T,P i j)) ∧
      x=normalizeSignCode (show 0<4*(q+1) from Nat.mul_pos (Nat.zero_lt_succ 3) (Nat.succ_pos q)) (flipSignVector T (P i)) := by
  classical
  obtain ⟨hxfirst,hm⟩ := (Finset.mem_filter.mp hx).2
  have hnot : ¬∀ i,(∑ j,P i j*modularBitSign (x j))=0 := by
    intro he
    exact hne (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxfirst,he⟩)
  obtain ⟨i,hi⟩ := not_forall.mp hnot
  let v := fun j => modularBitSign (x j)
  have hv (j : Fin (4*(q+1))) : v j=1 ∨ v j= -1 := modularBitSign_sign _
  have hvals := near_modular_no_half_inner hr hq hodd P hs hg v hv hm i
  obtain ⟨ε,hε,hcorr⟩ : ∃ ε : ℤ,(ε=1 ∨ ε= -1) ∧ (∑ j,P i j*v j)=4*(q : ℤ)*ε := by
    rcases hvals with hh|hh|hh
    · exact ⟨-1,Or.inr rfl,by rw [hh]; ring⟩
    · exact (hi hh).elim
    · exact ⟨1,Or.inl rfl,by rw [hh]; ring⟩
  let u := fun j => ε*P i j
  have hu (j : Fin (4*(q+1))) : u j=1 ∨ u j= -1 := by
    rcases hε with h|h <;> rcases hs i j with g|g <;> simp [u,h,g]
  have hdu : (∑ j,u j*v j)=4*(q : ℤ) := by
    have he (j : Fin (4*(q+1))) : u j*v j=ε*(P i j*v j) := by dsimp [u]; ring
    simp_rw [he]
    rw [← Finset.mul_sum,hcorr]
    rcases hε with h|h <;> simp [h]
  let T := signDisagreement u v
  have hT : T.card=2 := near_extreme_two_disagreements u v hu hv hdu
  have hflip : v=flipSignVector T u := signDisagreement_flip u v hu hv
  have hw : flipSignVector T (P i)=(fun j => ε*v j) := by
    funext j
    have hj := congrFun hflip j
    change v j=(ε*P i j)*coordinateFlipSign T j at hj
    change P i j*coordinateFlipSign T j=ε*v j
    rcases hε with h|h <;> rw [h] at hj ⊢ <;> nlinarith
  have huniq := near_modular_nonzero_unique hr hq hodd P hs hg v hv hm
  have hzero (k : Fin r) (hki : k≠i) : (∑ j,P k j*v j)=0 := by
    by_contra hn
    exact hki (huniq k i hn hi)
  have hout (k : Fin r) (hki : k≠i) : (∏ j∈T,P k j)= -(∏ j∈T,P i j) := by
    have hsumzero : (∑ j,P k j*flipSignVector T (P i) j)=0 := by
      rw [hw]
      have he (j : Fin (4*(q+1))) : P k j*(ε*v j)=ε*(P k j*v j) := by ring
      simp_rw [he]
      rw [← Finset.mul_sum,hzero k hki,mul_zero]
    rw [flipSignVector_inner,hg k i,if_neg hki] at hsumzero
    have htwo : (∑ j∈T,P k j*P i j)=0 := by omega
    exact (two_sign_sum_zero_iff_products_opposite T hT (P k) (P i) (hs k) (hs i)).mp htwo
  have hr2 : 2<r := by
    by_contra hn
    have hm := Nat.mul_le_mul_right (q^2) (show r≤2 by omega)
    nlinarith
  have hOutUnique : ∃! j : Fin r,∀ k,k≠j → (∏ a∈T,P k a)= -(∏ a∈T,P j a) := by
    refine ⟨i,hout,?_⟩
    intro k hk
    by_contra hki
    obtain ⟨a,hai,hak⟩ := Fin.exists_ne_and_ne_of_two_lt i k hr2
    have h1 := hout a hai
    have h2 := hk a hak
    have h3 := hout k hki
    rcases integer_prod_sign T (P i) (fun j _ => hs i j) with hh|hh <;> omega
  have hA : T∈columnPairCandidates P := (columnPairCandidates_outlier hr2 P hs T).mpr ⟨hT,hOutUnique⟩
  refine ⟨T,i,hA,hout,?_⟩
  rw [hw,normalizeSignCode_sign_mul _ ε hε v]
  exact (normalizeSignCode_positive _ x hxfirst).symm


theorem normalized_flip_pair_inner_profile {r q : ℕ}
    (P : Matrix (Fin r) (Fin (4*(q+1))) ℤ)
    (hs : ∀ i j,P i j=1 ∨ P i j= -1)
    (hg : ∀ i k,(∑ j,P i j*P k j)=if i=k then (4*(q+1) : ℤ) else 0)
    (T : Finset (Fin (4*(q+1)))) (hT : T.card=2) (i k : Fin r)
    (hout : ∀ a,a≠i → (∏ j∈T,P a j)= -(∏ j∈T,P i j)) :
    (∑ j,P k j*modularBitSign (normalizeSignCode (show 0<4*(q+1) from Nat.mul_pos (Nat.zero_lt_succ 3) (Nat.succ_pos q)) (flipSignVector T (P i)) j))=
      (if k=i then 4*(q : ℤ) else 0)*flipSignVector T (P i) ⟨0,by omega⟩ := by
  let hN : 0<4*(q+1) := by omega
  let w := flipSignVector T (P i)
  have hw (j : Fin (4*(q+1))) : w j=1 ∨ w j= -1 := flipSignVector_sign T (P i) (hs i) j
  calc
    (∑ j,P k j*modularBitSign (normalizeSignCode hN w j))=
        ∑ j,(P k j*w j)*w ⟨0,hN⟩ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [normalizeSignCode_sign hN w hw j]
      ring
    _=(∑ j,P k j*w j)*w ⟨0,hN⟩ := by rw [Finset.sum_mul]
    _=(if k=i then 4*(q : ℤ) else 0)*w ⟨0,hN⟩ :=
      congrArg (fun z : ℤ => z*w ⟨0,hN⟩) (flip_pair_inner_profile P hs hg T hT i hout k)

theorem column_pair_modular_correction {r q : ℕ} (hr : 4*(q+1)^2<r*q^2)
    (hq : 3≤q) (hodd : q%2=1) (P : Matrix (Fin r) (Fin (4*(q+1))) ℤ)
    (hs : ∀ i j,P i j=1 ∨ P i j= -1)
    (hg : ∀ i k,(∑ j,P i j*P k j)=if i=k then (4*(q+1) : ℤ) else 0) :
    (exactSignCandidates P).card=(modularCandidatesAt q P).card-(columnPairCandidates P).card ∧
      ∃ e : ↥(columnPairCandidates P) ≃ ↥(modularCandidatesAt q P \ exactSignCandidates P),
        ∀ T : columnPairCandidates P,∃ i : Fin r,
          (∀ k,k≠i → (∏ j∈T.val,P k j)= -(∏ j∈T.val,P i j)) ∧
          (e T).val=normalizeSignCode (show 0<4*(q+1) from Nat.mul_pos (Nat.zero_lt_succ 3) (Nat.succ_pos q)) (flipSignVector T.val (P i)) := by
  classical
  have hqp : 0<q := by omega
  have hqZ : (0 : ℤ)<q := by exact_mod_cast hqp
  have hr2 : 2<r := by
    by_contra hn
    have hm := Nat.mul_le_mul_right (q^2) (show r≤2 by omega)
    nlinarith
  let A := columnPairCandidates P
  let B := modularCandidatesAt q P \ exactSignCandidates P
  let row (T : A) : Fin r := Classical.choose
    (((columnPairCandidates_outlier hr2 P hs T.val).mp T.property).2.exists)
  have hrow (T : A) : ∀ k,k≠row T → (∏ j∈T.val,P k j)= -(∏ j∈T.val,P (row T) j) :=
    Classical.choose_spec (((columnPairCandidates_outlier hr2 P hs T.val).mp T.property).2.exists)
  have hTcard (T : A) : T.val.card=2 := ((columnPairCandidates_outlier hr2 P hs T.val).mp T.property).1
  let F (T : A) : B := ⟨normalizeSignCode (show 0<4*(q+1) from Nat.mul_pos (Nat.zero_lt_succ 3) (Nat.succ_pos q)) (flipSignVector T.val (P (row T))),
    Finset.mem_sdiff.mpr (normalized_flip_pair_modular hqp P hs hg T.val (hTcard T) (row T) (hrow T))⟩
  have hNonzero (T : A) : (∑ j,P (row T) j*modularBitSign ((F T).val j))≠0 := by
    have hh := normalized_flip_pair_inner_profile P hs hg T.val (hTcard T) (row T) (row T) (hrow T)
    simp only [eq_self_iff_true,ite_true] at hh
    change (∑ j,P (row T) j*modularBitSign (normalizeSignCode _ (flipSignVector T.val (P (row T))) j))≠0
    rcases flipSignVector_sign T.val (P (row T)) (hs (row T)) (⟨0,by omega⟩ : Fin (4*(q+1))) with h|h <;>
      rw [h] at hh <;> omega
  have hinj : Function.Injective F := by
    intro T U he
    have hcode : normalizeSignCode (show 0<4*(q+1) from Nat.mul_pos (Nat.zero_lt_succ 3) (Nat.succ_pos q)) (flipSignVector T.val (P (row T)))=
        normalizeSignCode (show 0<4*(q+1) from Nat.mul_pos (Nat.zero_lt_succ 3) (Nat.succ_pos q)) (flipSignVector U.val (P (row U))) := congrArg Subtype.val he
    have hxM := (Finset.mem_sdiff.mp (F T).property).1
    have hm := (Finset.mem_filter.mp hxM).2.2
    have hiT := hNonzero T
    have hiU : (∑ j,P (row U) j*modularBitSign ((F T).val j))≠0 := by
      change (∑ j,P (row U) j*modularBitSign (normalizeSignCode _ (flipSignVector T.val (P (row T))) j))≠0
      rw [hcode]
      exact hNonzero U
    have hidx := near_modular_nonzero_unique hr hq hodd P hs hg
      (fun j => modularBitSign ((F T).val j)) (fun j => modularBitSign_sign _) hm (row T) (row U) hiT hiU
    rw [hidx] at hcode
    apply Subtype.ext
    exact normalized_two_flips_injective (by omega : 4<4*(q+1)) (P (row U)) (hs (row U))
      T.val U.val (hTcard T) (hTcard U) hcode
  have hsurj : Function.Surjective F := by
    intro x
    obtain ⟨hxM,hxE⟩ := Finset.mem_sdiff.mp x.property
    obtain ⟨T,i,hT,hout,hx⟩ := near_modular_spurious_pair_exists hr hq hodd P hs hg x.val hxM hxE
    let t : A := ⟨T,hT⟩
    have hi : i=row t := (((columnPairCandidates_outlier hr2 P hs T).mp hT).2).unique hout (hrow t)
    refine ⟨t,Subtype.ext ?_⟩
    change normalizeSignCode (show 0<4*(q+1) from Nat.mul_pos (Nat.zero_lt_succ 3) (Nat.succ_pos q)) (flipSignVector T (P (row t)))=x.val
    rw [← hi]
    exact hx.symm
  let e : A ≃ B := Equiv.ofBijective F ⟨hinj,hsurj⟩
  have hcard : A.card=B.card := by simpa only [Fintype.card_coe] using Fintype.card_congr e
  have hsub : exactSignCandidates P⊆modularCandidatesAt q P := by
    intro x hx
    obtain ⟨hxfirst,hzero⟩ := (Finset.mem_filter.mp hx).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxfirst,fun i => by rw [hzero i]; exact dvd_zero _⟩
  have hle := Finset.card_le_card hsub
  have hcount : (exactSignCandidates P).card=(modularCandidatesAt q P).card-(columnPairCandidates P).card := by
    change (columnPairCandidates P).card=(modularCandidatesAt q P \ exactSignCandidates P).card at hcard
    rw [Finset.card_sdiff_of_subset hsub] at hcard
    omega
  refine ⟨hcount,e,?_⟩
  intro T
  exact ⟨row T,hrow T,rfl⟩


theorem normalized_two_flip_self_nonzero {r q : ℕ} (hq : 0<q)
    (P : Matrix (Fin r) (Fin (4*(q+1))) ℤ) (hs : ∀ i j,P i j=1 ∨ P i j= -1)
    (hg : ∀ i k,(∑ j,P i j*P k j)=if i=k then (4*(q+1) : ℤ) else 0)
    (T : Finset (Fin (4*(q+1)))) (hT : T.card=2) (i : Fin r) :
    (∑ j,P i j*modularBitSign (normalizeSignCode (show 0<4*(q+1) from Nat.mul_pos (Nat.zero_lt_succ 3) (Nat.succ_pos q)) (flipSignVector T (P i)) j))≠0 := by
  let hN : 0<4*(q+1) := by omega
  let w := flipSignVector T (P i)
  have hw (j : Fin (4*(q+1))) : w j=1 ∨ w j= -1 := flipSignVector_sign T (P i) (hs i) j
  have hself : (∑ j,P i j*w j)=4*(q : ℤ) := by
    rw [flipSignVector_inner,hg i i]
    have hsquare (j : Fin (4*(q+1))) : P i j*P i j=1 := by rcases hs i j with h|h <;> simp [h]
    simp [hsquare,hT] <;> ring
  have hinner : (∑ j,P i j*modularBitSign (normalizeSignCode hN w j))=4*(q : ℤ)*w ⟨0,hN⟩ := by
    calc
      (∑ j,P i j*modularBitSign (normalizeSignCode hN w j))=
          ∑ j,(P i j*w j)*w ⟨0,hN⟩ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [normalizeSignCode_sign hN w hw j]
        ring
      _=(∑ j,P i j*w j)*w ⟨0,hN⟩ := by rw [Finset.sum_mul]
      _=4*(q : ℤ)*w ⟨0,hN⟩ := by rw [hself]
  have hqZ : (0 : ℤ)<q := by exact_mod_cast hq
  change (∑ j,P i j*modularBitSign (normalizeSignCode hN w j))≠0
  rcases hw ⟨0,hN⟩ with h|h <;> rw [h] at hinner <;> omega

theorem near_modular_spurious_unique_row {r q : ℕ} (hr : 4*(q+1)^2<r*q^2)
    (hq : 3≤q) (hodd : q%2=1) (P : Matrix (Fin r) (Fin (4*(q+1))) ℤ)
    (hs : ∀ i j,P i j=1 ∨ P i j= -1)
    (hg : ∀ i k,(∑ j,P i j*P k j)=if i=k then (4*(q+1) : ℤ) else 0)
    (x : Fin (4*(q+1)) → Bool) (hx : x∈modularCandidatesAt q P) (hne : x∉exactSignCandidates P) :
    ∃! i : Fin r,∃ T : Finset (Fin (4*(q+1))),T.card=2 ∧
      x=normalizeSignCode (show 0<4*(q+1) from Nat.mul_pos (Nat.zero_lt_succ 3) (Nat.succ_pos q)) (flipSignVector T (P i)) := by
  classical
  obtain ⟨T,i,hT,hout,hxT⟩ := near_modular_spurious_pair_exists hr hq hodd P hs hg x hx hne
  have hT2 : T.card=2 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).2
  refine ⟨i,⟨T,hT2,hxT⟩,?_⟩
  intro k hk
  obtain ⟨U,hU2,hxU⟩ := hk
  have hm := (Finset.mem_filter.mp hx).2.2
  have hqp : 0<q := by omega
  have hi := normalized_two_flip_self_nonzero hqp P hs hg T hT2 i
  have hk := normalized_two_flip_self_nonzero hqp P hs hg U hU2 k
  rw [← hxT] at hi
  rw [← hxU] at hk
  exact near_modular_nonzero_unique hr hq hodd P hs hg
    (fun j => modularBitSign (x j)) (fun j => modularBitSign_sign _) hm k i hk hi

end CompletionTheory
