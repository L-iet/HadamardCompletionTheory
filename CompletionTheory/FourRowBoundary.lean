/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.ModularRowCorrection
public import Mathlib.Tactic.FinCases
@[expose] public section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory
open Matrix

theorem integer_row_combination_norm {r N : ℕ} (P : Matrix (Fin r) (Fin N) ℤ)
    (hg : ∀ i k,(∑ j,P i j*P k j)=if i=k then (N : ℤ) else 0)
    (c : Fin r → ℤ) :
    (∑ j,(∑ i,c i*P i j)^2)=(N : ℤ)*∑ i,c i^2 := by
  classical
  have he (j : Fin N) : (∑ i,c i*P i j)^2=
      ∑ i,∑ k,(c i*c k)*(P i j*P k j) := by
    rw [pow_two,Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Eq.trans _ (by rw [Finset.mul_sum])
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,hg]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  ring

theorem saturated_four_half_projection {q : ℕ} (P : Matrix (Fin 4) (Fin (4*q)) ℤ)
    (hg : ∀ i k,(∑ j,P i j*P k j)=if i=k then (4*q : ℤ) else 0)
    (v : Fin (4*q) → ℤ) (hv : ∀ j,v j=1 ∨ v j= -1)
    (σ : Fin 4 → ℤ) (hσ : ∀ i,σ i=1 ∨ σ i= -1)
    (hdot : ∀ i,(∑ j,P i j*v j)=2*(q : ℤ)*σ i) :
    ∀ j,2*v j=∑ i,σ i*P i j := by
  classical
  let w := fun j => ∑ i,σ i*P i j
  have hnorm := integer_row_combination_norm P hg σ
  have hσsq (i : Fin 4) : σ i^2=1 := by rcases hσ i with h|h <;> simp [h]
  have hvsq (j : Fin (4*q)) : v j^2=1 := by rcases hv j with h|h <;> simp [h]
  have hcross : (∑ j,v j*w j)=8*(q : ℤ) := by
    simp only [w,Finset.mul_sum]
    rw [Finset.sum_comm]
    have he (i : Fin 4) : (∑ j,v j*(σ i*P i j))=σ i*(∑ j,P i j*v j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp_rw [he,hdot]
    have he2 (i : Fin 4) : σ i*(2*(q : ℤ)*σ i)=2*(q : ℤ) := by nlinarith [hσsq i]
    simp_rw [he2]
    norm_num <;> ring
  have hzero : (∑ j,(2*v j-w j)^2)=0 := by
    have he (j : Fin (4*q)) : (2*v j-w j)^2=4*(v j)^2-4*(v j*w j)+(w j)^2 := by ring
    simp_rw [he]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,hcross]
    change 4*(∑ j,v j^2)-4*(8*(q : ℤ))+(∑ j,(∑ i,σ i*P i j)^2)=0
    rw [hnorm]
    simp only [hvsq,hσsq,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat,mul_one]
    ring
  intro j
  have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (2*v j-w j))).mp hzero j (Finset.mem_univ j)
  change 2*v j=w j
  nlinarith

theorem four_sign_half_iff_closed (f : Fin 4 → ℤ) (hf : ∀ i,f i=1 ∨ f i= -1) (i : Fin 4) :
    ((∑ k,f k)-2*f i=2 ∨ (∑ k,f k)-2*f i= -2) ↔ (∏ k,f k)=1 := by
  classical
  let g : Fin 4 → ℤ := fun k => if k=i then -f k else f k
  have hg (k : Fin 4) : g k=1 ∨ g k= -1 := by
    dsimp [g]
    split_ifs <;> rcases hf k with h|h <;> simp [h]
  have hsum : (∑ k,g k)=(∑ k,f k)-2*f i := by
    have he (k : Fin 4) : g k=f k-(if k=i then 2*f i else 0) := by
      dsimp [g]
      by_cases hki : k=i
      · subst k
        simp only [ite_true]
        ring
      · simp only [if_neg hki,sub_zero]
    simp_rw [he]
    rw [Finset.sum_sub_distrib]
    simp
  have hproduct : (∏ k,g k)= -(∏ k,f k) := by
    have he (k : Fin 4) : g k=(if k=i then (-1 : ℤ) else 1)*f k := by
      dsimp [g]
      split_ifs <;> ring
    simp_rw [he]
    rw [Finset.prod_mul_distrib]
    simp
  have hm := integer_sign_sum_mod_four Finset.univ g (fun k _ => hg k)
  have hp := integer_prod_sign Finset.univ f (fun k _ => hf k)
  have hb := integer_sign_sum_bounds g hg
  simp only [Finset.card_univ,Fintype.card_fin,hsum,hproduct] at hm hb
  constructor
  · intro hh
    rcases hp with hp|hp
    · exact hp
    · rw [hp] at hm
      omega
  · intro hp
    rw [hp] at hm
    omega

def closedFourRows {N : ℕ} (P : Matrix (Fin 4) (Fin N) ℤ) : Prop :=
  ∀ j,(∏ i,P i j)=1

def halfQuadRowCode {N : ℕ} (P : Matrix (Fin 4) (Fin N) ℤ) (i : Fin 4) : Fin N → Bool :=
  fun j => decide ((∑ k,P k j)-2*P i j= -2)

theorem halfQuadRowCode_sign {N : ℕ} (P : Matrix (Fin 4) (Fin N) ℤ)
    (hs : ∀ i j,P i j=1 ∨ P i j= -1) (hclosed : closedFourRows P) (i : Fin 4) (j : Fin N) :
    2*modularBitSign (halfQuadRowCode P i j)=(∑ k,P k j)-2*P i j := by
  have hh := (four_sign_half_iff_closed (fun k => P k j) (fun k => hs k j) i).mpr (hclosed j)
  rcases hh with h|h <;> simp [halfQuadRowCode,modularBitSign,h]

theorem halfQuadRowCode_inner {q : ℕ} (P : Matrix (Fin 4) (Fin (4*q)) ℤ)
    (hs : ∀ i j,P i j=1 ∨ P i j= -1)
    (hg : ∀ i k,(∑ j,P i j*P k j)=if i=k then (4*q : ℤ) else 0)
    (hclosed : closedFourRows P) (i k : Fin 4) :
    (∑ j,P k j*modularBitSign (halfQuadRowCode P i j))=
      if k=i then -(2*(q : ℤ)) else 2*(q : ℤ) := by
  have htwice : 2*(∑ j,P k j*modularBitSign (halfQuadRowCode P i j))=
      (4*(q : ℤ))-2*(if k=i then 4*(q : ℤ) else 0) := by
    rw [Finset.mul_sum]
    have he (j : Fin (4*q)) : 2*(P k j*modularBitSign (halfQuadRowCode P i j))=
        (∑ l,P k j*P l j)-2*(P k j*P i j) := by
      have hh := halfQuadRowCode_sign P hs hclosed i j
      rw [← Finset.mul_sum]
      have hmul := congrArg (fun z : ℤ => P k j*z) hh
      nlinarith
    simp_rw [he]
    rw [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_comm,hg]
    simp_rw [hg]
    simp only [Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  by_cases hki : k=i <;> simp only [hki,ite_true,ite_false] at htwice ⊢ <;> omega


theorem four_sign_sum_two (σ : Fin 4 → ℤ) (hσ : ∀ i,σ i=1 ∨ σ i= -1)
    (hsum : (∑ i,σ i)=2) : ∃ i,∀ k,σ k=if k=i then -1 else 1 := by
  classical
  let T := Finset.univ.filter (fun i => σ i= -1)
  have hcount : (∑ i : Fin 4,if σ i= -1 then (1 : ℤ) else 0)=(T.card : ℤ) := by
    simp only [T,Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.sum_const,nsmul_eq_mul,mul_one]
  have he (i : Fin 4) : σ i=1-2*(if σ i= -1 then (1 : ℤ) else 0) := by
    rcases hσ i with h|h <;> simp [h]
  have hh : (∑ i,σ i)=4-2*(T.card : ℤ) := by
    calc
      (∑ i,σ i)=(∑ i,(1-2*(if σ i= -1 then (1 : ℤ) else 0))) :=
        Finset.sum_congr rfl (fun i _ => he i)
      _=4-2*(T.card : ℤ) := by
        rw [Finset.sum_sub_distrib,← Finset.mul_sum,hcount]
        norm_num
  have hc : T.card=1 := by omega
  obtain ⟨i,hi⟩ := Finset.card_eq_one.mp hc
  refine ⟨i,?_⟩
  intro k
  by_cases hki : k=i
  · subst k
    have hm : i∈T := by rw [hi]; simp
    have hh := (Finset.mem_filter.mp hm).2
    rw [if_pos rfl]
    exact hh
  · have hn : k∉T := by rw [hi]; simp [hki]
    have hkn : σ k≠ -1 := by intro hh; exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩)
    rw [if_neg hki]
    exact (hσ k).resolve_right hkn

theorem modular_four_half_expansion {q : ℕ} (hq : 0<q) (hodd : q%2=1)
    (P : Matrix (Fin 4) (Fin (4*q)) ℤ)
    (hs : ∀ i j,P i j=1 ∨ P i j= -1)
    (hg : ∀ i k,(∑ j,P i j*P k j)=if i=k then (4*q : ℤ) else 0)
    (v : Fin (4*q) → ℤ) (hv : ∀ j,v j=1 ∨ v j= -1)
    (hm : ∀ i,(q : ℤ)∣∑ j,P i j*v j)
    (hhalf : ∃ i,(∑ j,P i j*v j)= -(2*(q : ℤ)) ∨ (∑ j,P i j*v j)=2*(q : ℤ)) :
    ∃ σ : Fin 4 → ℤ,(∀ i,σ i=1 ∨ σ i= -1) ∧
      (∀ i,(∑ j,P i j*v j)=2*(q : ℤ)*σ i) ∧
      ∀ j,2*v j=∑ i,σ i*P i j := by
  classical
  have hprod (i : Fin 4) (j : Fin (4*q)) : P i j*v j=1 ∨ P i j*v j= -1 := by
    rcases hs i j with h|h <;> rcases hv j with g|g <;> simp [h,g]
  have hcommon (i k : Fin 4) : (∑ j,P i j*v j)%4=(∑ j,P k j*v j)%4 := by
    have hi := integer_sign_sum_mod_four Finset.univ (fun j => P i j*v j) (fun j _ => hprod i j)
    have hk := integer_sign_sum_mod_four Finset.univ (fun j => P k j*v j) (fun j _ => hprod k j)
    rw [Finset.prod_mul_distrib] at hi hk
    rw [integer_frame_row_parity P hs hg i k] at hi
    exact hi.trans hk.symm
  obtain ⟨k,hk⟩ := hhalf
  have hoddZ : (q : ℤ)%2=1 := by exact_mod_cast hodd
  have hhalfmod : (2*(q : ℤ))%4=2 ∧ (-(2*(q : ℤ)))%4=2 := by omega
  have hres (i : Fin 4) : (∑ j,P i j*v j)%4=2 := by
    have hh := hcommon i k
    rcases hk with hk|hk <;> rw [hk] at hh <;> omega
  have hvals (i : Fin 4) : (∑ j,P i j*v j)= -(2*(q : ℤ)) ∨ (∑ j,P i j*v j)=2*(q : ℤ) := by
    have hh := modular_sign_sum_values hq hodd _ (hprod i) (hm i)
    have hr := hres i
    rcases hh with hh|hh|hh|hh|hh <;> omega
  let σ : Fin 4 → ℤ := fun i => if (∑ j,P i j*v j)=2*(q : ℤ) then 1 else -1
  have hσ (i : Fin 4) : σ i=1 ∨ σ i= -1 := by dsimp [σ]; split_ifs <;> simp
  have hdot (i : Fin 4) : (∑ j,P i j*v j)=2*(q : ℤ)*σ i := by
    dsimp [σ]
    split_ifs with hi
    · simpa using hi
    · rcases hvals i with hh|hh
      · rw [hh]
        ring
      · exact (hi hh).elim
  exact ⟨σ,hσ,hdot,saturated_four_half_projection P hg v hv σ hσ hdot⟩

theorem normalized_four_half_candidate {q : ℕ} (hq : 0<q) (hodd : q%2=1)
    (P : Matrix (Fin 4) (Fin (4*q)) ℤ)
    (hs : ∀ i j,P i j=1 ∨ P i j= -1)
    (hg : ∀ i k,(∑ j,P i j*P k j)=if i=k then (4*q : ℤ) else 0)
    (hpfirst : ∀ i j,j.val=0 → P i j=1)
    (x : Fin (4*q) → Bool) (hxfirst : positiveFirstBit x)
    (hm : ∀ i,(q : ℤ)∣∑ j,P i j*modularBitSign (x j))
    (hhalf : ∃ i,(∑ j,P i j*modularBitSign (x j))= -(2*(q : ℤ)) ∨
      (∑ j,P i j*modularBitSign (x j))=2*(q : ℤ)) :
    closedFourRows P ∧ ∃ i,x=halfQuadRowCode P i := by
  obtain ⟨σ,hσ,hdot,hprojection⟩ := modular_four_half_expansion hq hodd P hs hg
    (fun j => modularBitSign (x j)) (fun j => modularBitSign_sign _) hm hhalf
  let j0 : Fin (4*q) := ⟨0,by omega⟩
  have hsum : (∑ i,σ i)=2 := by
    have hh := hprojection j0
    have hx0 := hxfirst j0 rfl
    simp only [hpfirst _ j0 rfl,mul_one,hx0,modularBitSign,Bool.false_eq_true,ite_false] at hh
    omega
  obtain ⟨i,hi⟩ := four_sign_sum_two σ hσ hsum
  have he (j : Fin (4*q)) : 2*modularBitSign (x j)=(∑ k,P k j)-2*P i j := by
    rw [hprojection]
    have hh (k : Fin 4) : σ k*P k j=P k j-(if k=i then 2*P i j else 0) := by
      rw [hi]
      by_cases hki : k=i
      · subst k
        simp only [ite_true]
        ring
      · simp only [if_neg hki,one_mul,sub_zero]
    simp_rw [hh]
    rw [Finset.sum_sub_distrib]
    simp
  have hclosed : closedFourRows P := by
    intro j
    apply (four_sign_half_iff_closed (fun k => P k j) (fun k => hs k j) i).mp
    have hej := he j
    rcases modularBitSign_sign (x j) with hx|hx <;> rw [hx] at hej
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  refine ⟨hclosed,i,?_⟩
  funext j
  apply modularBitSign_injective
  have h1 := he j
  have h2 := halfQuadRowCode_sign P hs hclosed i j
  omega


theorem boundary_integer_dot_max {N : ℕ} (u v : Fin N → ℤ)
    (hu : ∀ j,u j=1 ∨ u j= -1) (hv : ∀ j,v j=1 ∨ v j= -1)
    (hdot : (∑ j,u j*v j)=(N : ℤ)) : u=v := by
  have hsq (j : Fin N) : (u j-v j)^2=2-2*(u j*v j) := by
    rcases hu j with h|h <;> rcases hv j with g|g <;> norm_num [h,g]
  have hsum : (∑ j,(u j-v j)^2)=0 := by
    simp_rw [hsq]
    rw [Finset.sum_sub_distrib,← Finset.mul_sum,hdot]
    simp
    ring
  funext j
  have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (u j-v j))).mp hsum j (Finset.mem_univ j)
  nlinarith

theorem normalized_extreme_row_code {r q : ℕ} (hq : 0<q)
    (P : Matrix (Fin r) (Fin (4*q)) ℤ) (hs : ∀ i j,P i j=1 ∨ P i j= -1)
    (hpfirst : ∀ i j,j.val=0 → P i j=1) (x : Fin (4*q) → Bool)
    (hxfirst : positiveFirstBit x) (i : Fin r)
    (hextreme : (∑ j,P i j*modularBitSign (x j))= -(4*(q : ℤ)) ∨
      (∑ j,P i j*modularBitSign (x j))=4*(q : ℤ)) : x=modularRowCode P i := by
  rcases hextreme with hmin|hmax
  · have hvneg (j : Fin (4*q)) : -modularBitSign (x j)=1 ∨ -modularBitSign (x j)= -1 := by
      rcases modularBitSign_sign (x j) with h|h <;> simp [h]
    have hd : (∑ j,P i j*(-modularBitSign (x j)))=((4*q : ℕ) : ℤ) := by
      simp only [mul_neg,Finset.sum_neg_distrib,hmin,neg_neg,Nat.cast_mul,Nat.cast_ofNat]
    have he := boundary_integer_dot_max (P i) (fun j => -modularBitSign (x j)) (hs i) hvneg hd
    let j0 : Fin (4*q) := ⟨0,by omega⟩
    have hh := congrFun he j0
    have hx0 := hxfirst j0 rfl
    norm_num [hpfirst i j0 rfl,hx0,modularBitSign] at hh
  · have hd : (∑ j,P i j*modularBitSign (x j))=((4*q : ℕ) : ℤ) := by
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using hmax
    have he := boundary_integer_dot_max (P i) (fun j => modularBitSign (x j)) (hs i)
      (fun j => modularBitSign_sign _) hd
    funext j
    apply modularBitSign_injective
    rw [modularRowCode_sign P hs]
    exact (congrFun he j).symm

theorem halfQuadRowCode_first {N : ℕ} (P : Matrix (Fin 4) (Fin N) ℤ)
    (hpfirst : ∀ i j,j.val=0 → P i j=1) (i : Fin 4) : positiveFirstBit (halfQuadRowCode P i) := by
  intro j hj
  have hp (k : Fin 4) : P k j=1 := hpfirst k j hj
  simp only [halfQuadRowCode,hp,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  norm_num

theorem halfQuadRowCode_injective {q : ℕ} (hq : 0<q)
    (P : Matrix (Fin 4) (Fin (4*q)) ℤ) (hs : ∀ i j,P i j=1 ∨ P i j= -1)
    (hg : ∀ i k,(∑ j,P i j*P k j)=if i=k then (4*q : ℤ) else 0)
    (hclosed : closedFourRows P) : Function.Injective (halfQuadRowCode P) := by
  intro i k heq
  by_contra hne
  have hi := halfQuadRowCode_inner P hs hg hclosed i i
  have hk := halfQuadRowCode_inner P hs hg hclosed k i
  rw [if_pos rfl] at hi
  rw [if_neg hne] at hk
  rw [heq] at hi
  have hqZ : (0 : ℤ)<q := by exact_mod_cast hq
  omega


noncomputable def closedFourIndicator {N : ℕ} (P : Matrix (Fin 4) (Fin N) ℤ) : ℕ := by
  classical
  exact if closedFourRows P then 1 else 0

theorem normalized_four_row_boundary_count {q : ℕ} (hq : 0<q) (hodd : q%2=1)
    (P : Matrix (Fin 4) (Fin (4*q)) ℤ)
    (hs : ∀ i j,P i j=1 ∨ P i j= -1)
    (hg : ∀ i j,(∑ k,P i k*P j k)=if i=j then (4*q : ℤ) else 0)
    (hfirst : ∀ i j,j.val=0 → P i j=1) :
    (exactSignCandidates P).card=(modularSignCandidates q P).card-4-4*closedFourIndicator P := by
  classical
  let R := Finset.univ.image (modularRowCode P)
  have hqZ : (0 : ℤ)<q := by exact_mod_cast hq
  have hrowfirst (i : Fin 4) : positiveFirstBit (modularRowCode P i) := by
    intro j hj
    simp only [modularRowCode,hfirst i j hj]
    norm_num
  have hrownot (i : Fin 4) : modularRowCode P i∉exactSignCandidates P := by
    intro hh
    have hm := (Finset.mem_filter.mp hh).2.2 i
    simp_rw [modularRowCode_sign P hs] at hm
    have hself := hg i i
    rw [if_pos rfl] at hself
    omega
  have hrowmod (i : Fin 4) : modularRowCode P i∈modularSignCandidates q P := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,hrowfirst i,?_⟩
    intro j
    simp_rw [modularRowCode_sign P hs]
    rw [hg]
    by_cases hji : j=i
    · rw [if_pos hji]
      exact ⟨4,by ring⟩
    · rw [if_neg hji]
      exact dvd_zero _
  have hinj : Function.Injective (modularRowCode P) := by
    intro i j hij
    by_contra hne
    have hsame (k : Fin (4*q)) : P i k=P j k := by
      have hh := congrArg (fun x => modularBitSign (x k)) hij
      simpa only [modularRowCode_sign P hs] using hh
    have hz := hg i j
    rw [if_neg hne] at hz
    simp_rw [← hsame] at hz
    have hn := hg i i
    rw [if_pos rfl] at hn
    omega

  let H := if closedFourRows P then Finset.univ.image (halfQuadRowCode P) else ∅
  have hHmem (x : Fin (4*q) → Bool) (hx : x∈H) : closedFourRows P ∧ ∃ i,x=halfQuadRowCode P i := by
    dsimp [H] at hx
    split_ifs at hx with hc
    · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hx
      exact ⟨hc,i,hi.symm⟩
    · simp at hx
  have hhalfmod (hc : closedFourRows P) (i : Fin 4) : halfQuadRowCode P i∈modularSignCandidates q P := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,halfQuadRowCode_first P hfirst i,?_⟩
    intro k
    rw [halfQuadRowCode_inner P hs hg hc i k]
    by_cases hki : k=i
    · rw [if_pos hki]
      exact ⟨-2,by ring⟩
    · rw [if_neg hki]
      exact ⟨2,by ring⟩
  have hhalfnotE (hc : closedFourRows P) (i : Fin 4) : halfQuadRowCode P i∉exactSignCandidates P := by
    intro hx
    have hz := (Finset.mem_filter.mp hx).2.2 i
    have hi := halfQuadRowCode_inner P hs hg hc i i
    rw [if_pos rfl] at hi
    omega
  have hhalfnotR (hc : closedFourRows P) (i k : Fin 4) : halfQuadRowCode P i≠modularRowCode P k := by
    intro heq
    have hh := halfQuadRowCode_inner P hs hg hc i k
    rw [heq] at hh
    simp_rw [modularRowCode_sign P hs] at hh
    have hself := hg k k
    rw [if_pos rfl] at hself
    by_cases hki : k=i
    · rw [if_pos hki] at hh
      omega
    · rw [if_neg hki] at hh
      omega
  have hunion : modularSignCandidates q P=(exactSignCandidates P∪R)∪H := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxfirst,hm⟩ := (Finset.mem_filter.mp hx).2
      by_cases he : ∀ i,(∑ j,P i j*modularBitSign (x j))=0
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxfirst,he⟩))
      · obtain ⟨i,hi⟩ := not_forall.mp he
        have hsg (j : Fin (4*q)) : P i j*modularBitSign (x j)=1 ∨ P i j*modularBitSign (x j)= -1 := by
          rcases hs i j with h|h <;> rcases modularBitSign_sign (x j) with g|g <;> simp [h,g]
        have hvals := modular_sign_sum_values hq hodd _ hsg (hm i)
        have hrowfinish (hv : (∑ j,P i j*modularBitSign (x j))= -(4*(q : ℤ)) ∨
            (∑ j,P i j*modularBitSign (x j))=4*(q : ℤ)) : x∈(exactSignCandidates P∪R)∪H := by
          have hh := normalized_extreme_row_code hq P hs hfirst x hxfirst i hv
          apply Finset.mem_union_left
          apply Finset.mem_union_right
          exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hh.symm⟩
        have hhalffinish (hv : (∑ j,P i j*modularBitSign (x j))= -(2*(q : ℤ)) ∨
            (∑ j,P i j*modularBitSign (x j))=2*(q : ℤ)) : x∈(exactSignCandidates P∪R)∪H := by
          obtain ⟨hc,k,hx⟩ := normalized_four_half_candidate hq hodd P hs hg hfirst x hxfirst hm ⟨i,hv⟩
          apply Finset.mem_union_right
          dsimp [H]
          rw [if_pos hc]
          exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _,hx.symm⟩
        rcases hvals with hv|hv|hv|hv|hv
        · exact hrowfinish (Or.inl hv)
        · exact hhalffinish (Or.inl hv)
        · exact (hi hv).elim
        · exact hhalffinish (Or.inr hv)
        · exact hrowfinish (Or.inr hv)
    · intro hx
      rcases Finset.mem_union.mp hx with hER|hH
      · rcases Finset.mem_union.mp hER with he|hR
        · obtain ⟨hxfirst,hm⟩ := (Finset.mem_filter.mp he).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxfirst,fun i => by rw [hm i]; exact dvd_zero _⟩
        · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hR
          exact hrowmod i
      · obtain ⟨hc,i,rfl⟩ := hHmem x hH
        exact hhalfmod hc i
  have hdisER : Disjoint (exactSignCandidates P) R := by
    apply Finset.disjoint_left.mpr
    intro x hx hR
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hR
    exact hrownot i hx
  have hdisH : Disjoint (exactSignCandidates P∪R) H := by
    apply Finset.disjoint_left.mpr
    intro x hx hH
    obtain ⟨hc,i,rfl⟩ := hHmem x hH
    rcases Finset.mem_union.mp hx with he|hR
    · exact hhalfnotE hc i he
    · obtain ⟨k,_,hk⟩ := Finset.mem_image.mp hR
      exact hhalfnotR hc i k hk.symm
  have hHcard : H.card=4*closedFourIndicator P := by
    dsimp [H]
    by_cases hc : closedFourRows P
    · rw [if_pos hc,Finset.card_image_of_injective _ (halfQuadRowCode_injective hq P hs hg hc)]
      simp [closedFourIndicator,hc]
    · simp [hc,closedFourIndicator]
  have hcard : (modularSignCandidates q P).card=(exactSignCandidates P).card+4+4*closedFourIndicator P := by
    rw [hunion,Finset.card_union_of_disjoint hdisH,Finset.card_union_of_disjoint hdisER,hHcard]
    dsimp [R]
    rw [Finset.card_image_of_injective _ hinj]
    simp
  omega


def closedSignQuadruple {N : ℕ} (P : Matrix (Fin 4) (Fin N) ℤ) : Prop :=
  ∃ c : ℤ,∀ j,(∏ i,P i j)=c

noncomputable def closedSignQuadrupleIndicator {N : ℕ} (P : Matrix (Fin 4) (Fin N) ℤ) : ℕ := by
  classical
  exact if closedSignQuadruple P then 1 else 0

theorem closed_quadruple_normalization_iff {q : ℕ} (hq : 0<q)
    (P : Matrix (Fin 4) (Fin (4*q)) ℤ) (hs : ∀ i j,P i j=1 ∨ P i j= -1) :
    closedFourRows (normalizeModularRows hq P) ↔ closedSignQuadruple P := by
  let j0 : Fin (4*q) := ⟨0,by omega⟩
  have hp (j : Fin (4*q)) : (∏ i,normalizeModularRows hq P i j)=
      (∏ i,P i j0)*(∏ i,P i j) := by
    change (∏ i,P i j0*P i j)=(∏ i,P i j0)*(∏ i,P i j)
    rw [Finset.prod_mul_distrib]
  have ha := integer_prod_sign Finset.univ (fun i => P i j0) (fun i _ => hs i j0)
  constructor
  · intro hc
    refine ⟨∏ i,P i j0,?_⟩
    intro j
    have hh := hc j
    rw [hp] at hh
    rcases ha with ha|ha <;> rw [ha] at hh ⊢ <;> nlinarith
  · rintro ⟨c,hc⟩
    intro j
    rw [hp,hc j,← hc j0]
    rcases ha with ha|ha <;> rw [ha] <;> norm_num

theorem four_row_boundary_correction {q : ℕ} (hq : 0<q) (hodd : q%2=1)
    (P : Matrix (Fin 4) (Fin (4*q)) ℤ)
    (hs : ∀ i j,P i j=1 ∨ P i j= -1)
    (hg : ∀ i j,(∑ k,P i k*P j k)=if i=j then (4*q : ℤ) else 0) :
    (exactSignCandidates P).card=(modularSignCandidates q P).card-4-4*closedSignQuadrupleIndicator P := by
  classical
  let j0 : Fin (4*q) := ⟨0,by omega⟩
  let Q := normalizeModularRows hq P
  have hQ (i : Fin 4) (j : Fin (4*q)) : Q i j=P i j0*P i j := rfl
  have hsquare (i : Fin 4) : P i j0*P i j0=1 := by
    rcases hs i j0 with hh|hh <;> simp [hh]
  have hsign (i : Fin 4) (j : Fin (4*q)) : Q i j=1 ∨ Q i j= -1 := by
    rw [hQ]
    rcases hs i j0 with hh|hh <;> rcases hs i j with gg|gg <;> simp [hh,gg]
  have hgram (i j : Fin 4) : (∑ k,Q i k*Q j k)=if i=j then (4*q : ℤ) else 0 := by
    have he (k : Fin (4*q)) : Q i k*Q j k=(P i j0*P j j0)*(P i k*P j k) := by
      rw [hQ,hQ]
      ring
    simp_rw [he]
    rw [← Finset.mul_sum,hg]
    by_cases hij : i=j
    · subst j
      rw [if_pos rfl,hsquare,one_mul]
    · rw [if_neg hij,mul_zero]
  have hfirst (i : Fin 4) (j : Fin (4*q)) (hj : j.val=0) : Q i j=1 := by
    have hj0 : j=j0 := Fin.ext hj
    rw [hj0,hQ,hsquare]
  have hmod (i : Fin 4) (x : Fin (4*q) → Bool) :
      ((q : ℤ)∣∑ j,Q i j*modularBitSign (x j)) ↔
      ((q : ℤ)∣∑ j,P i j*modularBitSign (x j)) := by
    simp_rw [hQ,mul_assoc]
    rw [← Finset.mul_sum]
    rcases hs i j0 with hh|hh <;> simp [hh]
  have hex (i : Fin 4) (x : Fin (4*q) → Bool) :
      ((∑ j,Q i j*modularBitSign (x j))=0) ↔
      ((∑ j,P i j*modularBitSign (x j))=0) := by
    simp_rw [hQ,mul_assoc]
    rw [← Finset.mul_sum]
    rcases hs i j0 with hh|hh <;> simp [hh]
  have hM : modularSignCandidates q Q=modularSignCandidates q P := by
    ext x
    simp only [modularSignCandidates,Finset.mem_filter,Finset.mem_univ,true_and]
    exact and_congr_right (fun _ => forall_congr' (fun i => hmod i x))
  have hE : exactSignCandidates Q=exactSignCandidates P := by
    ext x
    simp only [exactSignCandidates,Finset.mem_filter,Finset.mem_univ,true_and]
    exact and_congr_right (fun _ => forall_congr' (fun i => hex i x))

  have hI : closedFourIndicator Q=closedSignQuadrupleIndicator P := by
    have hc := closed_quadruple_normalization_iff hq P hs
    by_cases hclosed : closedSignQuadruple P
    · have hQclosed : closedFourRows Q := hc.mpr hclosed
      simp only [closedFourIndicator,closedSignQuadrupleIndicator,if_pos hclosed,if_pos hQclosed]
    · have hQnot : ¬closedFourRows Q := fun hh => hclosed (hc.mp hh)
      simp only [closedFourIndicator,closedSignQuadrupleIndicator,if_neg hclosed,if_neg hQnot]
  have hh := normalized_four_row_boundary_count hq hodd Q hsign hgram hfirst
  rw [hM,hE,hI] at hh
  exact hh


theorem normalized_four_candidate_decomposition {q : ℕ} (hq : 0<q) (hodd : q%2=1)
    (P : Matrix (Fin 4) (Fin (4*q)) ℤ)
    (hs : ∀ i j,P i j=1 ∨ P i j= -1)
    (hg : ∀ i j,(∑ k,P i k*P j k)=if i=j then (4*q : ℤ) else 0)
    (hfirst : ∀ i j,j.val=0 → P i j=1)
    (x : Fin (4*q) → Bool) (hx : x∈modularSignCandidates q P) :
    x∈exactSignCandidates P ∨ (∃ i,x=modularRowCode P i) ∨
      (closedFourRows P ∧ ∃ i,x=halfQuadRowCode P i) := by
  classical
  obtain ⟨hxfirst,hm⟩ := (Finset.mem_filter.mp hx).2
  by_cases he : ∀ i,(∑ j,P i j*modularBitSign (x j))=0
  · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxfirst,he⟩)
  · obtain ⟨i,hi⟩ := not_forall.mp he
    have hsg (j : Fin (4*q)) : P i j*modularBitSign (x j)=1 ∨ P i j*modularBitSign (x j)= -1 := by
      rcases hs i j with h|h <;> rcases modularBitSign_sign (x j) with g|g <;> simp [h,g]
    have hvals := modular_sign_sum_values hq hodd _ hsg (hm i)
    rcases hvals with hh|hh|hh|hh|hh
    · exact Or.inr (Or.inl ⟨i,normalized_extreme_row_code hq P hs hfirst x hxfirst i (Or.inl hh)⟩)
    · exact Or.inr (Or.inr (normalized_four_half_candidate hq hodd P hs hg hfirst x hxfirst hm ⟨i,Or.inl hh⟩))
    · exact (hi hh).elim
    · exact Or.inr (Or.inr (normalized_four_half_candidate hq hodd P hs hg hfirst x hxfirst hm ⟨i,Or.inr hh⟩))
    · exact Or.inr (Or.inl ⟨i,normalized_extreme_row_code hq P hs hfirst x hxfirst i (Or.inr hh)⟩)

end CompletionTheory
