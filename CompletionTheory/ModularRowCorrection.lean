/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.SignCorrelationRigidity
public import CompletionTheory.CodimensionThree
public import CompletionTheory.ExchangeBudget
public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.Push
@[expose] public section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory
open Matrix
/-- A finite product of integer signs is an integer sign. -/
theorem integer_prod_sign {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hf : ∀ i ∈ s, f i = 1 ∨ f i = -1) :
    (∏ i ∈ s, f i) = 1 ∨ (∏ i ∈ s, f i) = -1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hfa := hf a (Finset.mem_insert_self a s)
      have hfs := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      rw [Finset.prod_insert ha]
      rcases hfa with h | h <;> rcases hfs with h' | h' <;> simp [h, h']

/-- The sum is congruent to cardinality minus one plus product modulo four. -/
theorem integer_sign_sum_mod_four {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hf : ∀ i ∈ s, f i = 1 ∨ f i = -1) :
    (∑ i ∈ s, f i) % 4 = ((s.card : ℤ) - 1 + ∏ i ∈ s, f i) % 4 := by
  classical
  induction s using Finset.induction_on with
  | empty => norm_num
  | @insert a s ha ih =>
      have hfa := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, f i = 1 ∨ f i = -1 :=
        fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hsum := ih hfs
      have hp := integer_prod_sign s f hfs
      rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
      push_cast
      rcases hfa with h | h <;> rcases hp with h' | h' <;>
        simp only [h, h', one_mul, neg_one_mul] at * <;> omega


theorem integer_sign_sum_bounds {ι : Type*} [Fintype ι] (f : ι → ℤ)
    (hf : ∀ i,f i=1 ∨ f i= -1) :
    -(Fintype.card ι : ℤ)≤∑ i,f i ∧ (∑ i,f i)≤(Fintype.card ι : ℤ) := by
  classical
  have hl := Finset.sum_le_sum (s := Finset.univ) (fun i _ => show (-1 : ℤ)≤f i from by rcases hf i with h|h <;> omega)
  have hu := Finset.sum_le_sum (s := Finset.univ) (fun i _ => show f i≤(1 : ℤ) from by rcases hf i with h|h <;> omega)
  simpa using And.intro hl hu

theorem modular_sign_sum_values {q : ℕ} (hq : 0<q) (hodd : q%2=1)
    (f : Fin (4*q) → ℤ) (hf : ∀ i,f i=1 ∨ f i= -1)
    (hdiv : (q : ℤ)∣∑ i,f i) :
    (∑ i,f i)= -(4*q : ℤ) ∨ (∑ i,f i)= -(2*q : ℤ) ∨ (∑ i,f i)=0 ∨
      (∑ i,f i)=(2*q : ℤ) ∨ (∑ i,f i)=(4*q : ℤ) := by
  have hsum := integer_sign_sum_mod_four Finset.univ f (fun i _ => hf i)
  have hprod := integer_prod_sign Finset.univ f (fun i _ => hf i)
  simp only [Finset.card_univ,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] at hsum
  have heven : (∑ i,f i)%2=0 := by rcases hprod with hp|hp <;> rw [hp] at hsum <;> omega
  obtain ⟨z,hz⟩ := hdiv
  have hqZ : (0 : ℤ)<q := by exact_mod_cast hq
  have hqmod : (q : ℤ)%2=1 := by exact_mod_cast hodd
  have hzeven : z%2=0 := by rw [hz,Int.mul_emod,hqmod,one_mul,Int.emod_emod] at heven; exact heven
  obtain ⟨hl,hu⟩ := integer_sign_sum_bounds f hf
  simp only [Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] at hl hu
  rw [hz] at hl hu
  have hzl : -4≤z := by nlinarith
  have hzu : z≤4 := by nlinarith
  have hzvalues : z= -4 ∨ z= -2 ∨ z=0 ∨ z=2 ∨ z=4 := by omega
  rcases hzvalues with hh|hh|hh|hh|hh <;> rw [hz,hh] <;> omega

def modularFrameReal {r N : ℕ} (P : Matrix (Fin r) (Fin N) ℤ) : Matrix (Fin r) (Fin N) ℝ :=
  fun i j => (P i j : ℝ)

theorem integer_frame_partial {r N : ℕ} (P : Matrix (Fin r) (Fin N) ℤ)
    (hs : ∀ i j,P i j=1 ∨ P i j= -1)
    (hg : ∀ i j,(∑ k,P i k*P j k)=if i=j then (N : ℤ) else 0) :
    IsPartialHadamard (modularFrameReal P) := by
  constructor
  · intro i j
    rcases hs i j with hh|hh <;> simp only [modularFrameReal,hh,Int.cast_one,Int.cast_neg,IsSign] <;> tauto
  · ext i j
    have hh := hg i j
    simp only [Matrix.mul_apply,Matrix.transpose_apply,Pi.smul_apply,Matrix.one_apply,Fintype.card_fin,smul_eq_mul,modularFrameReal]
    change (∑ k,(P i k : ℝ)*(P j k : ℝ))=(N : ℝ)*(if i=j then 1 else 0)
    by_cases hij : i=j
    · simp only [if_pos hij] at hh ⊢
      simpa only [mul_one] using (show (∑ k,(P i k : ℝ)*(P j k : ℝ))=(N : ℝ) by exact_mod_cast hh)
    · simp only [if_neg hij,mul_zero] at hh ⊢
      exact_mod_cast hh

theorem integer_frame_row_parity {r q : ℕ} (P : Matrix (Fin r) (Fin (4*q)) ℤ)
    (hs : ∀ i j,P i j=1 ∨ P i j= -1)
    (hg : ∀ i j,(∑ k,P i k*P j k)=if i=j then (4*q : ℤ) else 0)
    (i j : Fin r) : (∏ k,P i k)=(∏ k,P j k) := by
  classical
  by_cases hij : i=j
  · rw [hij]
  have hsign (k : Fin (4*q)) : P i k*P j k=1 ∨ P i k*P j k= -1 := by
    rcases hs i k with hh|hh <;> rcases hs j k with gg|gg <;> simp [hh,gg]
  have hm := integer_sign_sum_mod_four Finset.univ (fun k => P i k*P j k) (fun k _ => hsign k)
  have hp := integer_prod_sign Finset.univ (fun k => P i k*P j k) (fun k _ => hsign k)
  have hz := hg i j
  rw [if_neg hij] at hz
  simp only [Finset.card_univ,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat,hz] at hm
  have hpone : (∏ k,P i k*P j k)=1 := by
    rcases hp with hh|hh
    · exact hh
    · rw [hh] at hm
      omega
  rw [Finset.prod_mul_distrib] at hpone
  have hpi := integer_prod_sign Finset.univ (P i) (fun k _ => hs i k)
  have hpj := integer_prod_sign Finset.univ (P j) (fun k _ => hs j k)
  rcases hpi with hh|hh <;> rcases hpj with gg|gg <;> rw [hh,gg] at hpone ⊢ <;> norm_num at *

theorem modular_five_rows_no_half_inner {r q : ℕ} (hr : 5≤r) (hq : 0<q) (hodd : q%2=1)
    (P : Matrix (Fin r) (Fin (4*q)) ℤ)
    (hs : ∀ i j,P i j=1 ∨ P i j= -1)
    (hg : ∀ i j,(∑ k,P i k*P j k)=if i=j then (4*q : ℤ) else 0)
    (v : Fin (4*q) → ℤ) (hv : ∀ k,v k=1 ∨ v k= -1)
    (hm : ∀ i,(q : ℤ)∣∑ k,P i k*v k) :
    ∀ i,(∑ k,P i k*v k)= -(4*q : ℤ) ∨ (∑ k,P i k*v k)=0 ∨
      (∑ k,P i k*v k)=(4*q : ℤ) := by
  classical
  have hprod (i : Fin r) (k : Fin (4*q)) : P i k*v k=1 ∨ P i k*v k= -1 := by
    rcases hs i k with hh|hh <;> rcases hv k with gg|gg <;> simp [hh,gg]
  have hvalues (i : Fin r) := modular_sign_sum_values hq hodd _ (hprod i) (hm i)
  have hcommon (i j : Fin r) : (∑ k,P i k*v k)%4=(∑ k,P j k*v k)%4 := by
    have hi := integer_sign_sum_mod_four Finset.univ (fun k => P i k*v k) (fun k _ => hprod i k)
    have hj := integer_sign_sum_mod_four Finset.univ (fun k => P j k*v k) (fun k _ => hprod j k)
    rw [Finset.prod_mul_distrib] at hi hj
    rw [integer_frame_row_parity P hs hg i j] at hi
    exact hi.trans hj.symm
  have hqZ : (0 : ℤ)<q := by exact_mod_cast hq
  have hqR : (0 : ℝ)<q := by exact_mod_cast hq
  have hoddZ : (q : ℤ)%2=1 := by exact_mod_cast hodd
  have hhalfmod : (2*(q : ℤ))%4=2 ∧ (-(2*(q : ℤ)))%4=2 := by omega
  have hNmod : (4*(q : ℤ))%4=0 ∧ (-(4*(q : ℤ)))%4=0 := by omega
  have hbad (i : Fin r) (hres : (∑ k,P i k*v k)%4=2) : False := by
    have hall (j : Fin r) : (∑ k,P j k*v k)^2=4*(q : ℤ)^2 := by
      have hc := hcommon j i
      rw [hres] at hc
      rcases hvalues j with hj|hj|hj|hj|hj <;> rw [hj] at hc ⊢ <;> first | nlinarith | omega
    have hpartial := integer_frame_partial P hs hg
    have hgram : modularFrameReal P*(modularFrameReal P)ᵀ=(4*(q : ℝ)) • 1 := by
      simpa only [Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] using hpartial.2
    have hb := rowGram_bessel (modularFrameReal P) (4*(q : ℝ)) (by positivity) hgram (fun k => (v k : ℝ))
    have hnorm (k : Fin (4*q)) : (v k : ℝ)^2=1 := by rcases hv k with hvv|hvv <;> simp [hvv]
    have hinner (j : Fin r) : (∑ k,modularFrameReal P j k*(v k : ℝ))^2=4*(q : ℝ)^2 := by
      have hhR : ((∑ k,P j k*v k : ℤ) : ℝ)^2=4*(q : ℝ)^2 := by exact_mod_cast hall j
      simpa only [Int.cast_sum,Int.cast_mul,modularFrameReal] using hhR
    simp only [hinner,hnorm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat] at hb
    have hrR : (5 : ℝ)≤r := by exact_mod_cast hr
    have hhR := mul_le_mul_of_nonneg_right hrR (show 0≤4*(q : ℝ)^2 by positivity)
    nlinarith [sq_pos_of_pos hqR]
  intro i
  rcases hvalues i with hh|hh|hh|hh|hh
  · exact Or.inl hh
  · exact (hbad i (by rw [hh]; exact hhalfmod.2)).elim
  · exact Or.inr (Or.inl hh)
  · exact (hbad i (by rw [hh]; exact hhalfmod.1)).elim
  · exact Or.inr (Or.inr hh)

theorem modular_five_rows_classification {r q : ℕ} (hr : 5≤r) (hq : 0<q) (hodd : q%2=1)
    (P : Matrix (Fin r) (Fin (4*q)) ℤ)
    (hs : ∀ i j,P i j=1 ∨ P i j= -1)
    (hg : ∀ i j,(∑ k,P i k*P j k)=if i=j then (4*q : ℤ) else 0)
    (v : Fin (4*q) → ℤ) (hv : ∀ k,v k=1 ∨ v k= -1)
    (hm : ∀ i,(q : ℤ)∣∑ k,P i k*v k) :
    (∀ i,(∑ k,P i k*v k)=0) ∨ ∃ i,v=P i ∨ v= -P i := by
  classical
  by_cases he : ∀ i,(∑ k,P i k*v k)=0
  · exact Or.inl he
  · right
    obtain ⟨i,hi⟩ := not_forall.mp he
    have hvals := modular_five_rows_no_half_inner hr hq hodd P hs hg v hv hm i
    have hPi : IsCubeVector (fun k => (P i k : ℝ)) := by
      intro k
      rcases hs i k with hh|hh <;> simp [hh,IsSign]
    have hvR : IsCubeVector (fun k => (v k : ℝ)) := by
      intro k
      rcases hv k with hh|hh <;> simp [hh,IsSign]
    have habs : |∑ k,(P i k : ℝ)*(v k : ℝ)|=(Fintype.card (Fin (4*q)) : ℝ) := by
      have hqR : (0 : ℝ)≤q := by positivity
      rcases hvals with hh|hh|hh
      · have hhR : (∑ k,(P i k : ℝ)*(v k : ℝ))= -(4*(q : ℝ)) := by exact_mod_cast hh
        rw [hhR,abs_neg,abs_of_nonneg (by positivity)]
        simp
      · exact (hi hh).elim
      · have hhR : (∑ k,(P i k : ℝ)*(v k : ℝ))=4*(q : ℝ) := by exact_mod_cast hh
        rw [hhR,abs_of_nonneg (by positivity)]
        simp
    have hh := cube_abs_dot_eq_card_rigid (fun k => (P i k : ℝ)) (fun k => (v k : ℝ)) hPi hvR habs
    refine ⟨i,?_⟩
    rcases hh with hh|hh
    · left
      funext k
      have hk := congrFun hh k
      exact_mod_cast hk
    · right
      funext k
      have hk := congrFun hh k
      change (v k : ℝ)= -(P i k : ℝ) at hk
      exact_mod_cast hk

def modularBitSign (b : Bool) : ℤ := if b then -1 else 1

def modularRowCode {r N : ℕ} (P : Matrix (Fin r) (Fin N) ℤ) (i : Fin r) : Fin N → Bool :=
  fun j => decide (P i j= -1)

def positiveFirstBit {N : ℕ} (x : Fin N → Bool) : Prop := ∀ j,j.val=0 → x j=false

noncomputable def modularSignCandidates {r : ℕ} (q : ℕ) (P : Matrix (Fin r) (Fin (4*q)) ℤ) :
    Finset (Fin (4*q) → Bool) := by
  classical
  exact Finset.univ.filter (fun x => positiveFirstBit x ∧
      ∀ i,(q : ℤ)∣∑ j,P i j*modularBitSign (x j))

noncomputable def exactSignCandidates {r N : ℕ} (P : Matrix (Fin r) (Fin N) ℤ) :
    Finset (Fin N → Bool) := by
  classical
  exact Finset.univ.filter (fun x => positiveFirstBit x ∧
      ∀ i,(∑ j,P i j*modularBitSign (x j))=0)

theorem modularBitSign_sign (b : Bool) : modularBitSign b=1 ∨ modularBitSign b= -1 := by
  cases b <;> simp [modularBitSign]

theorem modularBitSign_injective : Function.Injective modularBitSign := by
  intro a b h
  cases a <;> cases b <;> simp_all [modularBitSign]

theorem modularRowCode_sign {r N : ℕ} (P : Matrix (Fin r) (Fin N) ℤ)
    (hs : ∀ i j,P i j=1 ∨ P i j= -1) (i : Fin r) (j : Fin N) :
    modularBitSign (modularRowCode P i j)=P i j := by
  rcases hs i j with hh|hh <;> simp [modularRowCode,modularBitSign,hh]


theorem modular_five_row_count {r q : ℕ} (hr : 5≤r) (hq : 0<q) (hodd : q%2=1)
    (P : Matrix (Fin r) (Fin (4*q)) ℤ)
    (hs : ∀ i j,P i j=1 ∨ P i j= -1)
    (hg : ∀ i j,(∑ k,P i k*P j k)=if i=j then (4*q : ℤ) else 0)
    (hfirst : ∀ i j,j.val=0 → P i j=1) :
    (exactSignCandidates P).card=(modularSignCandidates q P).card-r ∧
      ∀ x∈modularSignCandidates q P,x∉exactSignCandidates P ↔
        ∃! i : Fin r,x=modularRowCode P i := by
  classical
  let R := Finset.univ.image (modularRowCode P)
  have hqZ : (0 : ℤ)<q := by exact_mod_cast hq
  have hrowfirst (i : Fin r) : positiveFirstBit (modularRowCode P i) := by
    intro j hj
    simp only [modularRowCode,hfirst i j hj]
    norm_num
  have hrownot (i : Fin r) : modularRowCode P i∉exactSignCandidates P := by
    intro hh
    have hm := (Finset.mem_filter.mp hh).2.2 i
    simp_rw [modularRowCode_sign P hs] at hm
    have hself := hg i i
    rw [if_pos rfl] at hself
    omega
  have hrowmod (i : Fin r) : modularRowCode P i∈modularSignCandidates q P := by
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
  have hunion : modularSignCandidates q P=exactSignCandidates P∪R := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxfirst,hm⟩ := (Finset.mem_filter.mp hx).2
      have hh := modular_five_rows_classification hr hq hodd P hs hg
        (fun j => modularBitSign (x j)) (fun j => modularBitSign_sign (x j)) hm
      rcases hh with he|⟨i,hi|hi⟩
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxfirst,he⟩)
      · apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨i,Finset.mem_univ _,?_⟩
        funext j
        apply modularBitSign_injective
        rw [modularRowCode_sign P hs]
        exact (congrFun hi j).symm
      · let j : Fin (4*q) := ⟨0,by omega⟩
        have hj : x j=false := hxfirst j rfl
        have hp : P i j=1 := hfirst i j rfl
        have hh := congrFun hi j
        change modularBitSign (x j)= -P i j at hh
        norm_num [hj,hp,modularBitSign] at hh
    · intro hx
      rcases Finset.mem_union.mp hx with he|hR
      · obtain ⟨hxfirst,hm⟩ := (Finset.mem_filter.mp he).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxfirst,fun i => by rw [hm i]; exact dvd_zero _⟩
      · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hR
        exact hrowmod i
  have hdis : Disjoint (exactSignCandidates P) R := by
    apply Finset.disjoint_left.mpr
    intro x hx hR
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hR
    exact hrownot i hx
  have hcount : (modularSignCandidates q P).card=(exactSignCandidates P).card+r := by
    rw [hunion,Finset.card_union_of_disjoint hdis]
    dsimp [R]
    rw [Finset.card_image_of_injective _ hinj]
    simp
  refine ⟨by omega,?_⟩
  intro x hx
  constructor
  · intro hn
    rw [hunion] at hx
    have hxR : x∈R := (Finset.mem_union.mp hx).resolve_left hn
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hxR
    refine ⟨i,hi.symm,?_⟩
    intro j hj
    apply hinj
    exact hj.symm.trans hi.symm
  · rintro ⟨i,hi,_⟩
    rw [hi]
    exact hrownot i


def normalizeModularRows {r q : ℕ} (hq : 0<q)
    (P : Matrix (Fin r) (Fin (4*q)) ℤ) : Matrix (Fin r) (Fin (4*q)) ℤ :=
  fun i j => P i ⟨0,by omega⟩*P i j

theorem modular_row_correction {r q : ℕ} (hr : 5≤r) (hq : 0<q) (hodd : q%2=1)
    (P : Matrix (Fin r) (Fin (4*q)) ℤ)
    (hs : ∀ i j,P i j=1 ∨ P i j= -1)
    (hg : ∀ i j,(∑ k,P i k*P j k)=if i=j then (4*q : ℤ) else 0) :
    (exactSignCandidates P).card=(modularSignCandidates q P).card-r ∧
      ∀ x∈modularSignCandidates q P,x∉exactSignCandidates P ↔
        ∃! i : Fin r,x=modularRowCode (normalizeModularRows hq P) i := by
  classical
  let j0 : Fin (4*q) := ⟨0,by omega⟩
  let Q := normalizeModularRows hq P
  have hQ (i : Fin r) (j : Fin (4*q)) : Q i j=P i j0*P i j := rfl
  have hsquare (i : Fin r) : P i j0*P i j0=1 := by
    rcases hs i j0 with hh|hh <;> simp [hh]
  have hsign (i : Fin r) (j : Fin (4*q)) : Q i j=1 ∨ Q i j= -1 := by
    rw [hQ]
    rcases hs i j0 with hh|hh <;> rcases hs i j with gg|gg <;> simp [hh,gg]
  have hgram (i j : Fin r) : (∑ k,Q i k*Q j k)=if i=j then (4*q : ℤ) else 0 := by
    have he (k : Fin (4*q)) : Q i k*Q j k=(P i j0*P j j0)*(P i k*P j k) := by
      rw [hQ,hQ]
      ring
    simp_rw [he]
    rw [← Finset.mul_sum,hg]
    by_cases hij : i=j
    · subst j
      rw [if_pos rfl,hsquare,one_mul]
    · rw [if_neg hij,mul_zero]
  have hfirst (i : Fin r) (j : Fin (4*q)) (hj : j.val=0) : Q i j=1 := by
    have hj0 : j=j0 := Fin.ext hj
    rw [hj0,hQ,hsquare]
  have hmod (i : Fin r) (x : Fin (4*q) → Bool) :
      ((q : ℤ)∣∑ j,Q i j*modularBitSign (x j)) ↔
      ((q : ℤ)∣∑ j,P i j*modularBitSign (x j)) := by
    simp_rw [hQ,mul_assoc]
    rw [← Finset.mul_sum]
    rcases hs i j0 with hh|hh <;> simp [hh]
  have hex (i : Fin r) (x : Fin (4*q) → Bool) :
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
  have hh := modular_five_row_count hr hq hodd Q hsign hgram hfirst
  rw [hM,hE] at hh
  exact hh

end CompletionTheory
