/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.WeightedCodeGrid
public import Mathlib.FieldTheory.Finiteness
@[expose] public section
set_option maxHeartbeats 2000000
namespace CompletionTheory
open Module Submodule

theorem self_orthogonal_subspace_extends_self_dual {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (C S : Submodule K V) (hC : C=B.orthogonal C) (hS : S≤B.orthogonal S) :
    ∃ D : Submodule K V,D=B.orthogonal D ∧ S≤D := by
  classical
  have aux : ∀ d : ℕ,∀ F : Submodule K V,F=B.orthogonal F →
      finrank K S-finrank K ↥(S ⊓ F)=d →
        ∃ D : Submodule K V,D=B.orthogonal D ∧ S≤D := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro F hF hdefect
      by_cases hSF : S≤F
      · exact ⟨F,hF,hSF⟩
      · obtain ⟨v,hvS,hvF⟩ := SetLike.not_le_iff_exists.mp hSF
        have hvv : B v v=0 := hS hvS v hvS
        let F' := bilinearCodePivot B F v
        have hp := self_dual_bilinear_pivot B hB hnd F hF v hvF hvv
        have hle : S ⊓ F≤S ⊓ F' := by
          intro x hx
          refine ⟨hx.1,Submodule.mem_sup_left ⟨hx.2,?_⟩⟩
          exact hS hx.1 v hvS
        have hvnew : v∈S ⊓ F' := ⟨hvS,hp.2.2.2.2⟩
        have hvold : v∉S ⊓ F := fun hx => hvF hx.2
        have hlt : S ⊓ F<S ⊓ F' := lt_of_le_of_ne hle (by
          intro heq
          exact hvold ((SetLike.ext_iff.mp heq v).mpr hvnew))
        have hrank : finrank K ↥(S ⊓ F)<finrank K ↥(S ⊓ F') :=
          Submodule.finrank_lt_finrank_of_lt hlt
        have hbound : finrank K ↥(S ⊓ F')≤finrank K S :=
          Submodule.finrank_mono inf_le_left
        have hdec : finrank K S-finrank K ↥(S ⊓ F')<d := by omega
        exact ih _ hdec F' hp.1 rfl
  exact aux _ C hC rfl

noncomputable def selfDualQuotientEquiv {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (G : Submodule K V) (hG : G≤B.orthogonal G) :
    {D : Submodule K V // D=B.orthogonal D ∧ G≤D} ≃
      {L : Submodule K ((B.orthogonal G) ⧸ G.comap (B.orthogonal G).subtype) //
        L=(orthogonalQuotientForm B hB G).orthogonal L} where
  toFun D := ⟨orthogonalQuotientCode B D.val G,
    orthogonalQuotientCode_self_dual B hB D.val G D.property.1 D.property.2⟩
  invFun L := ⟨liftOrthogonalQuotientCode B G L.val,by
    have hGD := liftOrthogonalQuotientCode_contains B G hG L.val
    have hDH := liftOrthogonalQuotientCode_le_orthogonal B G L.val
    refine ⟨(quotient_code_self_dual_iff B hB G _ hGD hDH).mp ?_,hGD⟩
    rw [orthogonal_quotient_lift_code]
    exact L.property⟩
  left_inv D := by
    apply Subtype.ext
    apply lift_orthogonal_quotient_code B G D.val D.property.2
    intro x hx y hy
    exact ((SetLike.ext_iff.mp D.property.1 x).mp hx) y (D.property.2 hy)
  right_inv L := by
    apply Subtype.ext
    exact orthogonal_quotient_lift_code B G L.val

theorem self_dual_subspace_same_finrank {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (hnd : B.Nondegenerate)
    (C D : Submodule K V) (hC : C=B.orthogonal C) (hD : D=B.orthogonal D) :
    Module.finrank K C=Module.finrank K D := by
  have hc := B.finrank_add_finrank_orthogonal' C
  have hd := B.finrank_add_finrank_orthogonal' D
  rw [← hC,hnd.ker_eq_bot,inf_bot_eq,finrank_bot,add_zero] at hc
  rw [← hD,hnd.ker_eq_bot,inf_bot_eq,finrank_bot,add_zero] at hd
  omega

def splitGeneratorCount (q : ℕ) : ℕ → ℕ
  | 0 => 1
  | h+1 => (q^h+1)*splitGeneratorCount q h

def selfDualSubspaces {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) := {D : Submodule K V // D=B.orthogonal D}

theorem isotropic_singleton_span {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (v : V) (hvv : B v v=0) :
    K ∙ v≤B.orthogonal (K ∙ v) := by
  intro x hx y hy
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b,rfl⟩ := Submodule.mem_span_singleton.mp hy
  simp [map_smul,LinearMap.smul_apply,smul_eq_mul,hvv]

noncomputable def selfDualContainingVectorQuotientEquiv {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (v : V) (hvv : B v v=0) :
    {D : selfDualSubspaces B // v∈D.val} ≃
      selfDualSubspaces (orthogonalQuotientForm B hB (K ∙ v)) := by
  let e : {D : selfDualSubspaces B // v∈D.val} ≃
      {D : Submodule K V // D=B.orthogonal D ∧ K ∙ v≤D} := {
    toFun := fun D => ⟨D.val.val,D.val.property,(Submodule.span_singleton_le_iff_mem v D.val.val).mpr D.property⟩
    invFun := fun D => ⟨⟨D.val,D.property.1⟩,(Submodule.span_singleton_le_iff_mem v D.val).mp D.property.2⟩
    left_inv := fun D => rfl
    right_inv := fun D => rfl }
  exact e.trans (selfDualQuotientEquiv B hB (K ∙ v) (isotropic_singleton_span B v hvv))

theorem isotropic_point_quotient_has_lagrangian {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (C : Submodule K V) (hC : C=B.orthogonal C) (v : V) (hv : v≠0) (hvv : B v v=0) :
    ∃ L : Submodule K ((B.orthogonal (K ∙ v)) ⧸ (K ∙ v).comap (B.orthogonal (K ∙ v)).subtype),
      L=(orthogonalQuotientForm B hB (K ∙ v)).orthogonal L ∧
        finrank K L=finrank K C-1 := by
  obtain ⟨D,hD,hSD⟩ := self_orthogonal_subspace_extends_self_dual B hB hnd C (K ∙ v) hC
    (isotropic_singleton_span B v hvv)
  let L := orthogonalQuotientCode B D (K ∙ v)
  refine ⟨L,orthogonalQuotientCode_self_dual B hB D (K ∙ v) hD hSD,?_⟩
  have hr := orthogonalQuotientCode_finrank B D (K ∙ v) hD hSD
  have hd := self_dual_subspace_same_finrank B hnd C D hC hD
  rw [finrank_span_singleton hv,← hd] at hr
  change finrank K L+1=finrank K C at hr
  omega

theorem nonzero_finite_type_card (W : Type*) [Zero W] [Finite W] :
    Nat.card {x : W // x≠0}=Nat.card W-1 := by
  classical
  letI : Fintype W := Fintype.ofFinite W
  simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype_eq] using
    (Fintype.card_subtype_compl (fun x : W => x=0))

def nonzeroIsotropicVectors {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) := {x : V // B x x=0 ∧ x≠0}

theorem generator_nonzero_vector_fiber_card {K V : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (D : Submodule K V) (hD : D=B.orthogonal D) :
    Nat.card {v : nonzeroIsotropicVectors B // v.val∈D}=Nat.card K ^ finrank K D-1 := by
  classical
  letI : Fintype D := Fintype.ofEquiv (Fin (finrank K D) → K) (Module.finBasis K D).equivFun.symm.toEquiv
  let e : {v : nonzeroIsotropicVectors B // v.val∈D} ≃ {x : D // x≠0} := {
    toFun := fun v => ⟨⟨v.val.val,v.property⟩,by
      intro hz
      exact v.val.property.2 (congrArg Subtype.val hz)⟩
    invFun := fun x => ⟨⟨x.val.val,by
      exact ((SetLike.ext_iff.mp hD x.val.val).mp x.val.property) x.val.val x.val.property,by
        intro hz
        exact x.property (Subtype.ext hz)⟩,x.val.property⟩
    left_inv := fun v => rfl
    right_inv := fun x => rfl }
  rw [Nat.card_congr e,nonzero_finite_type_card,Module.natCard_eq_pow_finrank (K := K)]

theorem split_generator_incidence_count {K V : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (hnd : B.Nondegenerate)
    (C : Submodule K V) (hC : C=B.orthogonal C) (n : ℕ)
    (hthrough : ∀ v : nonzeroIsotropicVectors B,
      Nat.card {D : selfDualSubspaces B // v.val∈D.val}=n) :
    Nat.card (selfDualSubspaces B)*(Nat.card K ^ finrank K C-1)=
      Nat.card (nonzeroIsotropicVectors B)*n := by
  classical
  letI : Fintype V := Fintype.ofEquiv (Fin (finrank K V) → K) (Module.finBasis K V).equivFun.symm.toEquiv
  letI : Fintype (Submodule K V) := Fintype.ofInjective (fun D => (D : Set V)) SetLike.coe_injective
  let A := selfDualSubspaces B
  let P := nonzeroIsotropicVectors B
  letI : Fintype A := Fintype.ofInjective (fun D : A => D.val) Subtype.val_injective
  letI : Fintype P := Fintype.ofInjective (fun v : P => v.val) Subtype.val_injective
  have hl (D : A) : (Finset.univ.filter (fun v : P => v.val∈D.val)).card=Nat.card K ^ finrank K C-1 := by
    have hh := generator_nonzero_vector_fiber_card B D.val D.property
    rw [← self_dual_subspace_same_finrank B hnd C D.val hC D.property] at hh
    simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype] using hh
  have hr (v : P) : (Finset.univ.filter (fun D : A => v.val∈D.val)).card=n := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype] using hthrough v
  have hh := sum_filter_card_comm (Finset.univ : Finset A) (Finset.univ : Finset P)
    (fun D v => v.val∈D.val)
  simp_rw [hl,hr] at hh
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_eq_nat_card,Nat.cast_id] using hh

end CompletionTheory

namespace CompletionTheory
open Module Submodule Matrix

theorem nonzero_dot_kernel_card {K : Type*} [Field K] [Finite K] {h : ℕ}
    (x : Fin h → K) (hx : x≠0) :
    Nat.card {y : Fin h → K // (∑ i,x i*y i)=0}=Nat.card K ^ (h-1) := by
  classical
  let B := coordinateDotForm K h
  have hi : Function.Injective B := LinearMap.ker_eq_bot.mp (coordinateDotForm_nondegenerate K h).ker_eq_bot
  have hfn : B x≠0 := by
    intro hf
    apply hx
    exact hi (hf.trans B.map_zero.symm)
  have hr := Module.Dual.finrank_ker_add_one_of_ne_zero hfn
  simp only [Module.finrank_pi_fintype,Module.finrank_self,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one,Nat.cast_id] at hr
  have hdim : finrank K (LinearMap.ker (B x))=h-1 := by omega
  change Nat.card ↥(LinearMap.ker (B x))=_
  rw [Module.natCard_eq_pow_finrank (K := K),hdim]

theorem dot_fiber_card {K : Type*} [Field K] [Finite K] [DecidableEq K] {h : ℕ} (x : Fin h → K) :
    Nat.card {y : Fin h → K // (∑ i,x i*y i)=0}=
      if x=0 then Nat.card K ^ h else Nat.card K ^ (h-1) := by
  classical
  by_cases hx : x=0
  · rw [if_pos hx]
    let e : {y : Fin h → K // (∑ i,x i*y i)=0} ≃ (Fin h → K) := {
      toFun := Subtype.val
      invFun := fun y => ⟨y,by simp [hx]⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    rw [Nat.card_congr e,Nat.card_fun,Nat.card_fin]
  · rw [if_neg hx]
    exact nonzero_dot_kernel_card x hx

theorem split_dot_zero_count {K : Type*} [Field K] [Fintype K] (h : ℕ) :
    Nat.card {z : (Fin h → K)×(Fin h → K) // (∑ i,z.1 i*z.2 i)=0}=
      Nat.card K ^ h+(Nat.card K ^ h-1)*Nat.card K ^ (h-1) := by
  classical
  let e : {z : (Fin h → K)×(Fin h → K) // (∑ i,z.1 i*z.2 i)=0} ≃
      Σ x : Fin h → K,{y : Fin h → K // (∑ i,x i*y i)=0} := {
    toFun := fun z => ⟨z.val.1,z.val.2,z.property⟩
    invFun := fun z => ⟨(z.1,z.2.val),z.2.property⟩
    left_inv := fun z => by cases z; rfl
    right_inv := fun z => by cases z; rfl }
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_sigma]
  have hf (x : Fin h → K) : Fintype.card {y : Fin h → K // (∑ i,x i*y i)=0}=
      if x=0 then Nat.card K ^ h else Nat.card K ^ (h-1) := by
    rw [Fintype.card_eq_nat_card]
    exact dot_fiber_card x
  simp_rw [hf]
  rw [Finset.sum_ite]
  have heq : (Finset.univ.filter (fun x : Fin h → K => x=0))={0} := by ext x;simp
  simp [heq,Finset.filter_ne',Finset.card_erase_of_mem,Nat.card_fun,Nat.card_fin,Nat.card_eq_fintype_card]

theorem split_form_isotropic_vector_count {K V : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (htwo : (2 : K)≠0)
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (L : Submodule K V) (hL : L=B.orthogonal L) :
    Nat.card {x : V // B x x=0}=
      Nat.card K ^ finrank K L+(Nat.card K ^ finrank K L-1)*Nat.card K ^ (finrank K L-1) := by
  classical
  let h := finrank K L
  let b := Module.finBasis K L
  obtain ⟨e,he,hLe⟩ := lagrangian_hyperbolic_coordinates htwo B hB hnd L hL b
  have hpred (x : (Fin h → K)×(Fin h → K)) :
      (∑ i,x.1 i*x.2 i)=0 ↔ B (e x) (e x)=0 := by
    rw [he]
    have hh : (∑ i,(x.1 i*x.2 i+x.2 i*x.1 i))=2*(∑ i,x.1 i*x.2 i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hh,mul_eq_zero]
    simp only [htwo,false_or]
  let e' : {z : (Fin h → K)×(Fin h → K) // (∑ i,z.1 i*z.2 i)=0} ≃ {x : V // B x x=0} :=
    e.subtypeEquiv hpred
  rw [← Nat.card_congr e']
  exact split_dot_zero_count h

theorem split_form_nonzero_isotropic_vector_count {K V : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (htwo : (2 : K)≠0)
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (L : Submodule K V) (hL : L=B.orthogonal L) :
    Nat.card {x : V // B x x=0 ∧ x≠0}=
      (Nat.card K ^ finrank K L-1)*(Nat.card K ^ (finrank K L-1)+1) := by
  classical
  letI : Fintype V := Fintype.ofEquiv (Fin (finrank K V) → K) (Module.finBasis K V).equivFun.symm.toEquiv
  let I := {x : V // B x x=0}
  let z : I := ⟨0,by simp⟩
  let e : {x : V // B x x=0 ∧ x≠0} ≃ ↥((Finset.univ : Finset I).erase z) := {
    toFun := fun x => ⟨⟨x.val,x.property.1⟩,Finset.mem_erase.mpr ⟨by
      intro heq
      exact x.property.2 (congrArg Subtype.val heq),Finset.mem_univ _⟩⟩
    invFun := fun x => ⟨x.val.val,x.val.property,by
      intro hz
      exact (Finset.mem_erase.mp x.property).1 (Subtype.ext hz)⟩
    left_inv := fun x => rfl
    right_inv := fun x => rfl }
  have hcard : Nat.card {x : V // B x x=0 ∧ x≠0}=Nat.card I-1 := by
    rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_coe,Finset.card_erase_of_mem (Finset.mem_univ z)]
    simp only [Finset.card_univ,Fintype.card_eq_nat_card]
  rw [hcard]
  change Nat.card {x : V // B x x=0}-1=_
  rw [split_form_isotropic_vector_count htwo B hB hnd L hL]
  have hp : 0<Nat.card K ^ finrank K L := Nat.pow_pos Nat.card_pos
  calc
    _=(Nat.card K ^ finrank K L-1)+(Nat.card K ^ finrank K L-1)*Nat.card K ^ (finrank K L-1) := by omega
    _=_ := by ring

universe u v

theorem split_form_self_dual_subspace_count_aux {K : Type u} [Field K] [Fintype K]
    (htwo : (2 : K)≠0) :
    ∀ h : ℕ,∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
      ∀ (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
        (C : Submodule K V),C=B.orthogonal C → finrank K C=h →
          Nat.card (selfDualSubspaces B)=splitGeneratorCount (Nat.card K) h := by
  intro h
  induction h with
  | zero =>
    intro V instAdd instMod instFinite B hB hnd C hC hdim
    have hbot (D : selfDualSubspaces B) : D.val=⊥ := by
      have hr := self_dual_subspace_same_finrank B hnd C D.val hC D.property
      have hz : finrank K D.val=0 := by omega
      have hh : (⊥ : Submodule K V)=D.val := Submodule.eq_of_le_of_finrank_le bot_le (by rw [hz,finrank_bot])
      exact hh.symm
    letI : Subsingleton (selfDualSubspaces B) := ⟨fun D E => Subtype.ext ((hbot D).trans (hbot E).symm)⟩
    letI : Unique (selfDualSubspaces B) := ⟨⟨C,hC⟩,fun _ => Subsingleton.elim _ _⟩
    simp [splitGeneratorCount]
  | succ h ih =>
    intro V instAdd instMod instFinite B hB hnd C hC hdim
    have hthrough (v : nonzeroIsotropicVectors B) :
        Nat.card {D : selfDualSubspaces B // v.val∈D.val}=splitGeneratorCount (Nat.card K) h := by
      obtain ⟨L,hL,hLdim⟩ := isotropic_point_quotient_has_lagrangian B hB hnd C hC v.val v.property.2 v.property.1
      have hdimL : finrank K L=h := by omega
      rw [Nat.card_congr (selfDualContainingVectorQuotientEquiv B hB v.val v.property.1)]
      exact ih _ (orthogonalQuotientForm B hB (K ∙ v.val))
        (orthogonalQuotientForm_symm B hB (K ∙ v.val))
          (orthogonalQuotientForm_nondegenerate B hB hnd (K ∙ v.val)) L hL hdimL
    have hinc := split_generator_incidence_count B hnd C hC (splitGeneratorCount (Nat.card K) h) hthrough
    have hiso := split_form_nonzero_isotropic_vector_count htwo B hB hnd C hC
    change Nat.card (nonzeroIsotropicVectors B)=_ at hiso
    rw [hiso,hdim] at hinc
    simp only [Nat.add_sub_cancel_right] at hinc
    have hq : 2≤Nat.card K := by rw [← Fintype.card_eq_nat_card];exact Fintype.one_lt_card
    have hpow : 0<Nat.card K ^ h := Nat.pow_pos (by omega)
    have hpow2 : 2≤Nat.card K ^ (h+1) := by rw [Nat.pow_succ];nlinarith
    have hfac : Nat.card K ^ (h+1)-1≠0 := by omega
    change Nat.card (selfDualSubspaces B)=(Nat.card K ^ h+1)*splitGeneratorCount (Nat.card K) h
    apply mul_right_cancel₀ hfac
    calc
      _=((Nat.card K ^ (h+1)-1)*(Nat.card K ^ h+1))*splitGeneratorCount (Nat.card K) h := hinc
      _=_ := by ring

theorem split_form_self_dual_subspace_count {K V : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (htwo : (2 : K)≠0)
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (C : Submodule K V) (hC : C=B.orthogonal C) :
    Nat.card (selfDualSubspaces B)=splitGeneratorCount (Nat.card K) (finrank K C) :=
  split_form_self_dual_subspace_count_aux htwo _ V B hB hnd C hC rfl

theorem splitGeneratorCount_pos (q h : ℕ) : 0<splitGeneratorCount q h := by
  induction h with
  | zero => simp [splitGeneratorCount]
  | succ h ih => exact Nat.mul_pos (Nat.succ_pos _) ih

theorem splitGeneratorCount_product (q h : ℕ) :
    splitGeneratorCount q (h+1)=2*∏ j∈Finset.range h,(q^(j+1)+1) := by
  induction h with
  | zero => simp [splitGeneratorCount]
  | succ h ih =>
    rw [splitGeneratorCount,ih,Finset.prod_range_succ]
    ring

theorem split_form_retained_subspace_count {K V : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (htwo : (2 : K)≠0)
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (C G : Submodule K V) (hC : C=B.orthogonal C) (hG : G≤B.orthogonal G) :
    Nat.card {D : Submodule K V // D=B.orthogonal D ∧ G≤D}=
      splitGeneratorCount (Nat.card K) (finrank K C-finrank K G) := by
  obtain ⟨D,hD,hGD⟩ := self_orthogonal_subspace_extends_self_dual B hB hnd C G hC hG
  let Q := orthogonalQuotientForm B hB G
  let L := orthogonalQuotientCode B D G
  have hL : L=Q.orthogonal L := orthogonalQuotientCode_self_dual B hB D G hD hGD
  have hr := orthogonalQuotientCode_finrank B D G hD hGD
  have hd := self_dual_subspace_same_finrank B hnd C D hC hD
  have hdim : finrank K L=finrank K C-finrank K G := by
    change finrank K L+finrank K G=finrank K D at hr
    omega
  rw [Nat.card_congr (selfDualQuotientEquiv B hB G hG)]
  change Nat.card (selfDualSubspaces Q)=_
  rw [split_form_self_dual_subspace_count htwo Q (orthogonalQuotientForm_symm B hB G)
    (orthogonalQuotientForm_nondegenerate B hB hnd G) L hL,hdim]

theorem non_isotropic_subspace_no_self_dual_extension {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (G : Submodule K V) (hG : ¬G≤B.orthogonal G) :
    Nat.card {D : Submodule K V // D=B.orthogonal D ∧ G≤D}=0 := by
  letI : IsEmpty {D : Submodule K V // D=B.orthogonal D ∧ G≤D} := ⟨by
    intro D
    apply hG
    intro x hx y hy
    exact ((SetLike.ext_iff.mp D.property.1 x).mp (D.property.2 hx)) y (D.property.2 hy)⟩
  simp

theorem splitGeneratorCount_interval_product (q h t : ℕ) :
    splitGeneratorCount q (h+t)=splitGeneratorCount q h*∏ j∈Finset.range t,(q^(h+j)+1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.add_succ,splitGeneratorCount,ih,Finset.prod_range_succ]
    ring

theorem splitGeneratorCount_ratio (q h t : ℕ) :
    (splitGeneratorCount q h : ℝ)/(splitGeneratorCount q (h+t) : ℝ)=
      1/(∏ j∈Finset.range t,((q : ℝ)^(h+j)+1)) := by
  have hL : (splitGeneratorCount q h : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (splitGeneratorCount_pos q h))
  have hd (j : ℕ) : ((q : ℝ)^(h+j)+1)≠0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (pow_nonneg (Nat.cast_nonneg q) _) zero_lt_one)
  have hP : (∏ j∈Finset.range t,((q : ℝ)^(h+j)+1))≠0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hd j)
  rw [splitGeneratorCount_interval_product,Nat.cast_mul,Nat.cast_prod]
  simp only [Nat.cast_add,Nat.cast_pow,Nat.cast_one]
  field_simp [hL,hP]

end CompletionTheory
