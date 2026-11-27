/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.CodeNeighbors
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.FieldTheory.Finiteness
@[expose] public section
set_option maxHeartbeats 2000000
namespace CompletionTheory
open Module Submodule

def linearHyperplanes (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :=
  {H : Submodule K V // finrank K H+1=finrank K V}

noncomputable def projectiveDualHyperplane {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (x : Projectivization K (Module.Dual K V)) :
    linearHyperplanes K V :=
  ⟨LinearMap.ker x.rep,Module.Dual.finrank_ker_add_one_of_ne_zero x.rep_nonzero⟩

theorem projectiveDualHyperplane_bijective {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] :
    Function.Bijective (projectiveDualHyperplane (K := K) (V := V)) := by
  constructor
  · intro x y hxy
    have hk : LinearMap.ker x.rep=LinearMap.ker y.rep := congrArg Subtype.val hxy
    obtain ⟨a,ha,hrep⟩ := (nonzero_functionals_same_kernel x.rep y.rep x.rep_nonzero y.rep_nonzero).mp hk
    have hh : Projectivization.mk K y.rep y.rep_nonzero=Projectivization.mk K x.rep x.rep_nonzero :=
      (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨a,hrep.symm⟩
    simpa only [Projectivization.mk_rep] using hh.symm
  · intro H
    have hlt : H.val<⊤ := by
      apply lt_of_le_of_ne le_top
      intro heq
      have hh := H.property
      rw [heq,finrank_top] at hh
      omega
    obtain ⟨f,hf,hle⟩ := H.val.exists_le_ker_of_lt_top hlt
    have heq : H.val=LinearMap.ker f := by
      apply Submodule.eq_of_le_of_finrank_le hle
      have hh := Module.Dual.finrank_ker_add_one_of_ne_zero hf
      have hH := H.property
      omega
    refine ⟨Projectivization.mk K f hf,?_⟩
    apply Subtype.ext
    change LinearMap.ker (Projectivization.mk K f hf).rep=H.val
    have hr := Projectivization.mk_rep (Projectivization.mk K f hf)
    have hs := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp hr
    obtain ⟨a,ha⟩ := hs
    have ha0 : a≠0 := by
      intro hz
      have hbad := (Projectivization.mk K f hf).rep_nonzero
      rw [hz,zero_smul] at ha
      exact hbad ha.symm
    have hk := (nonzero_functionals_same_kernel f _ hf (Projectivization.mk K f hf).rep_nonzero).mpr
      ⟨a,ha0,ha.symm⟩
    exact hk.symm.trans heq.symm

theorem finite_hyperplane_count {K V : Type*} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] :
    Nat.card (linearHyperplanes K V)=(Nat.card K ^ finrank K V-1)/(Nat.card K-1) := by
  have heq := Nat.card_congr (Equiv.ofBijective projectiveDualHyperplane
    (projectiveDualHyperplane_bijective (K := K) (V := V)))
  rw [← heq,Projectivization.card'']
  congr 2
  rw [Module.natCard_eq_pow_finrank (K := K),Subspace.dual_finrank_eq]

theorem submodule_quotient_image_finrank {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (G H : Submodule K V) (hGH : G≤H) :
    finrank K (H.map G.mkQ)+finrank K G=finrank K H := by
  let f := G.mkQ.domRestrict H
  have hmap : (LinearMap.ker f).map H.subtype=G := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      change G.mkQ y.val=0 at hy
      exact (Submodule.Quotient.mk_eq_zero G).mp hy
    · intro hx
      refine ⟨⟨x,hGH hx⟩,?_,rfl⟩
      change G.mkQ x=0
      exact (Submodule.Quotient.mk_eq_zero G).mpr hx
  have hh := LinearMap.finrank_range_add_finrank_ker f
  rw [← Submodule.finrank_map_subtype_eq H (LinearMap.ker f),hmap] at hh
  have hr : LinearMap.range f=H.map G.mkQ := LinearMap.range_domRestrict _ _
  rw [hr] at hh
  exact hh

def linearHyperplanesOver {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (G : Submodule K V) :=
  {H : Submodule K V // G≤H ∧ finrank K H+1=finrank K V}

noncomputable def quotientHyperplaneEquiv {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (G : Submodule K V) :
    linearHyperplanes K (V ⧸ G) ≃ linearHyperplanesOver G where
  toFun H := ⟨H.val.comap G.mkQ,Submodule.le_comap_mkQ G H.val,by
    have h1 := submodule_quotient_image_finrank G (H.val.comap G.mkQ)
      (Submodule.le_comap_mkQ G H.val)
    have hmap : (H.val.comap G.mkQ).map G.mkQ=H.val :=
      Submodule.map_comap_eq_self (by simp)
    rw [hmap] at h1
    have h2 := G.finrank_quotient_add_finrank
    have h3 := H.property
    omega⟩
  invFun H := ⟨H.val.map G.mkQ,by
    have h1 := submodule_quotient_image_finrank G H.val H.property.1
    have h2 := G.finrank_quotient_add_finrank
    have h3 := H.property.2
    omega⟩
  left_inv H := by
    apply Subtype.ext
    exact Submodule.map_comap_eq_self (by simp)
  right_inv H := by
    apply Subtype.ext
    simpa only [Submodule.comap_map_mkQ,sup_eq_right.mpr H.property.1]

theorem finite_restricted_hyperplane_count {K V : Type*} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (G : Submodule K V) :
    Nat.card (linearHyperplanesOver G)=
      (Nat.card K ^ (finrank K V-finrank K G)-1)/(Nat.card K-1) := by
  rw [← Nat.card_congr (quotientHyperplaneEquiv G),finite_hyperplane_count]
  have hh := G.finrank_quotient_add_finrank
  congr 3
  omega

noncomputable def hyperplaneContainingVectorEquiv {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (G : Submodule K V) (v : V) :
    {H : linearHyperplanesOver G // v∈H.val} ≃ linearHyperplanesOver (G ⊔ K ∙ v) where
  toFun H := ⟨H.val.val,⟨sup_le H.val.property.1
    ((Submodule.span_singleton_le_iff_mem _ _).mpr H.property),H.val.property.2⟩⟩
  invFun H := ⟨⟨H.val,⟨le_trans le_sup_left H.property.1,H.property.2⟩⟩,
    H.property.1 (Submodule.mem_sup_right (Submodule.mem_span_singleton.mpr ⟨1,one_smul _ _⟩))⟩
  left_inv H := rfl
  right_inv H := rfl

theorem finite_hyperplanes_missing_vector {K V : Type*} [Field K] [Fintype K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Fintype V]
    (G : Submodule K V) (v : V) (hv : v∉G) :
    Nat.card {H : linearHyperplanesOver G // v∉H.val}=
      Nat.card K ^ (finrank K V-finrank K G-1) := by
  classical
  letI : Fintype (Submodule K V) :=
    Fintype.ofInjective (fun E => (E : Set V)) SetLike.coe_injective
  letI : Fintype (linearHyperplanesOver G) :=
    Fintype.ofInjective (fun H => H.val) Subtype.val_injective
  have hsplit : Nat.card {H : linearHyperplanesOver G // v∉H.val}=
      Nat.card (linearHyperplanesOver G)-Nat.card {H : linearHyperplanesOver G // v∈H.val} := by
    simpa only [Fintype.card_eq_nat_card] using
      (Fintype.card_subtype_compl (fun H : linearHyperplanesOver G => v∈H.val))
  rw [hsplit,Nat.card_congr (hyperplaneContainingVectorEquiv G v),
    finite_restricted_hyperplane_count,finite_restricted_hyperplane_count]
  have hv0 : v≠0 := by intro hz;exact hv (hz ▸ G.zero_mem)
  have hinf : G ⊓ K ∙ v=⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hx.2
    by_cases ha0 : a=0
    · simpa [ha0] using ha.symm
    · have hh := G.smul_mem a⁻¹ (ha.symm ▸ hx.1)
      have hvG : v∈G := by simpa [smul_smul,inv_mul_cancel₀ ha0] using hh
      exact (hv hvG).elim
  have hsup : finrank K ↥(G ⊔ K ∙ v)=finrank K G+1 := by
    have hh := Submodule.finrank_sup_add_finrank_inf_eq G (K ∙ v)
    rw [hinf,finrank_bot,add_zero,finrank_span_singleton hv0] at hh
    exact hh
  have hle : finrank K G+1≤finrank K V := by
    have hh := Submodule.finrank_le (G ⊔ K ∙ v)
    rwa [hsup] at hh
  have hq : 2≤Nat.card K := by
    rw [← Fintype.card_eq_nat_card]
    exact Fintype.one_lt_card
  rw [hsup,← Nat.geomSum_eq hq,← Nat.geomSum_eq hq]
  have hd : finrank K V-finrank K G=(finrank K V-finrank K G-1)+1 := by omega
  have hd' : finrank K V-(finrank K G+1)=finrank K V-finrank K G-1 := by omega
  rw [hd',hd,Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel_right,Nat.add_sub_cancel_left]

theorem ambient_submodule_map_comap {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (C H : Submodule K V) (hHC : H≤C) :
    (H.comap C.subtype).map C.subtype=H := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x,hHC hx⟩,hx,rfl⟩

noncomputable def neighborIntersectionHyperplane {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (C : Submodule K V)
    (D : {D : Submodule K V // IsBilinearCodeNeighbor B C D}) : linearHyperplanes K C :=
  ⟨(C ⊓ D.val).comap C.subtype,by
    have hh := Submodule.finrank_map_subtype_eq C ((C ⊓ D.val).comap C.subtype)
    rw [ambient_submodule_map_comap C (C ⊓ D.val) inf_le_left] at hh
    rw [← hh]
    exact D.property.2.2⟩

theorem neighborIntersectionHyperplane_bijective {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (htwo : (2 : K)≠0)
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (C : Submodule K V) (hC : C=B.orthogonal C) :
    Function.Bijective (neighborIntersectionHyperplane B C) := by
  have same (D : {D : Submodule K V // IsBilinearCodeNeighbor B C D}) :
      ((neighborIntersectionHyperplane B C D).val).map C.subtype=C ⊓ D.val :=
    ambient_submodule_map_comap C _ inf_le_left
  constructor
  · intro D E hDE
    have hi : C ⊓ D.val=C ⊓ E.val := by
      rw [← same D,← same E,hDE]
    have hle : C ⊓ D.val≤C := inf_le_left
    obtain ⟨F,hF,hne,hCF,hpool,hunique⟩ := hyperplane_two_self_dual_spaces htwo B hB hnd C
      (C ⊓ D.val) hC hle D.property.2.2
    have hD := hunique D.val D.property.1 inf_le_right D.property.2.1
    have hE := hunique E.val E.property.1 (hi ▸ inf_le_right) E.property.2.1
    exact Subtype.ext (hD.trans hE.symm)
  · intro H
    let A := H.val.map C.subtype
    have hAC : A≤C := by
      rintro x ⟨y,hy,rfl⟩
      exact y.property
    have hdim : finrank K A+1=finrank K C := by
      rw [Submodule.finrank_map_subtype_eq]
      exact H.property
    obtain ⟨D,hD,hne,hCD,hpool,hunique⟩ := hyperplane_two_self_dual_spaces htwo B hB hnd C A hC hAC hdim
    refine ⟨⟨D,hD,hne,?_⟩,?_⟩
    · rw [hCD]
      exact hdim
    · apply Subtype.ext
      change (C ⊓ D).comap C.subtype=H.val
      rw [hCD]
      ext x
      constructor
      · rintro ⟨y,hy,heq⟩
        have hx : y=x := Subtype.ext heq
        exact hx ▸ hy
      · intro hx
        exact ⟨x,hx,rfl⟩

theorem finite_restricted_neighbor_count {K V : Type*} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (htwo : (2 : K)≠0)
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (C G : Submodule K V) (hC : C=B.orthogonal C) (hGC : G≤C) :
    Nat.card {D : Submodule K V // IsBilinearCodeNeighbor B C D ∧ G≤D}=
      (Nat.card K ^ (finrank K C-finrank K G)-1)/(Nat.card K-1) := by
  let A := G.comap C.subtype
  let f : {D : Submodule K V // IsBilinearCodeNeighbor B C D ∧ G≤D} → linearHyperplanesOver A :=
    fun D => ⟨(neighborIntersectionHyperplane B C ⟨D.val,D.property.1⟩).val,⟨by
      intro x hx
      exact ⟨x.property,D.property.2 hx⟩,
      (neighborIntersectionHyperplane B C ⟨D.val,D.property.1⟩).property⟩⟩
  have hb := neighborIntersectionHyperplane_bijective htwo B hB hnd C hC
  have hfb : Function.Bijective f := by
    constructor
    · intro D E hDE
      have hH : neighborIntersectionHyperplane B C ⟨D.val,D.property.1⟩=
          neighborIntersectionHyperplane B C ⟨E.val,E.property.1⟩ :=
        Subtype.ext (congrArg (fun H : linearHyperplanesOver A => H.val) hDE)
      exact Subtype.ext (congrArg
        (fun D : {D : Submodule K V // IsBilinearCodeNeighbor B C D} => D.val) (hb.1 hH))
    · intro H
      obtain ⟨D,hD⟩ := hb.2 ⟨H.val,H.property.2⟩
      have hGD : G≤D.val := by
        intro x hx
        have hxA : (⟨x,hGC hx⟩ : C)∈A := hx
        have hxH := H.property.1 hxA
        have heq := congrArg Subtype.val hD
        rw [← heq] at hxH
        exact hxH.2
      refine ⟨⟨D.val,D.property,hGD⟩,?_⟩
      exact Subtype.ext (congrArg (fun H : linearHyperplanes K C => H.val) hD)
  have hcard := Nat.card_congr (Equiv.ofBijective f hfb)
  rw [hcard,finite_restricted_hyperplane_count]
  have hr := Submodule.finrank_map_subtype_eq C A
  rw [ambient_submodule_map_comap C G hGC] at hr
  rw [← hr]

noncomputable def restrictedCodeNeighbors {p : ℕ} [Fact p.Prime]
    (C G : Submodule (ZMod p) (Fin (4*p) → ZMod p)) :
    Finset (Submodule (ZMod p) (Fin (4*p) → ZMod p)) := by
  classical
  exact (selfDualCodeNeighbors C).filter (fun D => G≤D)

theorem restrictedCodeNeighbors_card {p : ℕ} [Fact p.Prime] (hodd : p%2=1)
    (C G : Submodule (ZMod p) (Fin (4*p) → ZMod p))
    (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C) (hGC : G≤C) :
    (restrictedCodeNeighbors C G).card=
      (p ^ (finrank (ZMod p) C-finrank (ZMod p) G)-1)/(p-1) := by
  classical
  have hp : p.Prime := Fact.out
  have htwo : (2 : ZMod p)≠0 := by
    intro hz
    have hd : p∣2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have hp2 : p=2 := (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left hp.ne_one
    omega
  let S := restrictedCodeNeighbors C G
  let e : S ≃ {D : Submodule (ZMod p) (Fin (4*p) → ZMod p) //
      IsBilinearCodeNeighbor (coordinateDotForm (ZMod p) (4*p)) C D ∧ G≤D} := {
    toFun := fun D => ⟨D.val,(Finset.mem_filter.mp (Finset.mem_filter.mp D.property).1).2,
      (Finset.mem_filter.mp D.property).2⟩
    invFun := fun D => ⟨D.val,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,D.property.1⟩,D.property.2⟩⟩
    left_inv := fun D => rfl
    right_inv := fun D => rfl }
  have hleft : Nat.card S=S.card := by rw [Nat.card_eq_fintype_card,Fintype.card_coe]
  change S.card = _
  rw [← hleft,Nat.card_congr e]
  simpa only [Nat.card_zmod] using finite_restricted_neighbor_count htwo
    (coordinateDotForm (ZMod p) (4*p)) (coordinateDotForm_symm _ _)
      (coordinateDotForm_nondegenerate _ _) C G hC hGC

theorem restricted_neighbor_new_sign_census {p : ℕ} [Fact p.Prime] (hodd : p%2=1)
    (C G : Submodule (ZMod p) (Fin (4*p) → ZMod p))
    (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C) (hGC : G≤C) :
    (∑ D∈restrictedCodeNeighbors C G,(codeSignCandidates D \ codeSignCandidates C).card)=
      (codeSignCandidates ((coordinateDotForm (ZMod p) (4*p)).orthogonal G) \ codeSignCandidates C).card := by
  classical
  let B := coordinateDotForm (ZMod p) (4*p)
  let s := restrictedCodeNeighbors C G
  let t := fun D : Submodule (ZMod p) (Fin (4*p) → ZMod p) => codeSignCandidates D \ codeSignCandidates C
  have hdisjoint : (s : Set _).PairwiseDisjoint t := by
    intro D hD E hE hne
    apply Finset.disjoint_left.mpr
    intro x hxD hxE
    obtain ⟨hxD,hxC⟩ := Finset.mem_sdiff.mp hxD
    obtain ⟨hxE,_⟩ := Finset.mem_sdiff.mp hxE
    have hfirst := (Finset.mem_filter.mp hxD).2.1
    have hnC : (fun j => (modularBitSign (x j) : ZMod p))∉C := by
      intro hc
      exact hxC (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hfirst,hc⟩)
    obtain ⟨F,hF,hunique⟩ := sign_vector_unique_code_neighbor hodd C hC x hnC
    have hDm : IsBilinearCodeNeighbor B C D :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hD).1).2
    have hEm : IsBilinearCodeNeighbor B C E :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hE).1).2
    exact hne ((hunique D ⟨hDm,(Finset.mem_filter.mp hxD).2.2⟩).trans
      (hunique E ⟨hEm,(Finset.mem_filter.mp hxE).2.2⟩).symm)
  have hunion : s.biUnion t=codeSignCandidates (B.orthogonal G) \ codeSignCandidates C := by
    ext x
    constructor
    · intro hx
      obtain ⟨D,hD,hxD⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨hxD,hxC⟩ := Finset.mem_sdiff.mp hxD
      have hGD : G≤D := (Finset.mem_filter.mp hD).2
      have hself : D=B.orthogonal D :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hD).1).2.1
      have hxres := (Finset.mem_filter.mp hxD).2.2
      have hxorth : (fun j => (modularBitSign (x j) : ZMod p))∈B.orthogonal G := by
        intro y hy
        exact (hself ▸ hxres) y (hGD hy)
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,(Finset.mem_filter.mp hxD).2.1,hxorth⟩,hxC⟩
    · intro hx
      obtain ⟨hxpool,hxC⟩ := Finset.mem_sdiff.mp hx
      obtain ⟨hfirst,hwG⟩ := (Finset.mem_filter.mp hxpool).2
      let w : Fin (4*p) → ZMod p := fun j => (modularBitSign (x j) : ZMod p)
      have hwC : w∉C := by
        intro hc
        exact hxC (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hfirst,hc⟩)
      let D := bilinearCodePivot B C w
      have hp := self_dual_bilinear_pivot B (coordinateDotForm_symm _ _)
        (coordinateDotForm_nondegenerate _ _) C hC w hwC (signResidue_isotropic x)
      have hne : D≠C := by intro heq;exact hwC (heq ▸ hp.2.2.2.2)
      have hGD : G≤D := by
        intro y hy
        apply Submodule.mem_sup_left
        refine ⟨hGC hy,?_⟩
        change B w y=0
        rw [(coordinateDotForm_symm (ZMod p) (4*p)).eq w y]
        exact hwG y hy
      have hneighbor : IsBilinearCodeNeighbor B C D := by
        refine ⟨hp.1,hne,?_⟩
        rw [hp.2.2.1]
        exact hp.2.1
      refine Finset.mem_biUnion.mpr ⟨D,?_,?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,hneighbor⟩,hGD⟩
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,hfirst,hp.2.2.2.2⟩,hxC⟩
  have hh := Finset.card_biUnion hdisjoint
  rw [hunion] at hh
  exact hh.symm

theorem restricted_neighbor_hyperplane_equiv {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (htwo : (2 : K)≠0)
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (C G : Submodule K V) (hC : C=B.orthogonal C) (hGC : G≤C) :
    ∃ e : {D : Submodule K V // IsBilinearCodeNeighbor B C D ∧ G≤D} ≃
      linearHyperplanesOver (G.comap C.subtype),
      ∀ D,(e D).val=(C ⊓ D.val).comap C.subtype := by
  let A := G.comap C.subtype
  let f : {D : Submodule K V // IsBilinearCodeNeighbor B C D ∧ G≤D} → linearHyperplanesOver A :=
    fun D => ⟨(neighborIntersectionHyperplane B C ⟨D.val,D.property.1⟩).val,⟨by
      intro x hx
      exact ⟨x.property,D.property.2 hx⟩,
      (neighborIntersectionHyperplane B C ⟨D.val,D.property.1⟩).property⟩⟩
  have hb := neighborIntersectionHyperplane_bijective htwo B hB hnd C hC
  have hfb : Function.Bijective f := by
    constructor
    · intro D E hDE
      have hH : neighborIntersectionHyperplane B C ⟨D.val,D.property.1⟩=
          neighborIntersectionHyperplane B C ⟨E.val,E.property.1⟩ :=
        Subtype.ext (congrArg (fun H : linearHyperplanesOver A => H.val) hDE)
      exact Subtype.ext (congrArg
        (fun D : {D : Submodule K V // IsBilinearCodeNeighbor B C D} => D.val) (hb.1 hH))
    · intro H
      obtain ⟨D,hD⟩ := hb.2 ⟨H.val,H.property.2⟩
      have hGD : G≤D.val := by
        intro x hx
        have hxA : (⟨x,hGC hx⟩ : C)∈A := hx
        have hxH := H.property.1 hxA
        have heq := congrArg Subtype.val hD
        rw [← heq] at hxH
        exact hxH.2
      refine ⟨⟨D.val,D.property,hGD⟩,?_⟩
      exact Subtype.ext (congrArg (fun H : linearHyperplanes K C => H.val) hD)
  exact ⟨Equiv.ofBijective f hfb,fun _ => rfl⟩

theorem finite_restricted_neighbors_missing_vector {K V : Type*} [Field K] [Fintype K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Fintype V] (htwo : (2 : K)≠0)
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (C G : Submodule K V) (hC : C=B.orthogonal C) (hGC : G≤C)
    (v : V) (hvC : v∈C) (hvG : v∉G) :
    Nat.card {D : Submodule K V // IsBilinearCodeNeighbor B C D ∧ G≤D ∧ v∉D}=
      Nat.card K ^ (finrank K C-finrank K G-1) := by
  classical
  obtain ⟨e,he⟩ := restricted_neighbor_hyperplane_equiv htwo B hB hnd C G hC hGC
  let vC : C := ⟨v,hvC⟩
  have hmem (D : {D : Submodule K V // IsBilinearCodeNeighbor B C D ∧ G≤D}) :
      v∉D.val ↔ vC∉(e D).val := by
    rw [he]
    change (v∉D.val ↔ ¬(v∈C ∧ v∈D.val))
    simp only [hvC,true_and]
  let e' : {D : {D : Submodule K V // IsBilinearCodeNeighbor B C D ∧ G≤D} // v∉D.val} ≃
      {H : linearHyperplanesOver (G.comap C.subtype) // vC∉H.val} := e.subtypeEquiv hmem
  let regroup : {D : Submodule K V // IsBilinearCodeNeighbor B C D ∧ G≤D ∧ v∉D} ≃
      {D : {D : Submodule K V // IsBilinearCodeNeighbor B C D ∧ G≤D} // v∉D.val} := {
    toFun := fun D => ⟨⟨D.val,D.property.1,D.property.2.1⟩,D.property.2.2⟩
    invFun := fun D => ⟨D.val.val,D.val.property.1,D.val.property.2,D.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr (regroup.trans e')]
  have hvA : vC∉G.comap C.subtype := hvG
  rw [finite_hyperplanes_missing_vector (G.comap C.subtype) vC hvA]
  have hr := Submodule.finrank_map_subtype_eq C (G.comap C.subtype)
  rw [ambient_submodule_map_comap C G hGC] at hr
  rw [← hr]

noncomputable def restrictedNeighborsOmitting {p : ℕ} [Fact p.Prime]
    (C G : Submodule (ZMod p) (Fin (4*p) → ZMod p)) (v : Fin (4*p) → ZMod p) :
    Finset (Submodule (ZMod p) (Fin (4*p) → ZMod p)) := by
  classical
  exact (restrictedCodeNeighbors C G).filter (fun D => v∉D)

theorem restrictedCodeNeighbors_missing_card {p : ℕ} [Fact p.Prime] (hodd : p%2=1)
    (C G : Submodule (ZMod p) (Fin (4*p) → ZMod p))
    (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C) (hGC : G≤C)
    (v : Fin (4*p) → ZMod p) (hvC : v∈C) (hvG : v∉G) :
    (restrictedNeighborsOmitting C G v).card=
      p ^ (finrank (ZMod p) C-finrank (ZMod p) G-1) := by
  classical
  have hp : p.Prime := Fact.out
  have htwo : (2 : ZMod p)≠0 := by
    intro hz
    have hd : p∣2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have hp2 : p=2 := (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left hp.ne_one
    omega
  let S := (restrictedCodeNeighbors C G).filter (fun D => v∉D)
  let e : S ≃ {D : Submodule (ZMod p) (Fin (4*p) → ZMod p) //
      IsBilinearCodeNeighbor (coordinateDotForm (ZMod p) (4*p)) C D ∧ G≤D ∧ v∉D} := {
    toFun := fun D => by
      obtain ⟨hD,hv⟩ := Finset.mem_filter.mp D.property
      obtain ⟨hN,hG⟩ := Finset.mem_filter.mp hD
      exact ⟨D.val,(Finset.mem_filter.mp hN).2,hG,hv⟩
    invFun := fun D => ⟨D.val,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,D.property.1⟩,D.property.2.1⟩,D.property.2.2⟩⟩
    left_inv := fun D => rfl
    right_inv := fun D => rfl }
  have hleft : Nat.card S=S.card := by rw [Nat.card_eq_fintype_card,Fintype.card_coe]
  change S.card = _
  rw [← hleft,Nat.card_congr e]
  simpa only [Nat.card_zmod] using finite_restricted_neighbors_missing_vector htwo
    (coordinateDotForm (ZMod p) (4*p)) (coordinateDotForm_symm _ _)
      (coordinateDotForm_nondegenerate _ _) C G hC hGC v hvC hvG

theorem sum_filter_card_comm {α β : Type*} (s : Finset α) (t : Finset β)
    (R : α → β → Prop) [∀ a b,Decidable (R a b)] :
    (∑ a∈s,(t.filter (R a)).card)=(∑ b∈t,(s.filter (fun a => R a b)).card) := by
  calc
    _=(∑ a∈s,∑ b∈t,if R a b then (1 : ℕ) else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.card_eq_sum_ones,Finset.sum_filter]
    _=(∑ b∈t,∑ a∈s,if R a b then (1 : ℕ) else 0) := Finset.sum_comm
    _=_ := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.card_eq_sum_ones,Finset.sum_filter]

theorem restricted_neighbor_lost_sign_census {p : ℕ} [Fact p.Prime] (hodd : p%2=1)
    (C G : Submodule (ZMod p) (Fin (4*p) → ZMod p))
    (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C) (hGC : G≤C) :
    (∑ D∈restrictedCodeNeighbors C G,(codeSignCandidates C \ codeSignCandidates D).card)=
      (codeSignCandidates C \ codeSignCandidates G).card *
        p ^ (finrank (ZMod p) C-finrank (ZMod p) G-1) := by
  classical
  let s := restrictedCodeNeighbors C G
  let A := codeSignCandidates C
  let T := codeSignCandidates G
  let L := p ^ (finrank (ZMod p) C-finrank (ZMod p) G-1)
  have hsdiff (D : Submodule (ZMod p) (Fin (4*p) → ZMod p)) :
      A \ codeSignCandidates D=A.filter (fun x => x∉codeSignCandidates D) := by
    ext x
    simp
  have hfiber (x) (hx : x∈A) :
      (s.filter (fun D => x∉codeSignCandidates D)).card=if x∈T then 0 else L := by
    have hxfirst := (Finset.mem_filter.mp hx).2.1
    by_cases hxT : x∈T
    · rw [if_pos hxT]
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro D hD hn
      have hGD : G≤D := (Finset.mem_filter.mp hD).2
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxfirst,
        hGD (Finset.mem_filter.mp hxT).2.2⟩)
    · rw [if_neg hxT]
      have hvG : (fun j => (modularBitSign (x j) : ZMod p))∉G := by
        intro hv
        exact hxT (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxfirst,hv⟩)
      have hf : s.filter (fun D => x∉codeSignCandidates D)=
          s.filter (fun D => (fun j => (modularBitSign (x j) : ZMod p))∉D) := by
        ext D
        simp only [Finset.mem_filter,codeSignCandidates,Finset.mem_univ,true_and,hxfirst]
      rw [hf]
      exact restrictedCodeNeighbors_missing_card hodd C G hC hGC _ (Finset.mem_filter.mp hx).2.2 hvG
  change (∑ D∈s,(A \ codeSignCandidates D).card)=(A \ T).card*L
  simp_rw [hsdiff]
  rw [sum_filter_card_comm]
  calc
    _=(∑ x∈A,if x∈T then 0 else L) := Finset.sum_congr rfl hfiber
    _=(∑ x∈A \ T,L) := by
      rw [Finset.sdiff_eq_filter,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : x∈T <;> simp [h]
    _=(A \ T).card*L := by simp

theorem codeSignCandidates_mono {p N : ℕ}
    (C D : Submodule (ZMod p) (Fin N → ZMod p)) (hCD : C≤D) :
    codeSignCandidates C⊆codeSignCandidates D := by
  classical
  intro x hx
  obtain ⟨_,hfirst,hres⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hfirst,hCD hres⟩

theorem restricted_neighbor_signed_incidence {p : ℕ} [Fact p.Prime] (hodd : p%2=1)
    (C G : Submodule (ZMod p) (Fin (4*p) → ZMod p))
    (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C) (hGC : G≤C) :
    (∑ D∈restrictedCodeNeighbors C G,
      (((codeSignCandidates D).card : ℤ)-(codeSignCandidates C).card))=
      ((codeSignCandidates ((coordinateDotForm (ZMod p) (4*p)).orthogonal G)).card : ℤ)-
        (codeSignCandidates C).card-
          ((codeSignCandidates C).card-(codeSignCandidates G).card : ℤ)*
            (p : ℤ) ^ (finrank (ZMod p) C-finrank (ZMod p) G-1) := by
  classical
  let S := restrictedCodeNeighbors C G
  have hsub : C≤(coordinateDotForm (ZMod p) (4*p)).orthogonal G := by
    intro x hx y hy
    exact (hC ▸ hx) y (hGC hy)
  have hpool := codeSignCandidates_mono C _ hsub
  have hretained := codeSignCandidates_mono G C hGC
  have hdiff (D : Submodule (ZMod p) (Fin (4*p) → ZMod p)) :
      ((codeSignCandidates D).card : ℤ)-(codeSignCandidates C).card=
        ((codeSignCandidates D \ codeSignCandidates C).card : ℤ)-
          (codeSignCandidates C \ codeSignCandidates D).card := by
    have h1 := Finset.card_sdiff_add_card_inter (codeSignCandidates D) (codeSignCandidates C)
    have h2 := Finset.card_sdiff_add_card_inter (codeSignCandidates C) (codeSignCandidates D)
    rw [Finset.inter_comm] at h2
    omega
  have heqsum : (∑ D∈restrictedCodeNeighbors C G,
      (((codeSignCandidates D).card : ℤ)-(codeSignCandidates C).card))=
      ∑ D∈restrictedCodeNeighbors C G,
        (((codeSignCandidates D \ codeSignCandidates C).card : ℤ)-
          (codeSignCandidates C \ codeSignCandidates D).card) :=
    Finset.sum_congr rfl (fun D _ => hdiff D)
  rw [heqsum,Finset.sum_sub_distrib,← Nat.cast_sum,← Nat.cast_sum,
    restricted_neighbor_new_sign_census hodd C G hC hGC,
    restricted_neighbor_lost_sign_census hodd C G hC hGC,
    Finset.card_sdiff_of_subset hpool,Finset.card_sdiff_of_subset hretained,
    Nat.cast_sub (Finset.card_le_card hpool),Nat.cast_mul,
    Nat.cast_sub (Finset.card_le_card hretained),Nat.cast_pow]

theorem restricted_neighbor_incidence_and_improvement {p : ℕ} [Fact p.Prime] (hodd : p%2=1)
    (C G : Submodule (ZMod p) (Fin (4*p) → ZMod p))
    (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C) (hGC : G≤C) :
    (restrictedCodeNeighbors C G).card=
      (p ^ (finrank (ZMod p) C-finrank (ZMod p) G)-1)/(p-1) ∧
    (∑ D∈restrictedCodeNeighbors C G,
      (((codeSignCandidates D).card : ℤ)-(codeSignCandidates C).card))=
      ((codeSignCandidates ((coordinateDotForm (ZMod p) (4*p)).orthogonal G)).card : ℤ)-
        (codeSignCandidates C).card-
          ((codeSignCandidates C).card-(codeSignCandidates G).card : ℤ)*
            (p : ℤ) ^ (finrank (ZMod p) C-finrank (ZMod p) G-1) ∧
    (0<((codeSignCandidates ((coordinateDotForm (ZMod p) (4*p)).orthogonal G)).card : ℤ)-
        (codeSignCandidates C).card-
          ((codeSignCandidates C).card-(codeSignCandidates G).card : ℤ)*
            (p : ℤ) ^ (finrank (ZMod p) C-finrank (ZMod p) G-1) →
      ∃ D∈restrictedCodeNeighbors C G,(codeSignCandidates C).card<(codeSignCandidates D).card) := by
  have hi := restricted_neighbor_signed_incidence hodd C G hC hGC
  refine ⟨restrictedCodeNeighbors_card hodd C G hC hGC,hi,?_⟩
  intro hpos
  classical
  by_contra hn
  have hle (D) (hD : D∈restrictedCodeNeighbors C G) :
      (codeSignCandidates D).card≤(codeSignCandidates C).card := by
    by_contra h
    exact hn ⟨D,hD,by omega⟩
  have hs : (∑ D∈restrictedCodeNeighbors C G,
      (((codeSignCandidates D).card : ℤ)-(codeSignCandidates C).card))≤0 := by
    apply Finset.sum_nonpos
    intro D hD
    have hh := hle D hD
    omega
  rw [hi] at hs
  omega

end CompletionTheory
