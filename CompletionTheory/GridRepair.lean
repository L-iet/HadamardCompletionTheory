/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.WeightedCodeGrid
@[expose] public section
set_option maxHeartbeats 2000000
namespace CompletionTheory
open Matrix Module Submodule

theorem determinant_zero_subspace_in_labelled_ruling {K : Type*} [Field K]
    (W : Submodule K (Matrix (Fin 2) (Fin 2) K)) (hW : ∀ M∈W,M.det=0) :
    ∃ a : Projectivization K (Fin 2 → K) ⊕ Projectivization K (Fin 2 → K),W≤matrixRulingSpace a := by
  classical
  by_cases hz : W=⊥
  · let z : Fin 2 → K := ![1,0]
    have hz0 : z≠0 := by intro h;have hh := congrFun h 0;exact one_ne_zero hh
    exact ⟨Sum.inl (Projectivization.mk K z hz0),hz ▸ bot_le⟩
  · obtain ⟨A,hA,hA0⟩ := (Submodule.ne_bot_iff W).mp hz
    obtain ⟨u,v,hu,hv,hAv,hle⟩ := determinant_zero_subspace_in_one_ruling W hW A hA hA0
    rcases hle with hcol|hrow
    · refine ⟨Sum.inl (Projectivization.mk K u hu),?_⟩
      change W≤columnLineSpace (Projectivization.mk K u hu).rep
      rwa [columnLineSpace_projective_rep]
    · refine ⟨Sum.inr (Projectivization.mk K v hv),?_⟩
      change W≤rowLineSpace (Projectivization.mk K v hv).rep
      rwa [rowLineSpace_projective_rep]

theorem self_orthogonal_code_extension_codimension_two {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (htwo : (2 : K)≠0)
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (C G D : Submodule K V) (hC : C=B.orthogonal C) (hGC : G≤C)
    (hcodim : finrank K G+2=finrank K C) (hGD : G≤D) (hDH : D≤B.orthogonal G)
    (hD : D≤B.orthogonal D) :
    ∃ H : Submodule K V,H=B.orthogonal H ∧ G≤H ∧ D≤H := by
  classical
  obtain ⟨E,hnorm,hbase⟩ := code_quotient_determinant_model htwo B hB hnd C G hC hGC hcodim
  let W := (orthogonalQuotientCode B D G).map E.toLinearMap
  have hW : ∀ M∈W,M.det=0 := by
    rintro M ⟨q,hq,rfl⟩
    induction q using Submodule.Quotient.induction_on with | _ x =>
    have hx := (orthogonalQuotientCode_mk_mem_iff B D G hGD x).mp hq
    have hz : B x.val x.val=0 := hD hx x.val hx
    have hh := hnorm (Submodule.Quotient.mk x)
    change B x.val x.val=2*(E (Submodule.Quotient.mk x)).det at hh
    rw [hz] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left htwo
  obtain ⟨a,ha⟩ := determinant_zero_subspace_in_labelled_ruling W hW
  have hG : G≤B.orthogonal G := by
    intro x hx y hy
    exact ((SetLike.ext_iff.mp hC x).mp (hGC hx)) y (hGC hy)
  have hqdim := (codimension_two_quotient_dimensions B hB hnd C G hC hGC hcodim).1
  have hself := quotientRulingCode_self_dual htwo B hB hnd G hG E hnorm hqdim a
  refine ⟨quotientRulingCode B G E a,hself.1,hself.2,?_⟩
  intro x hx
  let xx : B.orthogonal G := ⟨x,hDH hx⟩
  have hq : Submodule.Quotient.mk xx∈orthogonalQuotientCode B D G :=
    (orthogonalQuotientCode_mk_mem_iff B D G hGD xx).mpr hx
  have hM : E (Submodule.Quotient.mk xx)∈W := ⟨_,hq,rfl⟩
  apply (liftOrthogonalQuotientCode_mem_iff B G _ xx).mpr
  exact ha hM

theorem span_with_retained_self_orthogonal {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (G : Submodule K V) (hG : G≤B.orthogonal G)
    (R : Set V) (hR : R⊆B.orthogonal G) (hRR : ∀ x∈R,∀ y∈R,B x y=0) :
    G ⊔ Submodule.span K R≤B.orthogonal (G ⊔ Submodule.span K R) := by
  let S := Submodule.span K R
  have hSG : S≤B.orthogonal G := Submodule.span_le.mpr hR
  have hker (x : V) (hx : x∈R) : S≤LinearMap.ker (B x) :=
    Submodule.span_le.mpr (fun y hy => hRR x hx y hy)
  have hSS : S≤B.orthogonal S := by
    intro x hx y hy
    have hk : S≤LinearMap.ker (B.flip x) :=
      Submodule.span_le.mpr (fun z hz => hker z hz hx)
    exact hk hy
  intro x hx y hy
  obtain ⟨gx,hgx,sx,hsx,rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨gy,hgy,sy,hsy,rfl⟩ := Submodule.mem_sup.mp hy
  have hgg : B gy gx=0 := hG hgx gy hgy
  have hgs : B gy sx=0 := hSG hsx gy hgy
  have hsg : B sy gx=0 := by rw [hB.eq sy gx];exact hSG hsy gx hgx
  have hss : B sy sx=0 := hSS hsx sy hsy
  simp only [map_add,LinearMap.add_apply,hgg,hgs,hsg,hss,add_zero]

theorem orthogonal_pool_family_contained_in_code {p : ℕ} [Fact p.Prime] (hodd : p%2=1)
    (C G : Submodule (ZMod p) (Fin (4*p) → ZMod p))
    (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C) (hGC : G≤C)
    (hcodim : finrank (ZMod p) G+2=finrank (ZMod p) C)
    (T : Finset (Fin (4*p) → Bool))
    (hT : T⊆codeSignCandidates ((coordinateDotForm (ZMod p) (4*p)).orthogonal G))
    (horth : ∀ x∈T,∀ y∈T,x≠y → (∑ j,modularBitSign (x j)*modularBitSign (y j))=0) :
    ∃ H : Submodule (ZMod p) (Fin (4*p) → ZMod p),
      H=(coordinateDotForm (ZMod p) (4*p)).orthogonal H ∧ G≤H ∧ T⊆codeSignCandidates H := by
  classical
  let B := coordinateDotForm (ZMod p) (4*p)
  let v := fun (x : Fin (4*p) → Bool) (j : Fin (4*p)) => (modularBitSign (x j) : ZMod p)
  let R := Set.range (fun x : T => v x.val)
  let D := G ⊔ Submodule.span (ZMod p) R
  have hp : p.Prime := Fact.out
  have htwo : (2 : ZMod p)≠0 := by
    intro hz
    have hd : p∣2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have hp2 : p=2 := (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left hp.ne_one
    omega
  have hG : G≤B.orthogonal G := by
    intro x hx y hy
    exact ((SetLike.ext_iff.mp hC x).mp (hGC hx)) y (hGC hy)
  have hR : R⊆B.orthogonal G := by
    rintro x ⟨t,rfl⟩
    exact (Finset.mem_filter.mp (hT t.property)).2.2
  have hRR : ∀ x∈R,∀ y∈R,B x y=0 := by
    rintro x ⟨t,rfl⟩ y ⟨u,rfl⟩
    change B (v t.val) (v u.val)=0
    by_cases heq : t.val=u.val
    · rw [heq]
      exact signResidue_isotropic u.val
    · have hz := horth t.val t.property u.val u.property heq
      change (∑ j,(modularBitSign (t.val j) : ZMod p)*(modularBitSign (u.val j) : ZMod p))=0
      have hc := congrArg (fun z : ℤ => (z : ZMod p)) hz
      simpa only [Int.cast_sum,Int.cast_mul,Int.cast_zero] using hc
  have hD : D≤B.orthogonal D := span_with_retained_self_orthogonal B (coordinateDotForm_symm _ _) G hG R hR hRR
  have hDH : D≤B.orthogonal G := sup_le hG (Submodule.span_le.mpr hR)
  obtain ⟨H,hH,hGH,hDH'⟩ := self_orthogonal_code_extension_codimension_two htwo B
    (coordinateDotForm_symm _ _) (coordinateDotForm_nondegenerate _ _) C G D hC hGC hcodim le_sup_left hDH hD
  refine ⟨H,hH,hGH,?_⟩
  intro x hx
  have hxD : v x∈D := Submodule.mem_sup_right (Submodule.subset_span ⟨⟨x,hx⟩,rfl⟩)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp (hT hx)).2.1,hDH' hxD⟩

theorem five_retained_rows_code_frame {p : ℕ} [Fact p.Prime] (hodd : p%2=1)
    (G H : Submodule (ZMod p) (Fin (4*p) → ZMod p))
    (hH : H=(coordinateDotForm (ZMod p) (4*p)).orthogonal H) (hGH : G≤H)
    (a : Fin 5 → Fin (4*p) → Bool) (ha : ∀ i,a i∈codeSignCandidates G)
    (hgram : ∀ i j,(∑ k,modularBitSign (a i k)*modularBitSign (a j k))=
      if i=j then (4*p : ℤ) else 0) :
    codeSignCandidates G⊆codeSignCandidates H ∧
      codeSignCandidates H⊆codeSignCandidates ((coordinateDotForm (ZMod p) (4*p)).orthogonal G) ∧
      (∀ x∈codeSignCandidates H,∀ y∈codeSignCandidates H,x≠y →
        (∑ j,modularBitSign (x j)*modularBitSign (y j))=0) ∧
      (codeSignCandidates H).card≤4*p := by
  have hp : p.Prime := Fact.out
  have hself : IsSelfOrthogonalModularCode H := by
    intro x hx y hy
    exact ((SetLike.ext_iff.mp hH y).mp hy) x hx
  have hsub := codeSignCandidates_mono G H hGH
  have haH (i : Fin 5) : a i∈codeSignCandidates H := hsub (ha i)
  have hf := five_rows_remove_code_compatibility hp.pos hodd H hself a haH hgram
  have hHG : H≤(coordinateDotForm (ZMod p) (4*p)).orthogonal G := by
    intro x hx y hy
    exact ((SetLike.ext_iff.mp hH x).mp hx) y (hGH hy)
  exact ⟨hsub,codeSignCandidates_mono H _ hHG,hf.1,hf.2.2⟩

theorem orthogonal_pool_optimum_over_codes {p : ℕ} [Fact p.Prime] (hodd : p%2=1)
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (C G : Submodule (ZMod p) (Fin (4*p) → ZMod p))
    (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C) (hGC : G≤C)
    (hcodim : finrank (ZMod p) G+2=finrank (ZMod p) C)
    (a : Fin 5 → Fin (4*p) → Bool) (ha : ∀ i,a i∈codeSignCandidates G)
    (hgram : ∀ i j,(∑ k,modularBitSign (a i k)*modularBitSign (a j k))=
      if i=j then (4*p : ℤ) else 0)
    (e : ι ≃ {D : Submodule (ZMod p) (Fin (4*p) → ZMod p) //
      D=(coordinateDotForm (ZMod p) (4*p)).orthogonal D ∧ G≤D}) :
    let U := codeSignCandidates ((coordinateDotForm (ZMod p) (4*p)).orthogonal G)
    let A := codeSignCandidates G
    let M := Finset.univ.sup (fun i => (codeSignCandidates (e i).val).card)
    M≤4*p ∧
    (∀ T : Finset (Fin (4*p) → Bool),T⊆U →
      (∀ x∈T,∀ y∈T,x≠y → (∑ j,modularBitSign (x j)*modularBitSign (y j))=0) → T.card≤M) ∧
    ∃ T : Finset (Fin (4*p) → Bool),A⊆T ∧ T⊆U ∧
      (∀ x∈T,∀ y∈T,x≠y → (∑ j,modularBitSign (x j)*modularBitSign (y j))=0) ∧ T.card=M := by
  classical
  let U := codeSignCandidates ((coordinateDotForm (ZMod p) (4*p)).orthogonal G)
  let A := codeSignCandidates G
  let f := fun i => (codeSignCandidates (e i).val).card
  let M := Finset.univ.sup f
  have frame (i : ι) := five_retained_rows_code_frame hodd G (e i).val (e i).property.1 (e i).property.2 a ha hgram
  refine ⟨?_,?_,?_⟩
  · apply Finset.sup_le
    intro i hi
    exact (frame i).2.2.2
  · intro T hTU hTorth
    obtain ⟨H,hH,hGH,hTH⟩ := orthogonal_pool_family_contained_in_code hodd C G hC hGC hcodim T hTU hTorth
    let j := e.symm ⟨H,hH,hGH⟩
    have hj : (e j).val=H := congrArg Subtype.val (e.apply_symm_apply ⟨H,hH,hGH⟩)
    have hTf : T.card≤f j := by
      change T.card≤(codeSignCandidates (e j).val).card
      rw [hj]
      exact Finset.card_le_card hTH
    exact hTf.trans (Finset.le_sup (Finset.mem_univ j))
  · obtain ⟨i,hi,hmax⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty f
    exact ⟨codeSignCandidates (e i).val,(frame i).1,(frame i).2.1,(frame i).2.2.1,hmax.symm⟩

theorem code_count_sup_grid_formula {p : ℕ} [Fact p.Prime]
    (G : Submodule (ZMod p) (Fin (4*p) → ZMod p))
    (e : (Fin (p+1) ⊕ Fin (p+1)) ≃ {D : Submodule (ZMod p) (Fin (4*p) → ZMod p) //
      D=(coordinateDotForm (ZMod p) (4*p)).orthogonal D ∧ G≤D})
    (w : Fin (p+1) → Fin (p+1) → ℕ)
    (hr : ∀ i,(codeSignCandidates (e (Sum.inl i)).val).card=(codeSignCandidates G).card+(∑ j,w i j))
    (hc : ∀ j,(codeSignCandidates (e (Sum.inr j)).val).card=(codeSignCandidates G).card+(∑ i,w i j)) :
    Finset.univ.sup (fun i => (codeSignCandidates (e i).val).card)=
      (codeSignCandidates G).card+max
        (Finset.univ.sup (fun i => ∑ j,w i j)) (Finset.univ.sup (fun j => ∑ i,w i j)) := by
  classical
  let f := fun i => (codeSignCandidates (e i).val).card
  let R := Finset.univ.sup (fun i => ∑ j,w i j)
  let L := Finset.univ.sup (fun j => ∑ i,w i j)
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro k hk
    rcases k with i|j
    · rw [hr]
      apply Nat.add_le_add_left
      exact (Finset.le_sup (Finset.mem_univ i)).trans (le_max_left R L)
    · rw [hc]
      apply Nat.add_le_add_left
      exact (Finset.le_sup (Finset.mem_univ j)).trans (le_max_right R L)
  · have hrow : (codeSignCandidates G).card+R≤Finset.univ.sup f := by
      obtain ⟨i,hi,hmax⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun i => ∑ j,w i j)
      have hh : f (Sum.inl i)≤Finset.univ.sup f := Finset.le_sup (Finset.mem_univ _)
      change (codeSignCandidates (e (Sum.inl i)).val).card≤_ at hh
      rw [hr,← hmax] at hh
      exact hh
    have hcol : (codeSignCandidates G).card+L≤Finset.univ.sup f := by
      obtain ⟨j,hj,hmax⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun j => ∑ i,w i j)
      have hh : f (Sum.inr j)≤Finset.univ.sup f := Finset.le_sup (Finset.mem_univ _)
      change (codeSignCandidates (e (Sum.inr j)).val).card≤_ at hh
      rw [hc,← hmax] at hh
      exact hh
    by_cases hRL : R≤L
    · rw [max_eq_right hRL]
      exact hcol
    · rw [max_eq_left (by omega : L≤R)]
      exact hrow

theorem weighted_grid_optimal_repair {p : ℕ} [Fact p.Prime] (hodd : p%2=1)
    (C G : Submodule (ZMod p) (Fin (4*p) → ZMod p))
    (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C) (hGC : G≤C)
    (hcodim : finrank (ZMod p) G+2=finrank (ZMod p) C)
    (a : Fin 5 → Fin (4*p) → Bool) (ha : ∀ i,a i∈codeSignCandidates G)
    (hgram : ∀ i j,(∑ k,modularBitSign (a i k)*modularBitSign (a j k))=
      if i=j then (4*p : ℤ) else 0) :
    let U := codeSignCandidates ((coordinateDotForm (ZMod p) (4*p)).orthogonal G)
    let A := codeSignCandidates G
    ∃ e : (Fin (p+1) ⊕ Fin (p+1)) ≃ {D : Submodule (ZMod p) (Fin (4*p) → ZMod p) //
      D=(coordinateDotForm (ZMod p) (4*p)).orthogonal D ∧ G≤D},
      ∃ w : Fin (p+1) → Fin (p+1) → ℕ,
        (∀ i,(codeSignCandidates (e (Sum.inl i)).val).card=A.card+(∑ j,w i j)) ∧
        (∀ j,(codeSignCandidates (e (Sum.inr j)).val).card=A.card+(∑ i,w i j)) ∧
        let M := A.card+max (Finset.univ.sup (fun i => ∑ j,w i j)) (Finset.univ.sup (fun j => ∑ i,w i j))
        M≤4*p ∧
        (∀ T : Finset (Fin (4*p) → Bool),T⊆U →
          (∀ x∈T,∀ y∈T,x≠y → (∑ j,modularBitSign (x j)*modularBitSign (y j))=0) →
            ∃ k,T⊆codeSignCandidates (e k).val) ∧
        (∀ T : Finset (Fin (4*p) → Bool),T⊆U →
          (∀ x∈T,∀ y∈T,x≠y → (∑ j,modularBitSign (x j)*modularBitSign (y j))=0) → T.card≤M) ∧
        (∃ T : Finset (Fin (4*p) → Bool),A⊆T ∧ T⊆U ∧
          (∀ x∈T,∀ y∈T,x≠y → (∑ j,modularBitSign (x j)*modularBitSign (y j))=0) ∧ T.card=M) ∧
        ((∃ T : Finset (Fin (4*p) → Bool),A⊆T ∧ T⊆U ∧
          (∀ x∈T,∀ y∈T,x≠y → (∑ j,modularBitSign (x j)*modularBitSign (y j))=0) ∧ T.card=4*p) ↔
          (∃ i,(∑ j,w i j)=4*p-A.card) ∨ (∃ j,(∑ i,w i j)=4*p-A.card)) := by
  classical
  obtain ⟨e,w,ht,hr,hc,hlabels⟩ := weighted_code_grid_classification hodd C G hC hGC hcodim
  have opt := orthogonal_pool_optimum_over_codes hodd C G hC hGC hcodim a ha hgram e
  have hmax := code_count_sup_grid_formula G e w hr hc
  let U := codeSignCandidates ((coordinateDotForm (ZMod p) (4*p)).orthogonal G)
  let A := codeSignCandidates G
  let M := A.card+max (Finset.univ.sup (fun i => ∑ j,w i j)) (Finset.univ.sup (fun j => ∑ i,w i j))
  have hbound : M≤4*p := by
    change (codeSignCandidates G).card+max _ _≤4*p
    rw [← hmax]
    exact opt.1
  have hupper (T : Finset (Fin (4*p) → Bool)) (hTU : T⊆U)
      (hO : ∀ x∈T,∀ y∈T,x≠y → (∑ j,modularBitSign (x j)*modularBitSign (y j))=0) : T.card≤M := by
    have hh := opt.2.1 T hTU hO
    rw [hmax] at hh
    exact hh
  have hattain : ∃ T : Finset (Fin (4*p) → Bool),A⊆T ∧ T⊆U ∧
      (∀ x∈T,∀ y∈T,x≠y → (∑ j,modularBitSign (x j)*modularBitSign (y j))=0) ∧ T.card=M := by
    obtain ⟨T,hAT,hTU,hO,hsize⟩ := opt.2.2
    exact ⟨T,hAT,hTU,hO,hsize.trans hmax⟩
  have hAN : A.card≤4*p := by
    have hb : A.card≤M := by dsimp [M];omega
    omega
  have frame (k) := five_retained_rows_code_frame hodd G (e k).val (e k).property.1 (e k).property.2 a ha hgram
  refine ⟨e,w,hr,hc,hbound,?_,hupper,hattain,?_⟩
  · intro T hTU hO
    obtain ⟨H,hH,hGH,hTH⟩ := orthogonal_pool_family_contained_in_code hodd C G hC hGC hcodim T hTU hO
    let k := e.symm ⟨H,hH,hGH⟩
    refine ⟨k,?_⟩
    have hk : (e k).val=H := congrArg Subtype.val (e.apply_symm_apply ⟨H,hH,hGH⟩)
    rw [hk]
    exact hTH
  · constructor
    · rintro ⟨T,hAT,hTU,hO,hsize⟩
      have hMN : M=4*p := by have hh := hupper T hTU hO;omega
      obtain ⟨k,hk,hEq⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
        (fun k => (codeSignCandidates (e k).val).card)
      have hcode : (codeSignCandidates (e k).val).card=4*p := by
        rw [hmax] at hEq
        exact hEq.symm.trans hMN
      rcases k with i|j
      · left
        refine ⟨i,?_⟩
        rw [hr] at hcode
        change A.card+(∑ j,w i j)=4*p at hcode
        change (∑ j,w i j)=4*p-A.card
        omega
      · right
        refine ⟨j,?_⟩
        rw [hc] at hcode
        change A.card+(∑ i,w i j)=4*p at hcode
        change (∑ i,w i j)=4*p-A.card
        omega
    · rintro (⟨i,hrow⟩|⟨j,hcol⟩)
      · refine ⟨codeSignCandidates (e (Sum.inl i)).val,(frame _).1,(frame _).2.1,(frame _).2.2.1,?_⟩
        rw [hr,hrow]
        change A.card+(4*p-A.card)=4*p
        omega
      · refine ⟨codeSignCandidates (e (Sum.inr j)).val,(frame _).1,(frame _).2.1,(frame _).2.2.1,?_⟩
        rw [hc,hcol]
        change A.card+(4*p-A.card)=4*p
        omega

theorem full_sign_family_gives_hadamard {N : ℕ} (hN : 0<N)
    (S : Finset (Fin N → Bool)) (hcard : S.card=N)
    (horth : ∀ x∈S,∀ y∈S,x≠y → (∑ j,modularBitSign (x j)*modularBitSign (y j))=0) :
    ∃ H : Matrix (Fin N) (Fin N) ℝ,Matrix.IsHadamard H ∧
      (∀ x∈S,∃ i : Fin N,∀ j,H i j=(modularBitSign (x j) : ℝ)) ∧
      ∀ i : Fin N,∃ x∈S,∀ j,H i j=(modularBitSign (x j) : ℝ) := by
  classical
  letI : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  have hs : Fintype.card S=N := by simpa only [Fintype.card_coe] using hcard
  let e : S ≃ Fin N := (Fintype.equivFin S).trans (finCongr hs)
  let P := signFamilyMatrix S
  have hp := signFamilyMatrix_partial S horth
  let H : Matrix (Fin N) (Fin N) ℝ := P.submatrix e.symm id
  have hsign : IsSignMatrix H := fun i j => hp.1 (e.symm i) j
  have hGram : H*Hᵀ=(N : ℝ) • (1 : Matrix (Fin N) (Fin N) ℝ) := by
    ext i k
    have hh := congrArg (fun M => M (e.symm i) (e.symm k)) hp.2
    by_cases hik : i=k
    · subst k
      simpa [H,Matrix.mul_apply,Matrix.transpose_apply,Matrix.submatrix_apply,
        Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,Fintype.card_fin] using hh
    · have hne : e.symm i≠e.symm k := fun heq => hik (e.symm.injective heq)
      simpa [H,Matrix.mul_apply,Matrix.transpose_apply,Matrix.submatrix_apply,
        Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,Fintype.card_fin,hik,hne] using hh
  refine ⟨H,?_,?_,?_⟩
  · apply isHadamard_mathlib
    exact ⟨hsign,by simpa only [Fintype.card_fin] using hGram⟩
  · intro x hx
    refine ⟨e ⟨x,hx⟩,?_⟩
    intro j
    simp [H,P,signFamilyMatrix]
  · intro i
    exact ⟨(e.symm i).val,(e.symm i).property,fun _ => rfl⟩

end CompletionTheory
