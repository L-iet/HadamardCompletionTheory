/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.GeneratorMoments
@[expose] public section
set_option maxHeartbeats 2000000
namespace CompletionTheory
open Module Submodule
open scoped Classical

noncomputable def retainedTupleRank {K V α : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (G : Submodule K V) (v : α → V) {k : ℕ} (t : Fin k → α) : ℕ :=
  finrank K ↥(G ⊔ tupleVectorSpan (K := K) v t)-finrank K G

theorem retainedTupleRank_bounds {K V α : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (G : Submodule K V) (v : α → V) (hv : ∀ a,v a∉G)
    {k : ℕ} (t : Fin (k+1) → α) :
    1≤retainedTupleRank G v t ∧ retainedTupleRank G v t≤k+1 := by
  let S := G ⊔ tupleVectorSpan (K := K) v t
  have hle : G≤S := le_sup_left
  have hne : G≠S := by
    intro heq
    apply hv (t 0)
    rw [heq]
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨0,rfl⟩)
  have hlo := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle hne)
  have hspan := finrank_range_le_card (R := K) (fun i => v (t i))
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq G (tupleVectorSpan (K := K) v t)
  change finrank K S+finrank K ↥(G ⊓ tupleVectorSpan (K := K) v t)=_ at hsup
  change finrank K (tupleVectorSpan (K := K) v t)≤Fintype.card (Fin (k+1)) at hspan
  simp only [Fintype.card_fin] at hspan
  dsimp only [retainedTupleRank]
  change 1≤finrank K S-finrank K G ∧ finrank K S-finrank K G≤k+1
  omega

theorem finite_rank_three_sum {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P]
    (r : α → ℕ) (f : ℕ → ℕ) (hr : ∀ a,1≤r a ∧ r a≤3) :
    (∑ a,if P a then f (r a) else 0)=
      Nat.card {a : α // P a ∧ r a=1}*f 1+
      Nat.card {a : α // P a ∧ r a=2}*f 2+
      Nat.card {a : α // P a ∧ r a=3}*f 3 := by
  classical
  have hc (j : ℕ) : Nat.card {a : α // P a ∧ r a=j}=∑ a,if P a ∧ r a=j then (1 : ℕ) else 0 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [hc 1,hc 2,hc 3,Finset.sum_mul,Finset.sum_mul,Finset.sum_mul,
    ← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hp : P a
  · have hcases : r a=1 ∨ r a=2 ∨ r a=3 := by have hh:=hr a;omega
    rcases hcases with h|h|h <;> simp [hp,h]
  · simp [hp]

noncomputable def retainedTupleMomentCount {K V α : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (G : Submodule K V)
    (v : α → V) (k r : ℕ) : ℕ :=
  Nat.card {t : Fin k → α //
    (G ⊔ tupleVectorSpan (K := K) v t)≤B.orthogonal (G ⊔ tupleVectorSpan (K := K) v t) ∧ retainedTupleRank G v t=r}

theorem retained_generator_third_moment_count {K V α : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype α]
    (htwo : (2 : K)≠0) (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (G : Submodule K V) [Fintype {D : Submodule K V // D=B.orthogonal D ∧ G≤D}]
    (C : Submodule K V) (hC : C=B.orthogonal C) (h : ℕ) (hrank : finrank K G+h=finrank K C)
    (v : α → V) (hv : ∀ a,v a∉G) :
    (∑ D : {D : Submodule K V // D=B.orthogonal D ∧ G≤D}, (Nat.card {a : α // v a∈D.val})^3)=
      retainedTupleMomentCount B G v 3 1*splitGeneratorCount (Nat.card K) (h-1)+
      retainedTupleMomentCount B G v 3 2*splitGeneratorCount (Nat.card K) (h-2)+
      retainedTupleMomentCount B G v 3 3*splitGeneratorCount (Nat.card K) (h-3) := by
  classical
  rw [split_generator_retained_vector_moments htwo B hB hnd G C hC v 3]
  have heq (t : Fin 3 → α) :
      finrank K C-finrank K ↥(G ⊔ tupleVectorSpan (K := K) v t)=h-retainedTupleRank G v t := by
    have hle : finrank K G≤finrank K ↥(G ⊔ tupleVectorSpan (K := K) v t) := Submodule.finrank_mono le_sup_left
    dsimp only [retainedTupleRank]
    omega
  simp_rw [heq]
  exact finite_rank_three_sum
    (fun t : Fin 3 → α => (G ⊔ tupleVectorSpan (K := K) v t)≤B.orthogonal (G ⊔ tupleVectorSpan (K := K) v t))
    (retainedTupleRank G v) (fun r => splitGeneratorCount (Nat.card K) (h-r))
    (fun t => retainedTupleRank_bounds G v hv t)

theorem retained_isotropic_tuple_rank_le {K V α : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (C G : Submodule K V) (hC : C=B.orthogonal C) (h : ℕ) (hrank : finrank K G+h=finrank K C)
    (v : α → V) {k : ℕ} (t : Fin k → α)
    (hS : (G ⊔ tupleVectorSpan (K := K) v t)≤B.orthogonal (G ⊔ tupleVectorSpan (K := K) v t)) :
    retainedTupleRank G v t≤h := by
  obtain ⟨D,hD,hSD⟩ := self_orthogonal_subspace_extends_self_dual B hB hnd C _ hC hS
  have hd := self_dual_subspace_same_finrank B hnd C D hC hD
  have hle := Submodule.finrank_mono hSD
  dsimp only [retainedTupleRank]
  omega

theorem retained_rank_three_count_vanishes_at_two {K V α : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (C G : Submodule K V) (hC : C=B.orthogonal C) (hrank : finrank K G+2=finrank K C)
    (v : α → V) : retainedTupleMomentCount B G v 3 3=0 := by
  letI : IsEmpty {t : Fin 3 → α //
      (G ⊔ tupleVectorSpan (K := K) v t)≤B.orthogonal (G ⊔ tupleVectorSpan (K := K) v t) ∧ retainedTupleRank G v t=3} := ⟨by
    intro t
    have ht := retained_isotropic_tuple_rank_le B hB hnd C G hC 2 hrank v t.val t.property.1
    have hh := t.property.2
    omega⟩
  unfold retainedTupleMomentCount
  exact Nat.card_of_isEmpty

theorem splitGeneratorCount_three_step_ratio (q h : ℕ) (hh : 3≤h) :
    (splitGeneratorCount q (h-3) : ℝ)/(splitGeneratorCount q h : ℝ)=
      1/(((q : ℝ)^(h-1)+1)*((q : ℝ)^(h-2)+1)*((q : ℝ)^(h-3)+1)) := by
  have hr := splitGeneratorCount_ratio q (h-3) 3
  have heq : h-3+3=h := by omega
  have heq' : h-3+1=h-2 := by omega
  have heq'' : h-3+2=h-1 := by omega
  rw [heq] at hr
  simp only [Finset.prod_range_succ,Finset.prod_range_zero,one_mul,Nat.add_zero,heq',heq''] at hr
  rw [hr]
  congr 1
  ring

theorem retained_generator_third_moment {K V α : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype α]
    (htwo : (2 : K)≠0) (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (G : Submodule K V) (hG : G≤B.orthogonal G)
    [Fintype {D : Submodule K V // D=B.orthogonal D ∧ G≤D}]
    (C : Submodule K V) (hC : C=B.orthogonal C) (h : ℕ) (hrank : finrank K G+h=finrank K C) (hh : 3≤h)
    (v : α → V) (hv : ∀ a,v a∉G) :
    (((∑ D : {D : Submodule K V // D=B.orthogonal D ∧ G≤D}, (Nat.card {a : α // v a∈D.val})^3) : ℕ) : ℝ)/
      (Nat.card {D : Submodule K V // D=B.orthogonal D ∧ G≤D} : ℝ)=
      (retainedTupleMomentCount B G v 3 1 : ℝ)/((Nat.card K : ℝ)^(h-1)+1)+
      (retainedTupleMomentCount B G v 3 2 : ℝ)/(((Nat.card K : ℝ)^(h-1)+1)*((Nat.card K : ℝ)^(h-2)+1))+
      (retainedTupleMomentCount B G v 3 3 : ℝ)/(((Nat.card K : ℝ)^(h-1)+1)*((Nat.card K : ℝ)^(h-2)+1)*((Nat.card K : ℝ)^(h-3)+1)) := by
  have hc := retained_generator_third_moment_count htwo B hB hnd G C hC h hrank v hv
  have hd := split_form_retained_subspace_count htwo B hB hnd C G hC hG
  have hr : finrank K C-finrank K G=h := by omega
  rw [hc,hd,hr]
  simp only [Nat.cast_add,Nat.cast_mul,add_div,mul_div_assoc]
  rw [splitGeneratorCount_one_step_ratio _ h (by omega),splitGeneratorCount_two_step_ratio _ h (by omega),
    splitGeneratorCount_three_step_ratio _ h hh]
  ring

theorem retained_generator_third_moment_at_two {K V α : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype α]
    (htwo : (2 : K)≠0) (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (G : Submodule K V) (hG : G≤B.orthogonal G)
    [Fintype {D : Submodule K V // D=B.orthogonal D ∧ G≤D}]
    (C : Submodule K V) (hC : C=B.orthogonal C) (hrank : finrank K G+2=finrank K C)
    (v : α → V) (hv : ∀ a,v a∉G) :
    retainedTupleMomentCount B G v 3 3=0 ∧
    (((∑ D : {D : Submodule K V // D=B.orthogonal D ∧ G≤D}, (Nat.card {a : α // v a∈D.val})^3) : ℕ) : ℝ)/
      (Nat.card {D : Submodule K V // D=B.orthogonal D ∧ G≤D} : ℝ)=
      (retainedTupleMomentCount B G v 3 1 : ℝ)/((Nat.card K : ℝ)+1)+
      (retainedTupleMomentCount B G v 3 2 : ℝ)/(((Nat.card K : ℝ)+1)*2) := by
  have hz := retained_rank_three_count_vanishes_at_two B hB hnd C G hC hrank v
  refine ⟨hz,?_⟩
  have hc := retained_generator_third_moment_count htwo B hB hnd G C hC 2 hrank v hv
  have hd := split_form_retained_subspace_count htwo B hB hnd C G hC hG
  have hr : finrank K C-finrank K G=2 := by omega
  rw [hz,zero_mul,add_zero] at hc
  rw [hc,hd,hr]
  simp only [Nat.cast_add,Nat.cast_mul,add_div,mul_div_assoc]
  rw [splitGeneratorCount_one_step_ratio _ 2 (by omega),splitGeneratorCount_two_step_ratio _ 2 (by omega)]
  norm_num
  field_simp
  all_goals ring

theorem finite_fiber_tuple_sum {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (label : α → β) (P : (ι → β) → Prop) [DecidablePred P] :
    (∑ u : ι → β,if P u then ∏ i,Nat.card {a : α // label a=u i} else 0)=
      Nat.card {t : ι → α // P (fun i => label (t i))} := by
  classical
  let g : (ι → α) → (ι → β) := fun t i => label (t i)
  have hf (u : ι → β) : Nat.card {t : ι → α // g t=u}=∏ i,Nat.card {a : α // label a=u i} := by
    let e : {t : ι → α // g t=u} ≃ {t : ι → α // ∀ i,label (t i)=u i} :=
      Equiv.subtypeEquivRight (fun t => funext_iff)
    rw [Nat.card_congr (e.trans (Equiv.subtypePiEquivPi (p := fun i a => label a=u i)))]
    simp only [Nat.card_eq_fintype_card,Fintype.card_pi]
  have hh (u : ι → β) : (Finset.univ.filter (fun t : ι → α => g t=u)).card=
      ∏ i,Nat.card {a : α // label a=u i} := by
    rw [← hf]
    simp [Nat.card_eq_fintype_card,Fintype.card_subtype]
  have hs := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (ι → α))
    (Finset.univ.filter P) g
  simp_rw [hh] at hs
  simpa [Finset.sum_filter,Nat.card_eq_fintype_card,Fintype.card_subtype] using hs

theorem retained_tuple_span_as_point_join {K V α : Type*} [Field K] [AddCommGroup V] [Module K V]
    (G : Submodule K V) (v : α → V) {k : ℕ} (t : Fin (k+1) → α) :
    G ⊔ tupleVectorSpan (K := K) v t=⨆ i : Fin (k+1),G ⊔ Submodule.span K {v (t i)} := by
  apply le_antisymm
  · apply sup_le
    · exact le_trans le_sup_left (le_iSup (fun i => G ⊔ Submodule.span K {v (t i)}) 0)
    · apply Submodule.span_le.mpr
      rintro x ⟨i,rfl⟩
      exact Submodule.mem_iSup_of_mem i (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  · apply iSup_le
    intro i
    apply sup_le le_sup_left
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr
      (Submodule.mem_sup_right (Submodule.subset_span ⟨i,rfl⟩))

theorem retained_tuple_count_as_weighted_points {K V α : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype α] [Fintype (Submodule K V)]
    (B : LinearMap.BilinForm K V) (G : Submodule K V) (v : α → V) (k r : ℕ) :
    let label : α → Submodule K V := fun a => G ⊔ Submodule.span K {v a}
    let w : Submodule K V → ℕ := fun L => Nat.card {a : α // label a=L}
    retainedTupleMomentCount B G v (k+1) r=
      ∑ u : Fin (k+1) → Submodule K V,
        if (⨆ i,u i)≤B.orthogonal (⨆ i,u i) ∧ finrank K ↥(⨆ i,u i)-finrank K G=r then
          ∏ i,w (u i) else 0 := by
  classical
  let label : α → Submodule K V := fun a => G ⊔ Submodule.span K {v a}
  change retainedTupleMomentCount B G v (k+1) r=
    ∑ u : Fin (k+1) → Submodule K V,
      if (⨆ i,u i)≤B.orthogonal (⨆ i,u i) ∧ finrank K ↥(⨆ i,u i)-finrank K G=r then
        ∏ i,Nat.card {a : α // label a=u i} else 0
  refine Eq.trans ?_ (finite_fiber_tuple_sum label (fun u : Fin (k+1) → Submodule K V =>
    (⨆ i,u i)≤B.orthogonal (⨆ i,u i) ∧ finrank K ↥(⨆ i,u i)-finrank K G=r)).symm
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro t
  dsimp only [retainedTupleRank]
  rw [← retained_tuple_span_as_point_join G v t]

theorem actual_sign_third_moment_formulas {p : ℕ} [Fact p.Prime] (hodd : p%2=1)
    (G C : Submodule (ZMod p) (Fin (4*p) → ZMod p))
    [Fintype {D : Submodule (ZMod p) (Fin (4*p) → ZMod p) //
      D=(coordinateDotForm (ZMod p) (4*p)).orthogonal D ∧ G≤D}]
    (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C) (hGC : G≤C)
    (h : ℕ) (hrank : finrank (ZMod p) G+h=2*p) :
    let B := coordinateDotForm (ZMod p) (4*p)
    let U := codeSignCandidates (B.orthogonal G)
    let A := codeSignCandidates G
    let S := U \ A
    let v : S → (Fin (4*p) → ZMod p) := fun x j => (modularBitSign (x.val j) : ZMod p)
    let R : ℕ → ℕ := fun r => retainedTupleMomentCount B G v 3 r
    let Ω := {D : Submodule (ZMod p) (Fin (4*p) → ZMod p) // D=B.orthogonal D ∧ G≤D}
    let Y : Ω → ℕ := fun D => (codeSignCandidates D.val).card-A.card
    (3≤h → (((∑ D : Ω,Y D^3 : ℕ) : ℝ)/(Nat.card Ω : ℝ))=
      (R 1 : ℝ)/((p : ℝ)^(h-1)+1)+(R 2 : ℝ)/(((p : ℝ)^(h-1)+1)*((p : ℝ)^(h-2)+1))+
      (R 3 : ℝ)/(((p : ℝ)^(h-1)+1)*((p : ℝ)^(h-2)+1)*((p : ℝ)^(h-3)+1))) ∧
    (h=2 → R 3=0 ∧ (((∑ D : Ω,Y D^3 : ℕ) : ℝ)/(Nat.card Ω : ℝ))=
      (R 1 : ℝ)/((p : ℝ)+1)+(R 2 : ℝ)/(((p : ℝ)+1)*2)) := by
  classical
  let B := coordinateDotForm (ZMod p) (4*p)
  let U := codeSignCandidates (B.orthogonal G)
  let A := codeSignCandidates G
  let S := U \ A
  let v : S → (Fin (4*p) → ZMod p) := fun x j => (modularBitSign (x.val j) : ZMod p)
  have hp : p.Prime := Fact.out
  have htwo : (2 : ZMod p)≠0 := by
    intro hz
    have hd : p∣2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have hp2 : p=2 := (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left hp.ne_one
    omega
  have hG : G≤B.orthogonal G := by
    intro x hx y hy
    exact ((SetLike.ext_iff.mp hC x).mp (hGC hx)) y (hGC hy)
  have hhalf : finrank (ZMod p) C=2*p := by
    have hd := B.finrank_add_finrank_orthogonal' C
    rw [← hC,(coordinateDotForm_nondegenerate (ZMod p) (4*p)).ker_eq_bot,
      inf_bot_eq,finrank_bot,add_zero] at hd
    simp only [Module.finrank_pi_fintype,Module.finrank_self,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,Nat.cast_id] at hd
    omega
  have hv (x : S) : v x∉G := by
    intro hx
    exact (Finset.mem_sdiff.mp x.property).2 (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,(Finset.mem_filter.mp (Finset.mem_sdiff.mp x.property).1).2.1,hx⟩)
  have hcount (D : {D : Submodule (ZMod p) (Fin (4*p) → ZMod p) // D=B.orthogonal D ∧ G≤D}) :
      Nat.card {x : S // v x∈D.val}=(codeSignCandidates D.val).card-A.card := by
    have hpred (x : S) : v x∈D.val ↔ x.val∈codeSignCandidates D.val := by
      have hxfirst := (Finset.mem_filter.mp (Finset.mem_sdiff.mp x.property).1).2.1
      simp only [codeSignCandidates,Finset.mem_filter,Finset.mem_univ,true_and,hxfirst,true_and]
      rfl
    rw [Nat.card_congr (Equiv.subtypeEquivRight hpred)]
    apply finite_subset_count_via_outside U A (codeSignCandidates D.val)
    · exact codeSignCandidates_mono G D.val D.property.2
    · apply codeSignCandidates_mono
      intro x hx y hy
      exact ((SetLike.ext_iff.mp D.property.1 x).mp hx) y (D.property.2 hy)
  have hq : Nat.card (ZMod p)=p := by simp only [Nat.card_eq_fintype_card,ZMod.card]
  constructor
  · intro hh
    have hm := retained_generator_third_moment htwo B (coordinateDotForm_symm _ _)
      (coordinateDotForm_nondegenerate _ _) G hG C hC h (by omega) hh v hv
    simp_rw [hcount] at hm
    rw [hq] at hm
    exact hm
  · intro heq
    have hm := retained_generator_third_moment_at_two htwo B (coordinateDotForm_symm _ _)
      (coordinateDotForm_nondegenerate _ _) G hG C hC (by omega) v hv
    simp_rw [hcount] at hm
    rw [hq] at hm
    exact hm

theorem actual_sign_third_moment_certificate {p : ℕ} [Fact p.Prime]
    (G C : Submodule (ZMod p) (Fin (4*p) → ZMod p))
    [Fintype {D : Submodule (ZMod p) (Fin (4*p) → ZMod p) //
      D=(coordinateDotForm (ZMod p) (4*p)).orthogonal D ∧ G≤D}]
    (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C) (hGC : G≤C) :
    let Ω := {D : Submodule (ZMod p) (Fin (4*p) → ZMod p) //
      D=(coordinateDotForm (ZMod p) (4*p)).orthogonal D ∧ G≤D}
    let b := (codeSignCandidates G).card
    let Y : Ω → ℕ := fun D => (codeSignCandidates D.val).card-b
    0<(((∑ D : Ω,Y D^2 : ℕ) : ℝ)/(Nat.card Ω : ℝ)) →
      ∃ D : Ω,b+Nat.ceil
        ((((∑ E : Ω,Y E^3 : ℕ) : ℝ)/(Nat.card Ω : ℝ))/
         (((∑ E : Ω,Y E^2 : ℕ) : ℝ)/(Nat.card Ω : ℝ)))≤(codeSignCandidates D.val).card := by
  classical
  let Ω := {D : Submodule (ZMod p) (Fin (4*p) → ZMod p) //
    D=(coordinateDotForm (ZMod p) (4*p)).orthogonal D ∧ G≤D}
  let b := (codeSignCandidates G).card
  let Y : Ω → ℕ := fun D => (codeSignCandidates D.val).card-b
  letI : Nonempty Ω := ⟨⟨C,hC,hGC⟩⟩
  change 0<(((∑ D : Ω,Y D^2 : ℕ) : ℝ)/(Nat.card Ω : ℝ)) → _
  intro hpos
  have hn : (Nat.card Ω : ℝ)≠0 := by
    intro hz
    rw [hz,div_zero] at hpos
    exact (lt_irrefl (0 : ℝ)) hpos
  have hsN : 0<∑ D : Ω,Y D^2 := by
    by_contra hnot
    have hz : (∑ D : Ω,Y D^2)=0 := Nat.eq_zero_of_not_pos hnot
    rw [hz,Nat.cast_zero,zero_div] at hpos
    exact (lt_irrefl (0 : ℝ)) hpos
  obtain ⟨D,hD⟩ := finite_moment_ratio_certificate Y 2 hsN
  have heq :
      ((((∑ E : Ω,Y E^3 : ℕ) : ℝ)/(Nat.card Ω : ℝ))/
       (((∑ E : Ω,Y E^2 : ℕ) : ℝ)/(Nat.card Ω : ℝ)))=
      (((∑ E : Ω,Y E^3 : ℕ) : ℝ)/((∑ E : Ω,Y E^2 : ℕ) : ℝ)) := by
    exact div_div_div_cancel_right₀ hn _ _
  refine ⟨D,?_⟩
  rw [heq]
  have hAD : b≤(codeSignCandidates D.val).card :=
    Finset.card_le_card (codeSignCandidates_mono G D.val D.property.2)
  simp only [Nat.reduceAdd] at hD
  change Nat.ceil (((∑ E : Ω,Y E^3 : ℕ) : ℝ)/((∑ E : Ω,Y E^2 : ℕ) : ℝ))≤
    (codeSignCandidates D.val).card-b at hD
  simpa only [Nat.add_comm] using (Nat.le_sub_iff_add_le hAD).mp hD

end CompletionTheory
