/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.GeneratorCounts
public import CompletionTheory.GridRepair
public import Mathlib.Algebra.BigOperators.Ring.Finset
@[expose] public section
namespace CompletionTheory
open Module Submodule
open scoped Classical

theorem finite_incidence_all_moments {α β : Type*} [Fintype α] [Fintype β]
    (P : α → β → Prop) [DecidableRel P] (k : ℕ) :
    (∑ a, (∑ b, if P a b then (1 : ℕ) else 0)^k)=
      ∑ t : Fin k → β, (Finset.univ.filter (fun a => ∀ i, P a (t i))).card := by
  classical
  simp_rw [Fintype.sum_pow]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  have hp (a : α) : (∏ i,if P a (t i) then (1 : ℕ) else 0)=if (∀ i,P a (t i)) then 1 else 0 := by
    by_cases h : ∀ i,P a (t i)
    · simp [h]
    · obtain ⟨i,hi⟩ := not_forall.mp h
      have hz : (∏ j,if P a (t j) then (1 : ℕ) else 0)=0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
      simp [hz,h]
  simp_rw [hp]
  simp

def tupleVectorSpan {K V α : Type*} [Field K] [AddCommGroup V] [Module K V]
    (v : α → V) {k : ℕ} (t : Fin k → α) : Submodule K V :=
  Submodule.span K (Set.range (fun i => v (t i)))

theorem tupleVectorSpan_le_iff {K V α : Type*} [Field K] [AddCommGroup V] [Module K V]
    (v : α → V) {k : ℕ} (t : Fin k → α) (D : Submodule K V) :
    tupleVectorSpan (K := K) v t≤D ↔ ∀ i,v (t i)∈D := by
  rw [tupleVectorSpan,Submodule.span_le]
  constructor
  · intro h i;exact h ⟨i,rfl⟩
  · rintro h x ⟨i,rfl⟩;exact h i

theorem split_generator_all_sign_moments {K V α : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype α]
    (htwo : (2 : K)≠0) (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    [Fintype (selfDualSubspaces B)]
    (C : Submodule K V) (hC : C=B.orthogonal C) (v : α → V) (k : ℕ) :
    (∑ D : selfDualSubspaces B, (Nat.card {a : α // v a∈D.val})^k)=
      ∑ t : Fin k → α,
        if tupleVectorSpan (K := K) v t≤B.orthogonal (tupleVectorSpan (K := K) v t) then
          splitGeneratorCount (Nat.card K) (finrank K C-finrank K (tupleVectorSpan (K := K) v t)) else 0 := by
  classical
  have hcount (D : selfDualSubspaces B) : Nat.card {a : α // v a∈D.val}=
      ∑ a,if v a∈D.val then (1 : ℕ) else 0 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]
  simp_rw [hcount]
  rw [finite_incidence_all_moments (fun (D : selfDualSubspaces B) a => v a∈D.val) k]
  apply Finset.sum_congr rfl
  intro t ht
  let S := tupleVectorSpan (K := K) v t
  let e : {D : selfDualSubspaces B // ∀ i,v (t i)∈D.val} ≃
      {D : Submodule K V // D=B.orthogonal D ∧ S≤D} := {
    toFun := fun D => ⟨D.val.val,D.val.property,(tupleVectorSpan_le_iff v t D.val.val).mpr D.property⟩
    invFun := fun D => ⟨⟨D.val,D.property.1⟩,(tupleVectorSpan_le_iff v t D.val).mp D.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have heq : (Finset.univ.filter (fun D : selfDualSubspaces B => ∀ i,v (t i)∈D.val)).card=
      Nat.card {D : Submodule K V // D=B.orthogonal D ∧ S≤D} := by
    rw [← Nat.card_congr e]
    simp [Nat.card_eq_fintype_card,Fintype.card_subtype]
  rw [heq]
  by_cases hS : S≤B.orthogonal S
  · rw [if_pos hS]
    exact split_form_retained_subspace_count htwo B hB hnd C S hC hS
  · rw [if_neg hS]
    exact non_isotropic_subspace_no_self_dual_extension B S hS

theorem split_generator_retained_vector_moments {K V α : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype α]
    (htwo : (2 : K)≠0) (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (G : Submodule K V) [Fintype {D : Submodule K V // D=B.orthogonal D ∧ G≤D}]
    (C : Submodule K V) (hC : C=B.orthogonal C) (v : α → V) (k : ℕ) :
    (∑ D : {D : Submodule K V // D=B.orthogonal D ∧ G≤D}, (Nat.card {a : α // v a∈D.val})^k)=
      ∑ t : Fin k → α,
        if (G ⊔ tupleVectorSpan (K := K) v t)≤B.orthogonal (G ⊔ tupleVectorSpan (K := K) v t) then
          splitGeneratorCount (Nat.card K) (finrank K C-finrank K ↥(G ⊔ tupleVectorSpan (K := K) v t)) else 0 := by
  classical
  let A := {D : Submodule K V // D=B.orthogonal D ∧ G≤D}
  have hcount (D : A) : Nat.card {a : α // v a∈D.val}=
      ∑ a,if v a∈D.val then (1 : ℕ) else 0 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]
  simp_rw [hcount]
  rw [finite_incidence_all_moments (fun (D : A) a => v a∈D.val) k]
  apply Finset.sum_congr rfl
  intro t ht
  let S := G ⊔ tupleVectorSpan (K := K) v t
  let e : {D : A // ∀ i,v (t i)∈D.val} ≃
      {D : Submodule K V // D=B.orthogonal D ∧ S≤D} := {
    toFun := fun D => ⟨D.val.val,D.val.property.1,
      sup_le D.val.property.2 ((tupleVectorSpan_le_iff v t D.val.val).mpr D.property)⟩
    invFun := fun D => ⟨⟨D.val,D.property.1,le_trans le_sup_left D.property.2⟩,
      (tupleVectorSpan_le_iff v t D.val).mp (le_trans le_sup_right D.property.2)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have heq : (Finset.univ.filter (fun D : A => ∀ i,v (t i)∈D.val)).card=
      Nat.card {D : Submodule K V // D=B.orthogonal D ∧ S≤D} := by
    rw [← Nat.card_congr e]
    simp [Nat.card_eq_fintype_card,Fintype.card_subtype]
  rw [heq]
  by_cases hS : S≤B.orthogonal S
  · rw [if_pos hS]
    exact split_form_retained_subspace_count htwo B hB hnd C S hC hS
  · rw [if_neg hS]
    exact non_isotropic_subspace_no_self_dual_extension B S hS

theorem retained_actual_sign_all_moments {p : ℕ} [Fact p.Prime] (hodd : p%2=1)
    (G C : Submodule (ZMod p) (Fin (4*p) → ZMod p))
    [Fintype {D : Submodule (ZMod p) (Fin (4*p) → ZMod p) //
      D=(coordinateDotForm (ZMod p) (4*p)).orthogonal D ∧ G≤D}]
    (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C) (k : ℕ) :
    let B := coordinateDotForm (ZMod p) (4*p)
    let U := codeSignCandidates (B.orthogonal G)
    let A := codeSignCandidates G
    let S := U \ A
    let v : S → (Fin (4*p) → ZMod p) := fun x j => (modularBitSign (x.val j) : ZMod p)
    (∑ D : {D : Submodule (ZMod p) (Fin (4*p) → ZMod p) // D=B.orthogonal D ∧ G≤D},
      ((codeSignCandidates D.val).card-A.card)^k)=
      ∑ t : Fin k → S,
        if (G ⊔ tupleVectorSpan (K := ZMod p) v t)≤B.orthogonal (G ⊔ tupleVectorSpan (K := ZMod p) v t) then
          splitGeneratorCount p (finrank (ZMod p) C-finrank (ZMod p) ↥(G ⊔ tupleVectorSpan (K := ZMod p) v t)) else 0 := by
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
  have hh := split_generator_retained_vector_moments htwo B (coordinateDotForm_symm _ _)
    (coordinateDotForm_nondegenerate _ _) G C hC v k
  simp_rw [hcount] at hh
  simpa only [Nat.card_eq_fintype_card,ZMod.card] using hh

theorem retained_generator_single_vector_count {K V : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (htwo : (2 : K)≠0) (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (C G : Submodule K V) (hC : C=B.orthogonal C) (hG : G≤B.orthogonal G)
    (v : V) (hvG : v∈B.orthogonal G) (hv : v∉G) (hvv : B v v=0) :
    Nat.card {D : Submodule K V // D=B.orthogonal D ∧ G≤D ∧ v∈D}=
      splitGeneratorCount (Nat.card K) (finrank K C-finrank K G-1) := by
  let S := G ⊔ Submodule.span K {v}
  have hS : S≤B.orthogonal S := span_with_retained_self_orthogonal B hB G hG {v}
    (by intro x hx;rcases Set.mem_singleton_iff.mp hx with rfl;exact hvG)
    (by intro x hx y hy;rcases Set.mem_singleton_iff.mp hx with rfl;rcases Set.mem_singleton_iff.mp hy with rfl;exact hvv)
  let e : {D : Submodule K V // D=B.orthogonal D ∧ G≤D ∧ v∈D} ≃
      {D : Submodule K V // D=B.orthogonal D ∧ S≤D} := {
    toFun := fun D => ⟨D.val,D.property.1,sup_le D.property.2.1
      ((Submodule.span_singleton_le_iff_mem v D.val).mpr D.property.2.2)⟩
    invFun := fun D => ⟨D.val,D.property.1,le_trans le_sup_left D.property.2,
      D.property.2 (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v))⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e,split_form_retained_subspace_count htwo B hB hnd C S hC hS]
  have hr : finrank K S=finrank K G+1 := Submodule.finrank_sup_span_singleton hv
  rw [hr,Nat.sub_add_eq]

theorem retained_generator_first_moment_count {K V α : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype α]
    (htwo : (2 : K)≠0) (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (C G : Submodule K V) (hC : C=B.orthogonal C) (hG : G≤B.orthogonal G)
    [Fintype {D : Submodule K V // D=B.orthogonal D ∧ G≤D}]
    (v : α → V) (hvG : ∀ a,v a∈B.orthogonal G) (hv : ∀ a,v a∉G) (hvv : ∀ a,B (v a) (v a)=0) :
    (∑ D : {D : Submodule K V // D=B.orthogonal D ∧ G≤D}, Nat.card {a : α // v a∈D.val})=
      Fintype.card α*splitGeneratorCount (Nat.card K) (finrank K C-finrank K G-1) := by
  classical
  let A := {D : Submodule K V // D=B.orthogonal D ∧ G≤D}
  have hcount (D : A) : Nat.card {a : α // v a∈D.val}=
      (Finset.univ.filter (fun a => v a∈D.val)).card := by simp [Nat.card_eq_fintype_card,Fintype.card_subtype]
  simp_rw [hcount]
  rw [sum_filter_card_comm]
  have heq (a : α) : (Finset.univ.filter (fun D : A => v a∈D.val)).card=
      splitGeneratorCount (Nat.card K) (finrank K C-finrank K G-1) := by
    let e : {D : A // v a∈D.val} ≃ {D : Submodule K V // D=B.orthogonal D ∧ G≤D ∧ v a∈D} := {
      toFun := fun D => ⟨D.val.val,D.val.property.1,D.val.property.2,D.property⟩
      invFun := fun D => ⟨⟨D.val,D.property.1,D.property.2.1⟩,D.property.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    have hc := retained_generator_single_vector_count htwo B hB hnd C G hC hG (v a) (hvG a) (hv a) (hvv a)
    rw [← Nat.card_congr e] at hc
    simpa [Nat.card_eq_fintype_card,Fintype.card_subtype] using hc
  change (∑ a : α,(Finset.univ.filter (fun D : A => v a∈D.val)).card)=_
  simp_rw [heq]
  simp

theorem splitGeneratorCount_one_step_ratio (q h : ℕ) (hh : 1≤h) :
    (splitGeneratorCount q (h-1) : ℝ)/(splitGeneratorCount q h : ℝ)=
      1/((q : ℝ)^(h-1)+1) := by
  have hr := splitGeneratorCount_ratio q (h-1) 1
  have heq : h-1+1=h := by omega
  simpa only [heq,Finset.prod_range_one,Nat.add_zero] using hr

theorem retained_generator_first_moment {K V α : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype α]
    (htwo : (2 : K)≠0) (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (C G : Submodule K V) (hC : C=B.orthogonal C) (hG : G≤B.orthogonal G)
    [Fintype {D : Submodule K V // D=B.orthogonal D ∧ G≤D}]
    (h : ℕ) (hrank : finrank K G+h=finrank K C) (hh : 1≤h)
    (v : α → V) (hvG : ∀ a,v a∈B.orthogonal G) (hv : ∀ a,v a∉G) (hvv : ∀ a,B (v a) (v a)=0) :
    (((∑ D : {D : Submodule K V // D=B.orthogonal D ∧ G≤D}, Nat.card {a : α // v a∈D.val}) : ℕ) : ℝ)/
      (Nat.card {D : Submodule K V // D=B.orthogonal D ∧ G≤D} : ℝ)=
        (Fintype.card α : ℝ)/((Nat.card K : ℝ)^(h-1)+1) := by
  have hc := retained_generator_first_moment_count htwo B hB hnd C G hC hG v hvG hv hvv
  have hd := split_form_retained_subspace_count htwo B hB hnd C G hC hG
  have hr : finrank K C-finrank K G=h := by omega
  rw [hc,hd,hr,Nat.cast_mul]
  rw [mul_div_assoc,splitGeneratorCount_one_step_ratio _ h hh]
  ring

theorem retained_pair_span_self_orthogonal {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (G : Submodule K V) (hG : G≤B.orthogonal G) (x y : V)
    (hxG : x∈B.orthogonal G) (hyG : y∈B.orthogonal G) (hxx : B x x=0) (hyy : B y y=0) :
    ((G ⊔ Submodule.span K {x}) ⊔ Submodule.span K {y})≤
      B.orthogonal ((G ⊔ Submodule.span K {x}) ⊔ Submodule.span K {y}) ↔ B x y=0 := by
  constructor
  · intro h
    have hx : x∈((G ⊔ Submodule.span K {x}) ⊔ Submodule.span K {y}) :=
      Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))
    have hy : y∈((G ⊔ Submodule.span K {x}) ⊔ Submodule.span K {y}) :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)
    exact h hy x hx
  · intro hxy
    have hS : G ⊔ Submodule.span K {x}≤B.orthogonal (G ⊔ Submodule.span K {x}) :=
      span_with_retained_self_orthogonal B hB G hG {x}
        (by intro z hz;rcases Set.mem_singleton_iff.mp hz with rfl;exact hxG)
        (by intro z hz t ht;rcases Set.mem_singleton_iff.mp hz with rfl;rcases Set.mem_singleton_iff.mp ht with rfl;exact hxx)
    have hyS : y∈B.orthogonal (G ⊔ Submodule.span K {x}) := by
      have hk : G ⊔ Submodule.span K {x}≤LinearMap.ker (B.flip y) :=
        sup_le (fun z hz => hyG z hz) ((Submodule.span_singleton_le_iff_mem x _).mpr hxy)
      exact fun z hz => hk hz
    exact span_with_retained_self_orthogonal B hB _ hS {y}
      (by intro z hz;rcases Set.mem_singleton_iff.mp hz with rfl;exact hyS)
      (by intro z hz t ht;rcases Set.mem_singleton_iff.mp hz with rfl;rcases Set.mem_singleton_iff.mp ht with rfl;exact hyy)

theorem retained_generator_two_vector_count {K V : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (htwo : (2 : K)≠0) (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (C G : Submodule K V) (hC : C=B.orthogonal C) (hG : G≤B.orthogonal G)
    (x y : V) (hxG : x∈B.orthogonal G) (hyG : y∈B.orthogonal G)
    (hx : x∉G) (hxx : B x x=0) (hyy : B y y=0) :
    Nat.card {D : Submodule K V // D=B.orthogonal D ∧ G≤D ∧ x∈D ∧ y∈D}=
      if y∈G ⊔ Submodule.span K {x} then
        splitGeneratorCount (Nat.card K) (finrank K C-finrank K G-1)
      else if B x y=0 then
        splitGeneratorCount (Nat.card K) (finrank K C-finrank K G-2) else 0 := by
  let Sx := G ⊔ Submodule.span K {x}
  let S := Sx ⊔ Submodule.span K {y}
  let e : {D : Submodule K V // D=B.orthogonal D ∧ G≤D ∧ x∈D ∧ y∈D} ≃
      {D : Submodule K V // D=B.orthogonal D ∧ S≤D} := {
    toFun := fun D => ⟨D.val,D.property.1,sup_le
      (sup_le D.property.2.1 ((Submodule.span_singleton_le_iff_mem x D.val).mpr D.property.2.2.1))
      ((Submodule.span_singleton_le_iff_mem y D.val).mpr D.property.2.2.2)⟩
    invFun := fun D => ⟨D.val,D.property.1,le_trans (le_trans le_sup_left le_sup_left) D.property.2,
      D.property.2 (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))),
      D.property.2 (Submodule.mem_sup_right (Submodule.mem_span_singleton_self y))⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  have hdimX : finrank K Sx=finrank K G+1 := Submodule.finrank_sup_span_singleton hx
  by_cases hy : y∈Sx
  · rw [if_pos hy]
    have hSx : S=Sx := sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem y Sx).mpr hy)
    have hSX : Sx≤B.orthogonal Sx := span_with_retained_self_orthogonal B hB G hG {x}
      (by intro z hz;rcases Set.mem_singleton_iff.mp hz with rfl;exact hxG)
      (by intro z hz t ht;rcases Set.mem_singleton_iff.mp hz with rfl;rcases Set.mem_singleton_iff.mp ht with rfl;exact hxx)
    rw [hSx,split_form_retained_subspace_count htwo B hB hnd C Sx hC hSX,hdimX,Nat.sub_add_eq]
  · rw [if_neg hy]
    by_cases hxy : B x y=0
    · rw [if_pos hxy]
      have hSS : S≤B.orthogonal S := (retained_pair_span_self_orthogonal B hB G hG x y hxG hyG hxx hyy).mpr hxy
      have hdim : finrank K S=finrank K G+2 := by
        have hh := Submodule.finrank_sup_span_singleton hy
        change finrank K S=finrank K Sx+1 at hh
        omega
      rw [split_form_retained_subspace_count htwo B hB hnd C S hC hSS,hdim,Nat.sub_add_eq]
    · rw [if_neg hxy]
      apply non_isotropic_subspace_no_self_dual_extension
      exact fun hs => hxy ((retained_pair_span_self_orthogonal B hB G hG x y hxG hyG hxx hyy).mp hs)

theorem finite_incidence_second_moment {α β : Type*} [Fintype α] [Fintype β]
    (P : α → β → Prop) [DecidableRel P] :
    (∑ a, (Nat.card {b : β // P a b})^2)=
      ∑ b : β, ∑ c : β,Nat.card {a : α // P a b ∧ P a c} := by
  classical
  have hc (a : α) : Nat.card {b : β // P a b}=∑ b,if P a b then (1 : ℕ) else 0 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]
  simp_rw [hc,pow_two,Fintype.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hab : P a b <;> by_cases hac : P a c <;> simp [hab,hac]

theorem finite_two_case_sum {α : Type*} [Fintype α] (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] (a b : ℕ) :
    (∑ x,if P x then a else if Q x then b else 0)=
      Nat.card {x : α // P x}*a+Nat.card {x : α // ¬P x ∧ Q x}*b := by
  classical
  have hc (R : α → Prop) : Nat.card {x : α // R x}=∑ x,if R x then (1 : ℕ) else 0 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [hc P,hc (fun x => ¬P x ∧ Q x),Finset.sum_mul,Finset.sum_mul,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hp : P x <;> by_cases hq : Q x <;> simp [hp,hq]

theorem retained_generator_second_moment_count {K V α : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype α]
    (htwo : (2 : K)≠0) (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (C G : Submodule K V) (hC : C=B.orthogonal C) (hG : G≤B.orthogonal G)
    [Fintype {D : Submodule K V // D=B.orthogonal D ∧ G≤D}]
    (v : α → V) (hvG : ∀ a,v a∈B.orthogonal G) (hv : ∀ a,v a∉G) (hvv : ∀ a,B (v a) (v a)=0) :
    (∑ D : {D : Submodule K V // D=B.orthogonal D ∧ G≤D}, (Nat.card {a : α // v a∈D.val})^2)=
      Nat.card {z : α×α // v z.2∈G ⊔ Submodule.span K {v z.1}}*
        splitGeneratorCount (Nat.card K) (finrank K C-finrank K G-1)+
      Nat.card {z : α×α // v z.2∉G ⊔ Submodule.span K {v z.1} ∧ B (v z.1) (v z.2)=0}*
        splitGeneratorCount (Nat.card K) (finrank K C-finrank K G-2) := by
  classical
  let A := {D : Submodule K V // D=B.orthogonal D ∧ G≤D}
  rw [finite_incidence_second_moment (fun (D : A) a => v a∈D.val)]
  have hcount (a b : α) : Nat.card {D : A // v a∈D.val ∧ v b∈D.val}=
      if v b∈G ⊔ Submodule.span K {v a} then
        splitGeneratorCount (Nat.card K) (finrank K C-finrank K G-1)
      else if B (v a) (v b)=0 then
        splitGeneratorCount (Nat.card K) (finrank K C-finrank K G-2) else 0 := by
    let e : {D : A // v a∈D.val ∧ v b∈D.val} ≃
        {D : Submodule K V // D=B.orthogonal D ∧ G≤D ∧ v a∈D ∧ v b∈D} := {
      toFun := fun D => ⟨D.val.val,D.val.property.1,D.val.property.2,D.property.1,D.property.2⟩
      invFun := fun D => ⟨⟨D.val,D.property.1,D.property.2.1⟩,D.property.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    rw [Nat.card_congr e]
    exact retained_generator_two_vector_count htwo B hB hnd C G hC hG (v a) (v b) (hvG a) (hvG b) (hv a) (hvv a) (hvv b)
  simp_rw [hcount]
  have hh := finite_two_case_sum (fun z : α×α => v z.2∈G ⊔ Submodule.span K {v z.1})
    (fun z : α×α => B (v z.1) (v z.2)=0)
    (splitGeneratorCount (Nat.card K) (finrank K C-finrank K G-1))
    (splitGeneratorCount (Nat.card K) (finrank K C-finrank K G-2))
  simpa only [Fintype.sum_prod_type] using hh

theorem splitGeneratorCount_two_step_ratio (q h : ℕ) (hh : 2≤h) :
    (splitGeneratorCount q (h-2) : ℝ)/(splitGeneratorCount q h : ℝ)=
      1/(((q : ℝ)^(h-1)+1)*((q : ℝ)^(h-2)+1)) := by
  have hr := splitGeneratorCount_ratio q (h-2) 2
  have heq : h-2+2=h := by omega
  have heq' : h-2+1=h-1 := by omega
  simpa only [heq,Finset.prod_range_succ,Finset.prod_range_zero,one_mul,Nat.add_zero,heq',mul_comm] using hr

theorem retained_generator_second_moment {K V α : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype α]
    (htwo : (2 : K)≠0) (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (C G : Submodule K V) (hC : C=B.orthogonal C) (hG : G≤B.orthogonal G)
    [Fintype {D : Submodule K V // D=B.orthogonal D ∧ G≤D}]
    (h : ℕ) (hrank : finrank K G+h=finrank K C) (hh : 2≤h)
    (v : α → V) (hvG : ∀ a,v a∈B.orthogonal G) (hv : ∀ a,v a∉G) (hvv : ∀ a,B (v a) (v a)=0) :
    (((∑ D : {D : Submodule K V // D=B.orthogonal D ∧ G≤D}, (Nat.card {a : α // v a∈D.val})^2) : ℕ) : ℝ)/
      (Nat.card {D : Submodule K V // D=B.orthogonal D ∧ G≤D} : ℝ)=
        (Nat.card {z : α×α // v z.2∈G ⊔ Submodule.span K {v z.1}} : ℝ)/((Nat.card K : ℝ)^(h-1)+1)+
        (Nat.card {z : α×α // v z.2∉G ⊔ Submodule.span K {v z.1} ∧ B (v z.1) (v z.2)=0} : ℝ)/
          (((Nat.card K : ℝ)^(h-1)+1)*((Nat.card K : ℝ)^(h-2)+1)) := by
  have hc := retained_generator_second_moment_count htwo B hB hnd C G hC hG v hvG hv hvv
  have hd := split_form_retained_subspace_count htwo B hB hnd C G hC hG
  have hr : finrank K C-finrank K G=h := by omega
  rw [hc,hd,hr,Nat.cast_add,Nat.cast_mul,Nat.cast_mul,add_div,mul_div_assoc,mul_div_assoc,
    splitGeneratorCount_one_step_ratio _ h (by omega),splitGeneratorCount_two_step_ratio _ h hh]
  ring

theorem finite_moment_ratio_certificate {α : Type*} [Fintype α] [Nonempty α]
    (Y : α → ℕ) (k : ℕ) (hpos : 0<∑ i,Y i^k) :
    ∃ i : α,Nat.ceil (((∑ j,Y j^(k+1) : ℕ) : ℝ)/((∑ j,Y j^k : ℕ) : ℝ))≤Y i := by
  classical
  obtain ⟨i,hi,hmax⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty Y
  have hle (j : α) : Y j≤Y i := by
    have hh : Y j≤Finset.univ.sup Y := Finset.le_sup (Finset.mem_univ _)
    rwa [hmax] at hh
  have hpoint (j : α) : Y j^(k+1)≤Y j^k*Y i := by
    rw [pow_succ]
    exact Nat.mul_le_mul_left _ (hle j)
  have hsum : (∑ j,Y j^(k+1))≤(∑ j,Y j^k)*Y i := by
    calc
      _≤∑ j,Y j^k*Y i := Finset.sum_le_sum (fun j _ => hpoint j)
      _=_ := by rw [Finset.sum_mul]
  have hden : (0 : ℝ)<((∑ j,Y j^k : ℕ) : ℝ) := by exact_mod_cast hpos
  have hsumR : ((∑ j,Y j^(k+1) : ℕ) : ℝ)≤((∑ j,Y j^k : ℕ) : ℝ)*(Y i : ℝ) := by
    exact_mod_cast hsum
  have hratio : (((∑ j,Y j^(k+1) : ℕ) : ℝ)/((∑ j,Y j^k : ℕ) : ℝ))≤(Y i : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    simpa only [mul_comm] using hsumR
  exact ⟨i,Nat.ceil_le.mpr hratio⟩

theorem retained_actual_sign_first_two_moments {p : ℕ} [Fact p.Prime] (hodd : p%2=1)
    (G C : Submodule (ZMod p) (Fin (4*p) → ZMod p))
    [Fintype {D : Submodule (ZMod p) (Fin (4*p) → ZMod p) //
      D=(coordinateDotForm (ZMod p) (4*p)).orthogonal D ∧ G≤D}]
    (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C) (hGC : G≤C)
    (h : ℕ) (hrank : finrank (ZMod p) G+h=2*p) (hh : 2≤h) :
    let B := coordinateDotForm (ZMod p) (4*p)
    let U := codeSignCandidates (B.orthogonal G)
    let A := codeSignCandidates G
    let S := U \ A
    let v : S → (Fin (4*p) → ZMod p) := fun x j => (modularBitSign (x.val j) : ZMod p)
    let S₂ := Nat.card {z : S×S // v z.2∈G ⊔ Submodule.span (ZMod p) {v z.1}}
    let T := Nat.card {z : S×S // v z.2∉G ⊔ Submodule.span (ZMod p) {v z.1} ∧ B (v z.1) (v z.2)=0}
    let Ω := {D : Submodule (ZMod p) (Fin (4*p) → ZMod p) // D=B.orthogonal D ∧ G≤D}
    let Y : Ω → ℕ := fun D => (codeSignCandidates D.val).card-A.card
    (((∑ D : Ω,Y D : ℕ) : ℝ)/(Nat.card Ω : ℝ)=(S.card : ℝ)/((p : ℝ)^(h-1)+1)) ∧
    (((∑ D : Ω,(Y D)^2 : ℕ) : ℝ)/(Nat.card Ω : ℝ)=
      (S₂ : ℝ)/((p : ℝ)^(h-1)+1)+(T : ℝ)/(((p : ℝ)^(h-1)+1)*((p : ℝ)^(h-2)+1))) := by
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
  have hvG (x : S) : v x∈B.orthogonal G := (Finset.mem_filter.mp (Finset.mem_sdiff.mp x.property).1).2.2
  have hv (x : S) : v x∉G := by
    intro hx
    exact (Finset.mem_sdiff.mp x.property).2 (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,(Finset.mem_filter.mp (Finset.mem_sdiff.mp x.property).1).2.1,hx⟩)
  have hvv (x : S) : B (v x) (v x)=0 := signResidue_isotropic x.val
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
  have hm1 := retained_generator_first_moment htwo B (coordinateDotForm_symm _ _)
    (coordinateDotForm_nondegenerate _ _) C G hC hG h (by omega) (by omega) v hvG hv hvv
  have hm2 := retained_generator_second_moment htwo B (coordinateDotForm_symm _ _)
    (coordinateDotForm_nondegenerate _ _) C G hC hG h (by omega) hh v hvG hv hvv
  simp_rw [hcount] at hm1 hm2
  constructor
  · simpa only [Nat.card_eq_fintype_card,ZMod.card,Fintype.card_coe] using hm1
  · simpa only [Nat.card_eq_fintype_card,ZMod.card,Fintype.card_coe] using hm2

theorem finite_second_moment_ceiling_certificate {α : Type*} [Fintype α] [Nonempty α]
    (Y : α → ℕ) (W S T D₁ D₂ : ℝ) (hW : 0<W) (hD₁ : 0<D₁) (hD₂ : 0<D₂)
    (hfirst : (((∑ a,Y a : ℕ) : ℝ)/(Fintype.card α : ℝ))=W/D₁)
    (hsecond : (((∑ a,Y a^2 : ℕ) : ℝ)/(Fintype.card α : ℝ))=S/D₁+T/(D₁*D₂)) :
    ∃ a,Nat.ceil ((S+T/D₂)/W)≤Y a := by
  have hn : (0 : ℝ)<Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hs : (0 : ℝ)<((∑ a,Y a : ℕ) : ℝ) := by
    have hh : (0 : ℝ)<((∑ a,Y a : ℕ) : ℝ)/(Fintype.card α : ℝ) := by rw [hfirst];exact div_pos hW hD₁
    simpa only [zero_mul] using (lt_div_iff₀ hn).mp hh
  have hsN : 0<∑ a,Y a := by exact_mod_cast hs
  have hc := finite_moment_ratio_certificate Y 1 (by simpa only [pow_one] using hsN)
  have hr : (((∑ a,Y a^2 : ℕ) : ℝ)/((∑ a,Y a : ℕ) : ℝ))=(S+T/D₂)/W := by
    calc
      _=((((∑ a,Y a^2 : ℕ) : ℝ)/(Fintype.card α : ℝ))/
          (((∑ a,Y a : ℕ) : ℝ)/(Fintype.card α : ℝ))) := by
        field_simp
      _=(S/D₁+T/(D₁*D₂))/(W/D₁) := by rw [hfirst,hsecond]
      _=_ := by field_simp
  simpa only [pow_one,hr] using hc

theorem retained_line_equality_iff {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (G : Submodule K V) (x y : V) (hx : x∉G) (hy : y∉G) :
    G ⊔ Submodule.span K {x}=G ⊔ Submodule.span K {y} ↔ y∈G ⊔ Submodule.span K {x} := by
  constructor
  · intro h;rw [h];exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)
  · intro hyx
    symm
    apply Submodule.eq_of_le_of_finrank_eq
      (sup_le le_sup_left ((Submodule.span_singleton_le_iff_mem y _).mpr hyx))
    rw [Submodule.finrank_sup_span_singleton hx,Submodule.finrank_sup_span_singleton hy]

theorem finite_fiber_square_sum {α β : Type*} [Fintype α] [Fintype β] (label : α → β) :
    (∑ b : β,(Nat.card {a : α // label a=b})^2)=
      Nat.card {z : α×α // label z.1=label z.2} := by
  classical
  let e : {z : α×α // label z.1=label z.2} ≃
      Σ b : β,({a : α // label a=b} × {a : α // label a=b}) := {
    toFun := fun z => ⟨label z.val.1,⟨⟨z.val.1,rfl⟩,⟨z.val.2,z.property.symm⟩⟩⟩
    invFun := fun z => ⟨(z.2.1.val,z.2.2.val),z.2.1.property.trans z.2.2.property.symm⟩
    left_inv := fun _ => rfl
    right_inv := by
      rintro ⟨b,⟨⟨a,ha⟩,⟨c,hc⟩⟩⟩
      dsimp
      subst b
      rfl }
  rw [Nat.card_congr e]
  simp only [Nat.card_eq_fintype_card,Fintype.card_sigma,Fintype.card_prod,pow_two]

theorem retained_actual_sign_second_moment_certificate {p : ℕ} [Fact p.Prime] (hodd : p%2=1)
    (G C : Submodule (ZMod p) (Fin (4*p) → ZMod p))
    [Fintype {D : Submodule (ZMod p) (Fin (4*p) → ZMod p) //
      D=(coordinateDotForm (ZMod p) (4*p)).orthogonal D ∧ G≤D}]
    (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C) (hGC : G≤C)
    (h : ℕ) (hrank : finrank (ZMod p) G+h=2*p) (hh : 2≤h) :
    let B := coordinateDotForm (ZMod p) (4*p)
    let U := codeSignCandidates (B.orthogonal G)
    let A := codeSignCandidates G
    let S := U \ A
    let v : S → (Fin (4*p) → ZMod p) := fun x j => (modularBitSign (x.val j) : ZMod p)
    let S₂ := Nat.card {z : S×S // v z.2∈G ⊔ Submodule.span (ZMod p) {v z.1}}
    let T := Nat.card {z : S×S // v z.2∉G ⊔ Submodule.span (ZMod p) {v z.1} ∧ B (v z.1) (v z.2)=0}
    0<S.card → ∃ D : {D : Submodule (ZMod p) (Fin (4*p) → ZMod p) // D=B.orthogonal D ∧ G≤D},
      A.card+Nat.ceil (((S₂ : ℝ)+(T : ℝ)/((p : ℝ)^(h-2)+1))/(S.card : ℝ))≤(codeSignCandidates D.val).card := by
  classical
  let B := coordinateDotForm (ZMod p) (4*p)
  let U := codeSignCandidates (B.orthogonal G)
  let A := codeSignCandidates G
  let S := U \ A
  let v : S → (Fin (4*p) → ZMod p) := fun x j => (modularBitSign (x.val j) : ZMod p)
  let S₂ := Nat.card {z : S×S // v z.2∈G ⊔ Submodule.span (ZMod p) {v z.1}}
  let T := Nat.card {z : S×S // v z.2∉G ⊔ Submodule.span (ZMod p) {v z.1} ∧ B (v z.1) (v z.2)=0}
  let Ω := {D : Submodule (ZMod p) (Fin (4*p) → ZMod p) // D=B.orthogonal D ∧ G≤D}
  let Y : Ω → ℕ := fun D => (codeSignCandidates D.val).card-A.card
  letI : Nonempty Ω := ⟨⟨C,hC,hGC⟩⟩
  change 0<S.card → ∃ D : Ω,A.card+Nat.ceil (((S₂ : ℝ)+(T : ℝ)/((p : ℝ)^(h-2)+1))/(S.card : ℝ))≤(codeSignCandidates D.val).card
  intro hS
  have hm := retained_actual_sign_first_two_moments hodd G C hC hGC h hrank hh
  have hW : (0 : ℝ)<S.card := by exact_mod_cast hS
  have hD₁ : (0 : ℝ)<(p : ℝ)^(h-1)+1 := by positivity
  have hD₂ : (0 : ℝ)<(p : ℝ)^(h-2)+1 := by positivity
  have hΩ : Nat.card Ω=Fintype.card Ω := Nat.card_eq_fintype_card
  have hm1 : (((∑ D : Ω,Y D : ℕ) : ℝ)/(Fintype.card Ω : ℝ))=(S.card : ℝ)/((p : ℝ)^(h-1)+1) := by
    rw [← hΩ]
    exact hm.1
  have hm2 : (((∑ D : Ω,(Y D)^2 : ℕ) : ℝ)/(Fintype.card Ω : ℝ))=
      (S₂ : ℝ)/((p : ℝ)^(h-1)+1)+(T : ℝ)/(((p : ℝ)^(h-1)+1)*((p : ℝ)^(h-2)+1)) := by
    rw [← hΩ]
    exact hm.2
  obtain ⟨D,hD⟩ := finite_second_moment_ceiling_certificate Y S.card S₂ T _ _ hW hD₁ hD₂ hm1 hm2
  refine ⟨D,?_⟩
  have hAD : A.card≤(codeSignCandidates D.val).card :=
    Finset.card_le_card (codeSignCandidates_mono G D.val D.property.2)
  change Nat.ceil (((S₂ : ℝ)+(T : ℝ)/((p : ℝ)^(h-2)+1))/(S.card : ℝ))≤
    (codeSignCandidates D.val).card-A.card at hD
  change A.card+Nat.ceil (((S₂ : ℝ)+(T : ℝ)/((p : ℝ)^(h-2)+1))/(S.card : ℝ))≤(codeSignCandidates D.val).card
  omega

theorem finite_fiber_relation_sum {α β : Type*} [Fintype α] [Fintype β]
    (label : α → β) (R : β → β → Prop) [DecidableRel R] :
    (∑ b : β,∑ c : β,if R b c then Nat.card {a : α // label a=b}*Nat.card {a : α // label a=c} else 0)=
      Nat.card {z : α×α // R (label z.1) (label z.2)} := by
  classical
  let e : {z : α×α // R (label z.1) (label z.2)} ≃
      Σ t : {z : β×β // R z.1 z.2},({a : α // label a=t.val.1} × {a : α // label a=t.val.2}) := {
    toFun := fun z => ⟨⟨(label z.val.1,label z.val.2),z.property⟩,⟨⟨z.val.1,rfl⟩,⟨z.val.2,rfl⟩⟩⟩
    invFun := fun z => ⟨(z.2.1.val,z.2.2.val),by rw [z.2.1.property,z.2.2.property];exact z.1.property⟩
    left_inv := fun _ => rfl
    right_inv := by
      rintro ⟨⟨⟨x,y⟩,hxy⟩,⟨⟨a,ha⟩,⟨b,hb⟩⟩⟩
      dsimp at ha hb ⊢
      subst x
      subst y
      rfl }
  rw [Nat.card_congr e]
  simp only [Nat.card_eq_fintype_card,Fintype.card_sigma,Fintype.card_prod]
  have hh := Finset.sum_subtype (p := fun z : β×β => R z.1 z.2) (F := inferInstance) (Finset.univ.filter (fun z : β×β => R z.1 z.2))
    (by intro z;simp) (fun z : β×β => Fintype.card {a : α // label a=z.1}*Fintype.card {a : α // label a=z.2})
  rw [Finset.sum_filter,Fintype.sum_prod_type] at hh
  exact hh

theorem retained_line_orthogonal_iff {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (G : Submodule K V) (hG : G≤B.orthogonal G)
    (x y : V) (hxG : x∈B.orthogonal G) (hyG : y∈B.orthogonal G) (hxx : B x x=0) (hyy : B y y=0) :
    G ⊔ Submodule.span K {x}≤B.orthogonal (G ⊔ Submodule.span K {y}) ↔ B x y=0 := by
  constructor
  · intro h
    have hz := h (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)) y
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self y))
    rwa [hB.eq y x] at hz
  · intro hxy
    have hS := (retained_pair_span_self_orthogonal B hB G hG x y hxG hyG hxx hyy).mpr hxy
    have hyS : G ⊔ Submodule.span K {y}≤(G ⊔ Submodule.span K {x}) ⊔ Submodule.span K {y} :=
      sup_le (le_trans le_sup_left le_sup_left) le_sup_right
    intro z hz t ht
    exact hS (Submodule.mem_sup_left hz) t (hyS ht)

theorem retained_line_weight_pair_identities {K V α : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype α] [Fintype (Submodule K V)]
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (G : Submodule K V) (hG : G≤B.orthogonal G)
    (v : α → V) (hvG : ∀ a,v a∈B.orthogonal G) (hv : ∀ a,v a∉G) (hvv : ∀ a,B (v a) (v a)=0) :
    let label : α → Submodule K V := fun a => G ⊔ Submodule.span K {v a}
    let w : Submodule K V → ℕ := fun L => Nat.card {a : α // label a=L}
    (∑ L : Submodule K V,w L^2)=Nat.card {z : α×α // v z.2∈G ⊔ Submodule.span K {v z.1}} ∧
    (∑ L : Submodule K V,∑ M : Submodule K V,if L≠M ∧ L≤B.orthogonal M then w L*w M else 0)=
      Nat.card {z : α×α // v z.2∉G ⊔ Submodule.span K {v z.1} ∧ B (v z.1) (v z.2)=0} := by
  classical
  let label : α → Submodule K V := fun a => G ⊔ Submodule.span K {v a}
  have heq (a b : α) : label a=label b ↔ v b∈G ⊔ Submodule.span K {v a} :=
    retained_line_equality_iff G (v a) (v b) (hv a) (hv b)
  constructor
  · rw [finite_fiber_square_sum label]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun z : α×α => heq z.1 z.2))
  · rw [finite_fiber_relation_sum label (fun L M => L≠M ∧ L≤B.orthogonal M)]
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro z
    exact and_congr (not_congr (heq z.1 z.2))
      (retained_line_orthogonal_iff B hB G hG (v z.1) (v z.2) (hvG z.1) (hvG z.2) (hvv z.1) (hvv z.2))

theorem retained_line_quotient_rank_one {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (G : Submodule K V)
    (hG : G≤B.orthogonal G) (x : V) (hxG : x∈B.orthogonal G) (hx : x∉G) :
    finrank K (orthogonalQuotientCode B (G ⊔ Submodule.span K {x}) G)=1 := by
  let H := B.orthogonal G
  let T := G.comap H.subtype
  let L := G ⊔ Submodule.span K {x}
  let A := L.comap H.subtype
  have hLH : L≤H := sup_le hG ((Submodule.span_singleton_le_iff_mem x H).mpr hxG)
  have hTA : T≤A := fun y hy => Submodule.mem_sup_left hy
  have hh := submodule_quotient_image_finrank T A hTA
  have hT := Submodule.finrank_map_subtype_eq H T
  have hA := Submodule.finrank_map_subtype_eq H A
  rw [ambient_submodule_map_comap H G hG] at hT
  rw [ambient_submodule_map_comap H L hLH] at hA
  change finrank K (orthogonalQuotientCode B L G)+finrank K T=finrank K A at hh
  rw [← hT,← hA] at hh
  have hdim : finrank K L=finrank K G+1 := Submodule.finrank_sup_span_singleton hx
  change finrank K (orthogonalQuotientCode B L G)=1
  omega

end CompletionTheory
