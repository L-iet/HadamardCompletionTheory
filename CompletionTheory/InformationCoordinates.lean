/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module

public import CompletionTheory
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Information coordinates for finite-dimensional subspaces -/

@[expose] public section
namespace CompletionTheory

def coordinateFunctional {K ι : Type*} [Field K] (V : Submodule K (ι → K)) (i : ι) :
    Module.Dual K V := (LinearMap.proj i).comp V.subtype

theorem coordinateFunctionals_span {K ι : Type*} [Field K] [Fintype ι]
    (V : Submodule K (ι → K)) :
    Submodule.span K (Set.range (coordinateFunctional V)) = ⊤ := by
  classical
  apply Submodule.span_eq_top_of_ne_zero
  intro z hz
  have hcoord : ∃ i, z.val i ≠ 0 := by
    by_contra h
    push Not at h
    apply hz
    apply Subtype.ext
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hcoord
  exact ⟨coordinateFunctional V i, ⟨i, rfl⟩, hi⟩

theorem exists_information_coordinates.{u, v} {K : Type u} {ι : Type v} [Field K] [Fintype ι]
    (V : Submodule K (ι → K)) :
    ∃ (J : Type v) (_ : Fintype J) (a : J → ι), Function.Injective a ∧
      Fintype.card J = Module.finrank K V ∧
      Function.Injective (fun v : V => fun j : J => v.val (a j)) := by
  classical
  obtain ⟨J, a, ha, hspan, hli⟩ := exists_linearIndependent' K (coordinateFunctional V)
  let : Finite J := Finite.of_injective a ha
  let : Fintype J := Fintype.ofFinite J
  rw [coordinateFunctionals_span] at hspan
  let b : Module.Basis J K (Module.Dual K V) := Module.Basis.mk hli hspan.ge
  refine ⟨J, inferInstance, a, ha, ?_, ?_⟩
  · rw [← Module.finrank_eq_card_basis b, Subspace.dual_finrank_eq]
  · intro u v huv
    have hzero : u - v = 0 := by
      by_contra hne
      have hnonzero : ∃ i, (u - v).val i ≠ 0 := by
        by_contra hn
        push Not at hn
        exact hne (Subtype.ext (funext hn))
      obtain ⟨i, hi⟩ := hnonzero
      have hmem : coordinateFunctional V i ∈ Submodule.span K
          (Set.range (coordinateFunctional V ∘ a)) := by rw [hspan]; trivial
      have hvanish : ∀ f ∈ Submodule.span K (Set.range (coordinateFunctional V ∘ a)),
          f (u - v) = 0 := by
        intro f hf
        induction hf using Submodule.span_induction with
        | mem f hf =>
          obtain ⟨j, rfl⟩ := hf
          change u.val (a j) - v.val (a j) = 0
          exact sub_eq_zero.mpr (congrFun huv j)
        | zero => simp
        | add f g hf hg ihf ihg => simp [ihf, ihg]
        | smul c f hf ih => simp [ih]
      exact hi (hvanish _ hmem)
    exact sub_eq_zero.mp hzero

theorem exists_information_coordinate_set {K ι : Type*} [Field K] [Fintype ι]
    (V : Submodule K (ι → K)) :
    ∃ I : Finset ι, I.card = Module.finrank K V ∧
      Function.Injective (fun v : V => fun j : I => v.val j.val) := by
  classical
  obtain ⟨J, inst, a, ha, hcard, hinj⟩ := exists_information_coordinates V
  let : Fintype J := inst
  let I : Finset ι := Finset.univ.image a
  refine ⟨I, ?_, ?_⟩
  · simpa only [I, Finset.card_image_of_injective _ ha, Finset.card_univ] using hcard
  · intro u v huv
    apply hinj
    funext j
    exact congrFun huv ⟨a j, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩

theorem exists_information_equivalence {K ι : Type*} [Field K] [Fintype ι]
    (V : Submodule K (ι → K)) :
    ∃ I : Finset ι, I.card = Module.finrank K V ∧
      ∃ e : V ≃ₗ[K] (I → K), ∀ v j, e v j = v.val j.val := by
  classical
  obtain ⟨I, hcard, hinj⟩ := exists_information_coordinate_set V
  let f : V →ₗ[K] (I → K) := LinearMap.pi (fun j => coordinateFunctional V j.val)
  have hf : Function.Injective f := hinj
  have hrank : Module.finrank K V = Module.finrank K (I → K) := by simp [← hcard]
  let e := LinearEquiv.ofInjectiveOfFinrankEq f hf hrank
  refine ⟨I, hcard, e, ?_⟩
  intro v j
  change (LinearEquiv.ofInjectiveOfFinrankEq f hf hrank) v j = _
  rfl

def IsCubeVector {K ι : Type*} [One K] [Neg K] (v : ι → K) : Prop :=
  ∀ i, v i = 1 ∨ v i = -1

noncomputable def cubeCandidates {K ι : Type*} [Field K] [Fintype ι]
    {V : Submodule K (ι → K)} {I : Finset ι} (e : V ≃ₗ[K] (I → K)) : Finset V := by
  classical
  exact (Finset.univ.image (fun b : I → Bool => e.symm (fun j => if b j then 1 else -1))).filter
    (fun v => IsCubeVector v.val)

theorem mem_cubeCandidates_iff {K ι : Type*} [Field K] [Fintype ι]
    {V : Submodule K (ι → K)} {I : Finset ι} (e : V ≃ₗ[K] (I → K))
    (he : ∀ v j, e v j = v.val j.val) (v : V) :
    v ∈ cubeCandidates e ↔ IsCubeVector v.val := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro hv
    refine Finset.mem_filter.mpr ⟨?_, hv⟩
    let b : I → Bool := fun j => decide (v.val j.val = 1)
    refine Finset.mem_image.mpr ⟨b, Finset.mem_univ b, ?_⟩
    apply e.injective
    rw [e.apply_symm_apply]
    funext j
    rw [he]
    rcases hv j.val with hp | hn
    · simp [b, hp]
    · by_cases hp : v.val j.val = 1
      · simp [b, hp]
      · simpa only [b, decide_eq_false_iff_not.mpr hp, Bool.false_eq_true, ite_false] using hn.symm

theorem cubeCandidates_card_le {K ι : Type*} [Field K] [Fintype ι]
    {V : Submodule K (ι → K)} {I : Finset ι} (e : V ≃ₗ[K] (I → K)) :
    (cubeCandidates e).card ≤ 2 ^ I.card := by
  classical
  exact (Finset.card_filter_le _ _).trans
    ((Finset.card_image_le).trans (by simp))

noncomputable def normalizedCubeCandidates {K ι : Type*} [Field K] [Fintype ι]
    {V : Submodule K (ι → K)} {I : Finset ι} (e : V ≃ₗ[K] (I → K)) (j : I) : Finset V := by
  classical
  exact (cubeCandidates e).filter (fun v => v.val j.val = 1)

theorem isCubeVector_neg {K ι : Type*} [Field K] (v : ι → K) (hv : IsCubeVector v) :
    IsCubeVector (-v) := by
  intro j
  rcases hv j with hp | hn
  · right; simp only [Pi.neg_apply, hp]
  · left; simp only [Pi.neg_apply, hn, neg_neg]

theorem normalizedCubeCandidates_cover {K ι : Type*} [Field K] [Fintype ι]
    {V : Submodule K (ι → K)} {I : Finset ι} (e : V ≃ₗ[K] (I → K))
    (he : ∀ v j, e v j = v.val j.val) (j : I) (v : V) (hv : IsCubeVector v.val) :
    v ∈ normalizedCubeCandidates e j ∨ -v ∈ normalizedCubeCandidates e j := by
  classical
  rcases hv j.val with hp | hn
  · exact Or.inl (Finset.mem_filter.mpr ⟨(mem_cubeCandidates_iff e he v).mpr hv, hp⟩)
  · apply Or.inr
    refine Finset.mem_filter.mpr ⟨(mem_cubeCandidates_iff e he (-v)).mpr
      (isCubeVector_neg v.val hv), ?_⟩
    change -v.val j.val = 1
    rw [hn, neg_neg]

theorem normalizedCubeCandidates_card_le {K ι : Type*} [Field K] [CharZero K] [Fintype ι]
    {V : Submodule K (ι → K)} {I : Finset ι} (e : V ≃ₗ[K] (I → K))
    (he : ∀ v j, e v j = v.val j.val) (j : I) :
    (normalizedCubeCandidates e j).card ≤ 2 ^ (I.card - 1) := by
  classical
  let P := normalizedCubeCandidates e j
  let N := P.image (fun v => -v)
  have hP : P ⊆ cubeCandidates e := fun v hv => (Finset.mem_filter.mp hv).1
  have hN : N ⊆ cubeCandidates e := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact (mem_cubeCandidates_iff e he (-w)).mpr
      (isCubeVector_neg w.val ((mem_cubeCandidates_iff e he w).mp (hP hw)))
  have hdis : Disjoint P N := by
    apply Finset.disjoint_left.mpr
    intro v hv hn
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hn
    have hp := (Finset.mem_filter.mp hv).2
    have hwp := (Finset.mem_filter.mp hw).2
    change -w.val j.val = 1 at hp
    norm_num [hwp] at hp
  have hncard : N.card = P.card := Finset.card_image_of_injective P neg_injective
  have hcount := Finset.card_le_card (Finset.union_subset hP hN)
  rw [Finset.card_union_of_disjoint hdis, hncard] at hcount
  have hall := cubeCandidates_card_le e
  have hi : 0 < I.card := Finset.card_pos.mpr ⟨j.val, j.property⟩
  have hpow : 2 ^ I.card = 2 * 2 ^ (I.card - 1) := by
    calc
      _ = 2 ^ (I.card - 1 + 1) := by congr 1; omega
      _ = _ := by rw [pow_succ]; omega
  change P.card ≤ _
  omega

noncomputable def normalizedInformationSeed {K ι : Type*} [Field K]
    {I : Finset ι} (j : I) (b : {k : I // k ≠ j} → Bool) : I → K := by
  classical
  exact fun k => if h : k = j then 1 else if b ⟨k, h⟩ then 1 else -1

noncomputable def normalizedInformationSearch {K ι : Type*} [Field K] [Fintype ι]
    {V : Submodule K (ι → K)} {I : Finset ι} (e : V ≃ₗ[K] (I → K)) (j : I) : Finset V := by
  classical
  exact (Finset.univ.image (fun b : {k : I // k ≠ j} → Bool =>
    e.symm (normalizedInformationSeed j b))).filter (fun v => IsCubeVector v.val)

theorem normalized_information_assignment_count {ι : Type*} [DecidableEq ι] {I : Finset ι} (j : I) :
    Fintype.card ({k : I // k ≠ j} → Bool) = 2 ^ (I.card - 1) := by
  classical
  simp [Fintype.card_subtype_compl]

theorem normalizedInformationSearch_eq {K ι : Type*} [Field K] [Fintype ι]
    {V : Submodule K (ι → K)} {I : Finset ι} (e : V ≃ₗ[K] (I → K))
    (he : ∀ v j, e v j = v.val j.val) (j : I) :
    normalizedInformationSearch e j = normalizedCubeCandidates e j := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨hvimage, hvsign⟩ := Finset.mem_filter.mp hv
    obtain ⟨b, hb, hval⟩ := Finset.mem_image.mp hvimage
    refine Finset.mem_filter.mpr ⟨(mem_cubeCandidates_iff e he v).mpr hvsign, ?_⟩
    rw [← he v j, ← hval, e.apply_symm_apply]
    simp [normalizedInformationSeed]
  · intro hv
    obtain ⟨hvC, hvj⟩ := Finset.mem_filter.mp hv
    have hvsign := (mem_cubeCandidates_iff e he v).mp hvC
    refine Finset.mem_filter.mpr ⟨?_, hvsign⟩
    let b : {k : I // k ≠ j} → Bool := fun k => decide (v.val k.val.val = 1)
    refine Finset.mem_image.mpr ⟨b, Finset.mem_univ b, ?_⟩
    apply e.injective
    rw [e.apply_symm_apply]
    funext k
    rw [he]
    by_cases hk : k = j
    · subst k
      simp [normalizedInformationSeed, hvj]
    · rw [normalizedInformationSeed, dite_eq_right hk]
      rcases hvsign k.val with hp | hn
      · simp [b, hp]
      · by_cases hp : v.val k.val = 1
        · simp [b, hp]
        · simpa only [b, decide_eq_false_iff_not.mpr hp, Bool.false_eq_true, ite_false] using hn.symm

theorem normalizedInformationSearch_card_le {K ι : Type*} [Field K] [Fintype ι]
    {V : Submodule K (ι → K)} {I : Finset ι} (e : V ≃ₗ[K] (I → K)) (j : I) :
    (normalizedInformationSearch e j).card ≤ 2 ^ (I.card - 1) := by
  classical
  exact (Finset.card_filter_le _ _).trans ((Finset.card_image_le).trans
    (by simp))

noncomputable def informationMatrix {K ι : Type*} [Field K]
    {V : Submodule K (ι → K)} {I : Finset ι} (e : V ≃ₗ[K] (I → K)) :
    Matrix ι I K := by
  classical
  exact fun i j => (e.symm (Pi.single j 1)).val i

theorem information_reconstruction_formula {K ι : Type*} [Field K]
    {V : Submodule K (ι → K)} {I : Finset ι} (e : V ≃ₗ[K] (I → K)) (b : I → K) (i : ι) :
    (e.symm b).val i = ∑ j, informationMatrix e i j * b j := by
  classical
  have hdecomp : (∑ j : I, b j • Pi.single j (1 : K)) = b := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [← hdecomp, map_sum]
  simp [informationMatrix, Finset.sum_apply, smul_eq_mul, mul_comm]

theorem informationMatrix_parameterizes {K ι : Type*} [Field K]
    {V : Submodule K (ι → K)} {I : Finset ι} (e : V ≃ₗ[K] (I → K))
    (he : ∀ v j, e v j = v.val j.val) (b : I → K) :
    (fun i => ∑ j, informationMatrix e i j * b j) ∈ V ∧
      ∀ j : I, (∑ k, informationMatrix e j.val k * b k) = b j := by
  have hf : (fun i => ∑ j, informationMatrix e i j * b j) = (e.symm b).val := by
    funext i
    exact (information_reconstruction_formula e b i).symm
  constructor
  · rw [hf]
    exact (e.symm b).property
  · intro j
    rw [← information_reconstruction_formula, ← he, e.apply_symm_apply]

theorem exists_cube_enumeration {K ι : Type*} [Field K] [Fintype ι]
    (V : Submodule K (ι → K)) :
    ∃ C : Finset V, (∀ v : V, v ∈ C ↔ IsCubeVector v.val) ∧
      C.card ≤ 2 ^ Module.finrank K V := by
  obtain ⟨I, hcard, e, he⟩ := exists_information_equivalence V
  exact ⟨cubeCandidates e, mem_cubeCandidates_iff e he, hcard ▸ cubeCandidates_card_le e⟩

theorem information_coordinate_enumeration {K ι : Type*} [Field K] [CharZero K]
    [Fintype ι] [DecidableEq ι] (V : Submodule K (ι → K)) :
    ∃ I : Finset ι, I.card = Module.finrank K V ∧
      ∃ e : V ≃ₗ[K] (I → K), (∀ v j, e v j = v.val j.val) ∧
        (∀ v : V, v ∈ cubeCandidates e ↔ IsCubeVector v.val) ∧
        (cubeCandidates e).card ≤ 2 ^ Module.finrank K V ∧
        (∀ j : I, Fintype.card ({k : I // k ≠ j} → Bool) = 2 ^ (Module.finrank K V - 1) ∧
          (normalizedInformationSearch e j).card ≤ 2 ^ (Module.finrank K V - 1) ∧
          ∀ v : V, IsCubeVector v.val →
            v ∈ normalizedInformationSearch e j ∨ -v ∈ normalizedInformationSearch e j) ∧
        (∀ b i, (e.symm b).val i = ∑ j, informationMatrix e i j * b j) := by
  classical
  obtain ⟨I, hcard, e, he⟩ := exists_information_equivalence V
  refine ⟨I, hcard, e, he, mem_cubeCandidates_iff e he,
    hcard ▸ cubeCandidates_card_le e, ?_, information_reconstruction_formula e⟩
  intro j
  refine ⟨hcard ▸ normalized_information_assignment_count j,
    hcard ▸ normalizedInformationSearch_card_le e j, ?_⟩
  intro v hv
  rw [normalizedInformationSearch_eq e he]
  exact normalizedCubeCandidates_cover e he j v hv

end CompletionTheory
