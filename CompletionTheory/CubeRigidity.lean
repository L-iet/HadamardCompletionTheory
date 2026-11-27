/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module

public import CompletionTheory.InformationCoordinates

/-! # Rigidity of linear forms on the sign cube -/

@[expose] public section
namespace CompletionTheory

theorem sign_linear_form_coefficients {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (h : ∀ x : ι → ℝ, IsCubeVector x → IsSign (∑ i, a i * x i)) :
    ∀ j, a j = 0 ∨ a j = 1 ∨ a j = -1 := by
  classical
  have hc : IsSign (∑ i, a i) := by
    simpa using h (fun _ => 1) (fun _ => Or.inl rfl)
  intro j
  have hx : IsCubeVector (fun i : ι => if i = j then (-1 : ℝ) else 1) := by
    intro i
    by_cases hij : i = j <;> simp [hij]
  have hf := h _ hx
  have heq : (∑ i, a i * (if i = j then (-1 : ℝ) else 1)) = (∑ i, a i) - 2 * a j := by
    calc
      _ = ∑ i, (a i - if i = j then 2 * a i else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hij : i = j
        · simp only [hij, ite_true, mul_neg_one]
          ring
        · simp [hij]
      _ = _ := by rw [Finset.sum_sub_distrib]; simp
  rw [heq] at hf
  rcases hc with hc | hc <;> rcases hf with hf | hf
  · left; linarith
  · right; left; linarith
  · right; right; linarith
  · left; linarith

theorem sign_linear_form_abs_sum {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (h : ∀ x : ι → ℝ, IsCubeVector x → IsSign (∑ i, a i * x i)) :
    (∑ i, |a i|) = 1 := by
  classical
  let x : ι → ℝ := fun i => if 0 ≤ a i then 1 else -1
  have hx : IsCubeVector x := by
    intro i
    by_cases hi : 0 ≤ a i <;> simp [x, hi]
  have heq : (∑ i, a i * x i) = ∑ i, |a i| := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases ha : 0 ≤ a i
    · simp [x, ha, abs_of_nonneg ha]
    · simp [x, ha, abs_of_neg (lt_of_not_ge ha)]
  have hs := h x hx
  rw [heq] at hs
  have hn : 0 ≤ ∑ i, |a i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  rcases hs with hs | hs
  · exact hs
  · linarith

theorem sign_linear_form_rigidity {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (h : ∀ x : ι → ℝ, IsCubeVector x → IsSign (∑ i, a i * x i)) :
    ∃ j, IsSign (a j) ∧ ∀ k, k ≠ j → a k = 0 := by
  classical
  have hsum := sign_linear_form_abs_sum a h
  have hex : ∃ j, a j ≠ 0 := by
    by_contra hn
    push Not at hn
    simp [hn] at hsum
  obtain ⟨j, hj⟩ := hex
  have hs : IsSign (a j) := (sign_linear_form_coefficients a h j).resolve_left hj
  have habs : |a j| = 1 := by rcases hs with hs | hs <;> simp [hs]
  refine ⟨j, hs, ?_⟩
  intro k hk
  have hpair : |a j| + |a k| ≤ ∑ i, |a i| := by
    have hh := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ ({j, k} : Finset ι)) (fun i _ _ => abs_nonneg (a i))
    simpa [Ne.symm hk] using hh
  have hz : |a k| = 0 := by linarith [abs_nonneg (a k)]
  exact abs_eq_zero.mp hz

theorem cubeCandidates_saturated {ι : Type*} [Fintype ι]
    {V : Submodule ℝ (ι → ℝ)} {I : Finset ι} (e : V ≃ₗ[ℝ] (I → ℝ))
    (hcard : (cubeCandidates e).card = 2 ^ I.card) :
    ∀ x : I → ℝ, IsCubeVector x → IsCubeVector (e.symm x).val := by
  classical
  let f : (I → Bool) → V := fun b => e.symm (fun j => if b j then 1 else -1)
  have hf : Function.Injective f := by
    intro b c hbc
    have hc := e.symm.injective hbc
    funext j
    have hj := congrFun hc j
    change (if b j then (1 : ℝ) else -1) = (if c j then 1 else -1) at hj
    cases hb : b j <;> cases hc : c j
    · rfl
    · norm_num [hb, hc] at hj
    · norm_num [hb, hc] at hj
    · rfl
  let B : Finset V := Finset.univ.image f
  have hBcard : B.card = 2 ^ I.card := by
    simp [B, Finset.card_image_of_injective _ hf]
  have hEq : cubeCandidates e = B := by
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.filter_subset _ _
    · rw [hcard, hBcard]
  intro x hx
  let b : I → Bool := fun j => decide (x j = 1)
  have hcode : (fun j => if b j then (1 : ℝ) else -1) = x := by
    funext j
    rcases hx j with hp | hn
    · simp [b, hp]
    · norm_num [b, hn]
  have hmem : e.symm x ∈ B := by
    refine Finset.mem_image.mpr ⟨b, Finset.mem_univ b, ?_⟩
    change e.symm (fun j => if b j then 1 else -1) = e.symm x
    rw [hcode]
  rw [← hEq] at hmem
  exact (Finset.mem_filter.mp hmem).2

theorem maximum_cube_signed_coordinates {ι : Type*} [Fintype ι]
    {V : Submodule ℝ (ι → ℝ)} {I : Finset ι} (e : V ≃ₗ[ℝ] (I → ℝ))
    (he : ∀ v j, e v j = v.val j.val) (hcard : (cubeCandidates e).card = 2 ^ I.card) :
    ∃ a : ι → I, Function.Surjective a ∧ ∃ s : ι → ℝ, IsCubeVector s ∧
      ∀ x : I → ℝ, ∀ i, (e.symm x).val i = s i * x (a i) := by
  classical
  have hrow (i : ι) : ∃ j, IsSign (informationMatrix e i j) ∧
      ∀ k, k ≠ j → informationMatrix e i k = 0 := by
    apply sign_linear_form_rigidity
    intro x hx
    rw [← information_reconstruction_formula]
    exact cubeCandidates_saturated e hcard x hx i
  choose a hs hz using hrow
  let s : ι → ℝ := fun i => informationMatrix e i (a i)
  have hrep (x : I → ℝ) (i : ι) : (e.symm x).val i = s i * x (a i) := by
    rw [information_reconstruction_formula]
    apply Finset.sum_eq_single (a i)
    · intro k hk hka
      rw [hz i k hka, zero_mul]
    · intro hn
      exact False.elim (hn (Finset.mem_univ _))
  have ha (j : I) : a j.val = j := by
    have hcoord : (e.symm (Pi.single j 1)).val j.val = 1 := by
      rw [← he, e.apply_symm_apply]
      simp
    have h := hrep (Pi.single j 1) j.val
    rw [hcoord] at h
    by_contra hn
    simp [hn] at h
  exact ⟨a, fun j => ⟨j.val, ha j⟩, s, hs, hrep⟩

def duplicationMap {ι J : Type*} (a : ι → J) (s : ι → ℝ) : (J → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun x i := s i * x (a i)
  map_add' x y := by funext i; simp [mul_add]
  map_smul' c x := by funext i; simp [smul_eq_mul]; ring

theorem maximum_cube_duplication_space {ι : Type*} [Fintype ι]
    (V : Submodule ℝ (ι → ℝ))
    (hmax : ∃ I : Finset ι, I.card = Module.finrank ℝ V ∧
      ∃ e : V ≃ₗ[ℝ] (I → ℝ), (∀ v j, e v j = v.val j.val) ∧
        (cubeCandidates e).card = 2 ^ I.card) :
    ∃ I : Finset ι, I.card = Module.finrank ℝ V ∧ ∃ a : ι → I,
      Function.Surjective a ∧ ∃ s : ι → ℝ, IsCubeVector s ∧
        V = LinearMap.range (duplicationMap a s) := by
  classical
  obtain ⟨I, hI, e, he, hc⟩ := hmax
  obtain ⟨a, ha, s, hs, hrep⟩ := maximum_cube_signed_coordinates e he hc
  refine ⟨I, hI, a, ha, s, hs, ?_⟩
  ext v
  constructor
  · intro hv
    refine ⟨e ⟨v, hv⟩, ?_⟩
    funext i
    have h := hrep (e ⟨v, hv⟩) i
    rw [e.symm_apply_apply] at h
    exact h.symm
  · rintro ⟨x, rfl⟩
    have hval : duplicationMap a s x = (e.symm x).val := by
      funext i
      exact (hrep x i).symm
    rw [hval]
    exact (e.symm x).property

theorem duplicationMap_injective {ι J : Type*} (a : ι → J) (s : ι → ℝ)
    (ha : Function.Surjective a) (hs : IsCubeVector s) :
    Function.Injective (duplicationMap a s) := by
  intro x y hxy
  funext j
  obtain ⟨i, rfl⟩ := ha j
  have hi := congrFun hxy i
  change s i * x (a i) = s i * y (a i) at hi
  rcases hs i with hp | hn
  · simpa [hp] using hi
  · simpa [hn] using hi

theorem duplicationMap_preserves_cube {ι J : Type*} (a : ι → J) (s : ι → ℝ)
    (hs : IsCubeVector s) (x : J → ℝ) (hx : IsCubeVector x) :
    IsCubeVector (duplicationMap a s x) := by
  intro i
  rcases hs i with hs | hs <;> rcases hx (a i) with hx | hx <;>
    simp [duplicationMap, hs, hx]

theorem duplicationMap_reflects_cube {ι J : Type*} (a : ι → J) (s : ι → ℝ)
    (ha : Function.Surjective a) (hs : IsCubeVector s) (x : J → ℝ)
    (hx : IsCubeVector (duplicationMap a s x)) : IsCubeVector x := by
  intro j
  obtain ⟨i, rfl⟩ := ha j
  have hi := hx i
  change s i * x (a i) = 1 ∨ s i * x (a i) = -1 at hi
  rcases hs i with hp | hn
  · simpa [hp] using hi
  · rcases hi with hi | hi
    · right; rw [hn] at hi; linarith
    · left; rw [hn] at hi; linarith

theorem duplication_space_dimension {ι J : Type*} [Fintype J]
    (a : ι → J) (s : ι → ℝ) (ha : Function.Surjective a) (hs : IsCubeVector s) :
    Module.finrank ℝ (LinearMap.range (duplicationMap a s)) = Fintype.card J := by
  rw [LinearMap.finrank_range_of_inj (duplicationMap_injective a s ha hs)]
  simp

theorem duplication_space_maximum {ι J : Type*} [Fintype ι] [Fintype J]
    (V : Submodule ℝ (ι → ℝ)) (a : ι → J) (s : ι → ℝ)
    (ha : Function.Surjective a) (hs : IsCubeVector s)
    (hV : V = LinearMap.range (duplicationMap a s))
    {I : Finset ι} (e : V ≃ₗ[ℝ] (I → ℝ)) (he : ∀ v j, e v j = v.val j.val) :
    (cubeCandidates e).card = 2 ^ Module.finrank ℝ V := by
  classical
  let f : (J → Bool) → V := fun b => ⟨duplicationMap a s (fun j => if b j then 1 else -1), by
    rw [hV]
    exact ⟨_, rfl⟩⟩
  have hf : Function.Injective f := by
    intro b c hbc
    have hval := congrArg Subtype.val hbc
    have hc := duplicationMap_injective a s ha hs hval
    funext j
    have hj := congrFun hc j
    change (if b j then (1 : ℝ) else -1) = (if c j then 1 else -1) at hj
    cases hb : b j <;> cases hc : c j
    · rfl
    · norm_num [hb, hc] at hj
    · norm_num [hb, hc] at hj
    · rfl
  have hsubset : Finset.univ.image f ⊆ cubeCandidates e := by
    intro v hv
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
    apply (mem_cubeCandidates_iff e he (f b)).mpr
    apply duplicationMap_preserves_cube a s hs
    intro j
    cases hb : b j <;> simp [hb]
  have hcard : (Finset.univ.image f).card = 2 ^ Fintype.card J := by
    simp [Finset.card_image_of_injective _ hf]
  have hdim : Module.finrank ℝ V = Fintype.card J := by
    rw [hV]
    exact duplication_space_dimension a s ha hs
  have hI : I.card = Module.finrank ℝ V := by simpa using e.finrank_eq.symm
  apply le_antisymm
  · exact hI ▸ cubeCandidates_card_le e
  · rw [hdim, ← hcard]
    exact Finset.card_le_card hsubset

theorem maximum_cube_iff_signed_duplication {ι : Type*} [Fintype ι]
    (V : Submodule ℝ (ι → ℝ)) :
    (∃ I : Finset ι, I.card = Module.finrank ℝ V ∧
      ∃ e : V ≃ₗ[ℝ] (I → ℝ), (∀ v j, e v j = v.val j.val) ∧
        (cubeCandidates e).card = 2 ^ I.card) ↔
    (∃ I : Finset ι, I.card = Module.finrank ℝ V ∧ ∃ a : ι → I,
      Function.Surjective a ∧ ∃ s : ι → ℝ, IsCubeVector s ∧
        V = LinearMap.range (duplicationMap a s)) := by
  constructor
  · exact maximum_cube_duplication_space V
  · rintro ⟨I, hI, a, ha, s, hs, hV⟩
    obtain ⟨T, hT, e, he⟩ := exists_information_equivalence V
    refine ⟨T, hT, e, he, ?_⟩
    rw [hT]
    exact duplication_space_maximum V a s ha hs hV e he

end CompletionTheory
