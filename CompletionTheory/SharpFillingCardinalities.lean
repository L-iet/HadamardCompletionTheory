/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.RealFeasibilityTopology
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 20000
namespace CompletionTheory
theorem signed_triangle_operator_not_identically_zero_int : ∀ a b : SignedTwoState,
    ∃ p c : Bool,
      let R : Matrix (Fin 2) (Fin 2) ℤ := twoPlaneMatrix p (if c then 0 else 1) (if c then 1 else 0)
      R+signedTwoInt a*R.transpose*signedTwoInt b≠0 := by decide +kernel

theorem signed_triangle_operator_not_identically_zero_real (a b : SignedTwoState) :
    ∃ p c : Bool,
      let R : Matrix (Fin 2) (Fin 2) ℝ := twoPlaneMatrix p (if c then 0 else 1) (if c then 1 else 0)
      R+signedTwoReal a*R.transpose*signedTwoReal b≠0 := by
  obtain ⟨p,c,h⟩ := signed_triangle_operator_not_identically_zero_int a b
  refine ⟨p,c,?_⟩
  dsimp only at h ⊢
  intro hz
  apply h
  have hR : (twoPlaneMatrix p (if c then 0 else 1) (if c then 1 else 0) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)=
      twoPlaneMatrix p (if c then 0 else 1) (if c then 1 else 0) := by
    cases p <;> cases c <;> ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [twoPlaneMatrix,Matrix.map_apply]
  ext i j
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M i j) hz
  rw [← hR] at he
  simp only [Matrix.add_apply,Matrix.mul_apply,Matrix.transpose_apply,Matrix.map_apply,signedTwoReal,Matrix.zero_apply] at he ⊢
  change ((twoPlaneMatrix p (if c then 0 else 1) (if c then 1 else 0) : Matrix (Fin 2) (Fin 2) ℤ) i j : ℝ)+
    (∑ k : Fin 2, (∑ l : Fin 2, (signedTwoInt a i l : ℝ)*
      ((twoPlaneMatrix p (if c then 0 else 1) (if c then 1 else 0) : Matrix (Fin 2) (Fin 2) ℤ) k l : ℝ))*(signedTwoInt b k j : ℝ))=0 at he
  exact_mod_cast he


theorem root_triangle_excludes_two_full_planes {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root i j : ι) (hi : i≠root) (hj : j≠root) (hij : i≠j) :
    ¬(∀ p : Bool, ∀ x y : ℝ, realRootConsistency A root (twoPlaneMatrix p x y)) := by
  intro hFull
  obtain ⟨a,ha⟩ := signed_two_real_triple_transpose_closed (A root j) (A i j) (A i root)
  obtain ⟨b,hb⟩ := signed_two_real_triple_transpose_closed (A root i) (A j i) (A j root)
  obtain ⟨p,c,hBad⟩ := signed_triangle_operator_not_identically_zero_real a b
  dsimp only at hBad
  let ij : RootTriangleIndex root := ⟨(i,j),hi,hj,hij⟩
  have h := (real_root_consistency_iff_triangles A root _).mp
    (hFull p (if c then 0 else 1) (if c then 1 else 0)) ij
  change twoPlaneMatrix p (if c then 0 else 1) (if c then 1 else 0)+rootTriangleLeft A root ij*
    (twoPlaneMatrix p (if c then 0 else 1) (if c then 1 else 0)).transpose*rootTriangleRight A root ij=0 at h
  have hLeft : rootTriangleLeft A root ij=signedTwoReal a := ha.symm
  have hRight : rootTriangleRight A root ij=signedTwoReal b := hb.symm
  rw [hLeft,hRight] at h
  exact hBad h

theorem three_blocks_exclude_two_full_planes {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (hCard : 3≤Fintype.card ι) :
    ¬(∀ p : Bool, ∀ x y : ℝ, realRootConsistency A root (twoPlaneMatrix p x y)) := by
  have hc : 1<(Finset.univ.erase root : Finset ι).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ root),Finset.card_univ]
    omega
  obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp hc
  exact root_triangle_excludes_two_full_planes A root i j (Finset.mem_erase.mp hi).1 (Finset.mem_erase.mp hj).1 hij


theorem axis_unit_point_norm (x y : ℝ) (h : IsAxisUnitPoint x y) : x^2+y^2=1 := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> norm_num

theorem component_sign_completions_disjoint {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (k l : TwoPlaneSectionKind) :
    Disjoint (componentSignCompletions A root false k) (componentSignCompletions A root true l) := by
  classical
  apply Finset.disjoint_left.mpr
  intro K hK0 hK1
  simp only [componentSignCompletions,Finset.mem_image] at hK0 hK1
  obtain ⟨z,hz,hzK⟩ := hK0
  obtain ⟨w,hw,hwK⟩ := hK1
  have hAxis := ((component_signed_points_spec k (z.1 : ℝ) (z.2 : ℝ)).mp ⟨z,hz,rfl,rfl⟩).2
  have hUnit := axis_unit_point_norm _ _ hAxis
  have he := congrArg (fun H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ => realFillRoot (twoBlock H root root)) (hzK.trans hwK.symm)
  rw [real_root_completion_root_inverse,real_root_completion_root_inverse] at he
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) he
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) he
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) he
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0) he
  simp [twoPlaneMatrix] at h00 h11 h01 h10
  have h00R : (z.1 : ℝ)=(w.1 : ℝ) := by exact_mod_cast h00
  have h01R : (z.2 : ℝ)=(w.2 : ℝ) := by exact_mod_cast h01
  have hx : (z.1 : ℝ)=0 := by linarith
  have hy : (z.2 : ℝ)=0 := by linarith
  rw [hx,hy] at hUnit
  norm_num at hUnit

theorem actual_fillings_component_union_exact {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι)
    (hW : normalizedTwoReal A*(normalizedTwoReal A).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (k : Bool → TwoPlaneSectionKind)
    (hk : ∀ p, k p=.zero ∨ k p=.full ∨ k p=.horizontal ∨ k p=.vertical)
    (hSections : ∀ p x y, realRootConsistency A root (twoPlaneMatrix p x y) ↔ twoPlaneSectionCondition (k p) x y)
    (H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) :
    H∈componentSignCompletions A root false (k false) ∪ componentSignCompletions A root true (k true) ↔
      IsZeroBlockHadamardFilling (normalizedTwoReal A) H := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h|h
    · obtain ⟨x,y,hEq,_,hHad⟩ := (component_sign_completions_exact A root hW false (k false) (hk false) (hSections false) H).mp h
      exact ⟨hHad,hEq ▸ real_root_completion_retains A root (twoPlaneMatrix false x y)⟩
    · obtain ⟨x,y,hEq,_,hHad⟩ := (component_sign_completions_exact A root hW true (k true) (hk true) (hSections true) H).mp h
      exact ⟨hHad,hEq ▸ real_root_completion_retains A root (twoPlaneMatrix true x y)⟩
  · rintro ⟨hHad,hRet⟩
    have hGram : H*H.transpose=(Fintype.card (Fin 2×ι) : ℝ) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hHad.mul_conjTranspose
    obtain ⟨hRG,hRC,hReconstruct⟩ := actual_real_completion_root_inverse A root hW H hGram hRet
    obtain ⟨p,x,y,hPlane,hUnit⟩ := real_orthogonal_two_plane _ hRG
    have hCons : realRootConsistency A root (twoPlaneMatrix p x y) := hPlane ▸ hRC
    have hEq : H=realRootCompletion A root (twoPlaneMatrix p x y) := by rw [← hPlane]; exact hReconstruct
    have hMem := (component_sign_completions_exact A root hW p (k p) (hk p) (hSections p) H).mpr
      ⟨x,y,hEq,⟨(two_plane_matrix_unit_gram p x y).mpr hUnit,hCons⟩,hHad⟩
    cases p
    · exact Finset.mem_union.mpr (Or.inl hMem)
    · exact Finset.mem_union.mpr (Or.inr hMem)


theorem actual_hadamard_fill_count_zero_two_four_six {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι)
    (hW : normalizedTwoReal A*(normalizedTwoReal A).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (hn : 4∣Fintype.card (Fin 2×ι)) (hCard : 3≤Fintype.card ι) :
    ∃ F : Finset (Matrix (Fin 2×ι) (Fin 2×ι) ℝ),
      (∀ H, H∈F ↔ IsZeroBlockHadamardFilling (normalizedTwoReal A) H) ∧
      (F.card=0 ∨ F.card=2 ∨ F.card=4 ∨ F.card=6) := by
  classical
  have h (p : Bool) := real_root_reduced_component_sections A root p hW hn
  choose k hk hSections using h
  have hProper : ¬(k false=.full ∧ k true=.full) := by
    intro hh
    apply three_blocks_exclude_two_full_planes A root hCard
    intro p x y
    apply (hSections p x y).mpr
    cases p <;> simp [hh.1,hh.2,twoPlaneSectionCondition]
  let F := componentSignCompletions A root false (k false) ∪ componentSignCompletions A root true (k true)
  refine ⟨F,actual_fillings_component_union_exact A root hW k hk hSections,?_⟩
  have hCount : F.card=(componentSignCompletions A root false (k false)).card+
      (componentSignCompletions A root true (k true)).card :=
    Finset.card_union_of_disjoint (component_sign_completions_disjoint A root (k false) (k true))
  rw [hCount,component_sign_completions_card,component_sign_completions_card]
  rcases hk false with h0|h0|h0|h0 <;> rcases hk true with h1|h1|h1|h1 <;> simp_all

theorem two_blocks_all_root_consistent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (hCard : Fintype.card ι=2)
    (R : Matrix (Fin 2) (Fin 2) ℝ) : realRootConsistency A root R := by
  classical
  apply (real_root_consistency_iff_triangles A root R).mpr
  intro ij
  have hs : ({root,ij.val.1,ij.val.2} : Finset ι).card=3 := by
    simp [ij.property.1,ij.property.2.1,ij.property.2.2,Ne.symm ij.property.1,Ne.symm ij.property.2.1]
  have hl := Finset.card_le_univ ({root,ij.val.1,ij.val.2} : Finset ι)
  omega

theorem order_four_exactly_eight_fillings {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι)
    (hW : normalizedTwoReal A*(normalizedTwoReal A).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (hCard : Fintype.card ι=2) :
    ∃ F : Finset (Matrix (Fin 2×ι) (Fin 2×ι) ℝ),
      (∀ H, H∈F ↔ IsZeroBlockHadamardFilling (normalizedTwoReal A) H) ∧ F.card=8 := by
  classical
  have hSections (p : Bool) (x y : ℝ) : realRootConsistency A root (twoPlaneMatrix p x y) ↔
      twoPlaneSectionCondition .full x y := by
    constructor
    · intro _; exact ⟨rfl,rfl⟩
    · intro _; exact two_blocks_all_root_consistent A root hCard _
  let F := componentSignCompletions A root false .full ∪ componentSignCompletions A root true .full
  refine ⟨F,actual_fillings_component_union_exact A root hW (fun _ => .full) (fun _ => Or.inr (Or.inl rfl)) hSections,?_⟩
  change (componentSignCompletions A root false .full ∪ componentSignCompletions A root true .full).card=8
  rw [Finset.card_union_of_disjoint (component_sign_completions_disjoint A root .full .full),
    component_sign_completions_card,component_sign_completions_card]
  norm_num


def fourConferenceInt : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0,1,1,1; -1,0,-1,1; -1,1,0,-1; -1,-1,1,0]

def conferenceEightStates (i j : Fin 4) : SignedTwoState :=
  if fourConferenceInt i j= -1 then (false,true,true) else (false,false,false)

theorem conference_eight_int_gram :
    normalizedTwoInt conferenceEightStates*(normalizedTwoInt conferenceEightStates).transpose=
      (6:ℤ) • (1 : Matrix (Fin 2×Fin 4) (Fin 2×Fin 4) ℤ) := by decide +kernel

theorem conference_eight_six_candidates :
    (twoZeroHadamardCandidates conferenceEightStates 0).card=6 := by decide +kernel

def twoBlockExampleStates (_ _ : Fin 2) : SignedTwoState := (false,false,false)

theorem two_block_example_int_gram :
    normalizedTwoInt twoBlockExampleStates*(normalizedTwoInt twoBlockExampleStates).transpose=
      (2:ℤ) • (1 : Matrix (Fin 2×Fin 2) (Fin 2×Fin 2) ℤ) := by decide +kernel

theorem two_block_example_eight_candidates :
    (twoZeroHadamardCandidates twoBlockExampleStates 0).card=8 := by decide +kernel


theorem conference_eight_real_gram :
    normalizedTwoReal conferenceEightStates*(normalizedTwoReal conferenceEightStates).transpose=
      ((Fintype.card (Fin 2×Fin 4) : ℝ)-2) • (1 : Matrix (Fin 2×Fin 4) (Fin 2×Fin 4) ℝ) := by
  have h := int_matrix_gram_cast _ 6 conference_eight_int_gram
  convert h using 1 <;> norm_num [normalizedTwoReal]

theorem order_eight_six_actual_fillings :
    ∃ F : Finset (Matrix (Fin 2×Fin 4) (Fin 2×Fin 4) ℝ),
      (∀ H, H∈F ↔ IsZeroBlockHadamardFilling (normalizedTwoReal conferenceEightStates) H) ∧ F.card=6 := by
  classical
  let F := (twoZeroHadamardCandidates conferenceEightStates 0).image
    (fun M => M.map (Int.castRingHom ℝ))
  have hInj : Function.Injective (fun M : Matrix (Fin 2×Fin 4) (Fin 2×Fin 4) ℤ => M.map (Int.castRingHom ℝ)) := by
    intro M N h
    ext p q
    have he := congrArg (fun A : Matrix (Fin 2×Fin 4) (Fin 2×Fin 4) ℝ => A p q) h
    change (M p q : ℝ)=(N p q : ℝ) at he
    exact_mod_cast he
  refine ⟨F,?_,?_⟩
  · intro H
    rw [twoZeroHadamardCandidates_exact conferenceEightStates 0 conference_eight_real_gram H]
    simp only [F,Finset.mem_image]
    constructor
    · rintro ⟨M,hM,hEq⟩; exact ⟨M,hM,hEq.symm⟩
    · rintro ⟨M,hM,hEq⟩; exact ⟨M,hM,hEq.symm⟩
  · rw [Finset.card_image_of_injective _ hInj]
    exact conference_eight_six_candidates


theorem sharp_zero_preserving_fill_cardinalities {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι)
    (hW : normalizedTwoReal A*(normalizedTwoReal A).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (hn : 4∣Fintype.card (Fin 2×ι)) :
    (3≤Fintype.card ι → ∃ F : Finset (Matrix (Fin 2×ι) (Fin 2×ι) ℝ),
      (∀ H, H∈F ↔ IsZeroBlockHadamardFilling (normalizedTwoReal A) H) ∧
      (F.card=0 ∨ F.card=2 ∨ F.card=4 ∨ F.card=6)) ∧
    (normalizedTwoReal conferenceEightStates*(normalizedTwoReal conferenceEightStates).transpose=
      ((Fintype.card (Fin 2×Fin 4) : ℝ)-2) • (1 : Matrix (Fin 2×Fin 4) (Fin 2×Fin 4) ℝ) ∧
      ∃ F : Finset (Matrix (Fin 2×Fin 4) (Fin 2×Fin 4) ℝ),
        (∀ H, H∈F ↔ IsZeroBlockHadamardFilling (normalizedTwoReal conferenceEightStates) H) ∧ F.card=6) ∧
    (Fintype.card ι=2 → ∃ F : Finset (Matrix (Fin 2×ι) (Fin 2×ι) ℝ),
      (∀ H, H∈F ↔ IsZeroBlockHadamardFilling (normalizedTwoReal A) H) ∧ F.card=8) := by
  exact ⟨actual_hadamard_fill_count_zero_two_four_six A root hW hn,
    ⟨conference_eight_real_gram,order_eight_six_actual_fillings⟩,order_four_exactly_eight_fillings A root hW⟩

end CompletionTheory
