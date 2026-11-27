/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.GeneratorCounts
public import CompletionTheory.GridRepair
@[expose] public section
set_option maxHeartbeats 2000000
namespace CompletionTheory
open Module Submodule

noncomputable def finiteNeighborAverage {α : Type*} (N : α → Finset α) (f : α → ℝ) (x : α) : ℝ :=
  (∑ y∈N x,f y)/((N x).card : ℝ)

noncomputable def finiteWalkExpectation {α : Type*} (N : α → Finset α) (f : α → ℝ) : ℕ → α → ℝ
  | 0 => f
  | t+1 => fun x => finiteNeighborAverage N (finiteWalkExpectation N f t) x

theorem finiteNeighborAverage_affine {α : Type*} (N : α → Finset α) (f : α → ℝ)
    (μ β : ℝ) (x : α) (hN : (N x).Nonempty) :
    finiteNeighborAverage N (fun y => μ+β*(f y-μ)) x=μ+β*(finiteNeighborAverage N f x-μ) := by
  have hn : (N x).card≠0 := Finset.card_ne_zero.mpr hN
  have hnR : ((N x).card : ℝ)≠0 := by exact_mod_cast hn
  unfold finiteNeighborAverage
  rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_sub_distrib]
  simp only [Finset.sum_const,nsmul_eq_mul]
  field_simp [hnR]
  all_goals ring

theorem finiteWalkExpectation_affine_eigenfunction {α : Type*} (N : α → Finset α) (f : α → ℝ)
    (hN : ∀ x,(N x).Nonempty) (μ ρ : ℝ)
    (hstep : ∀ x,finiteNeighborAverage N f x=μ+ρ*(f x-μ)) :
    ∀ t x,finiteWalkExpectation N f t x=μ+ρ^t*(f x-μ) := by
  intro t
  induction t with
  | zero => intro x;simp [finiteWalkExpectation]
  | succ t ih =>
    intro x
    change finiteNeighborAverage N (finiteWalkExpectation N f t) x=_
    rw [show finiteWalkExpectation N f t=(fun y => μ+ρ^t*(f y-μ)) from funext ih]
    rw [finiteNeighborAverage_affine N f μ (ρ^t) x (hN x),hstep,pow_succ]
    ring

def retainedCodeState {p : ℕ} [Fact p.Prime]
    (G : Submodule (ZMod p) (Fin (4*p) → ZMod p)) :=
  {C : Submodule (ZMod p) (Fin (4*p) → ZMod p) // C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C ∧ G≤C}

noncomputable def retainedCodeNeighbors {p : ℕ} [Fact p.Prime]
    (G : Submodule (ZMod p) (Fin (4*p) → ZMod p)) (C : retainedCodeState G) :
    Finset (retainedCodeState G) := by
  classical
  let S := restrictedCodeNeighbors C.val G
  let lift : S ↪ retainedCodeState G := {
    toFun := fun D => ⟨D.val,(Finset.mem_filter.mp (Finset.mem_filter.mp D.property).1).2.1,
      (Finset.mem_filter.mp D.property).2⟩
    inj' := by
      intro D E hDE
      exact Subtype.ext (congrArg (fun H : retainedCodeState G => H.val) hDE) }
  exact S.attach.map lift

theorem retainedCodeNeighbors_card {p : ℕ} [Fact p.Prime]
    (G : Submodule (ZMod p) (Fin (4*p) → ZMod p)) (C : retainedCodeState G) :
    (retainedCodeNeighbors G C).card=(restrictedCodeNeighbors C.val G).card := by
  classical
  simp only [retainedCodeNeighbors,Finset.card_map,Finset.card_attach]

theorem retainedCodeNeighbors_sign_sum {p : ℕ} [Fact p.Prime]
    (G : Submodule (ZMod p) (Fin (4*p) → ZMod p)) (C : retainedCodeState G) :
    (∑ D∈retainedCodeNeighbors G C,(codeSignCandidates D.val).card)=
      ∑ D∈restrictedCodeNeighbors C.val G,(codeSignCandidates D).card := by
  classical
  unfold retainedCodeNeighbors
  rw [Finset.sum_map]
  change (∑ D∈(restrictedCodeNeighbors C.val G).attach,(codeSignCandidates D.val).card)=_
  exact Finset.sum_attach (restrictedCodeNeighbors C.val G) (fun D => (codeSignCandidates D).card)

theorem coordinate_self_dual_half_rank {p : ℕ} [Fact p.Prime]
    (C : Submodule (ZMod p) (Fin (4*p) → ZMod p))
    (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C) :
    finrank (ZMod p) C=2*p := by
  have hh := (coordinateDotForm (ZMod p) (4*p)).finrank_add_finrank_orthogonal' C
  rw [← hC,(coordinateDotForm_nondegenerate (ZMod p) (4*p)).ker_eq_bot,
    inf_bot_eq,finrank_bot,add_zero] at hh
  simp only [Module.finrank_pi_fintype,Module.finrank_self,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,Nat.cast_id] at hh
  omega

theorem retainedCodeNeighbors_fixed_degree {p : ℕ} [Fact p.Prime] (hodd : p%2=1)
    (G : Submodule (ZMod p) (Fin (4*p) → ZMod p)) (h : ℕ)
    (hrank : finrank (ZMod p) G+h=2*p) (C : retainedCodeState G) :
    (retainedCodeNeighbors G C).card=(p^h-1)/(p-1) := by
  rw [retainedCodeNeighbors_card,restrictedCodeNeighbors_card hodd C.val G C.property.1 C.property.2]
  have hc := coordinate_self_dual_half_rank C.val C.property.1
  have heq : finrank (ZMod p) C.val-finrank (ZMod p) G=h := by omega
  rw [heq]

theorem code_walk_degree_pos {p h : ℕ} (hp : 2≤p) (hh : 1≤h) : 0<(p^h-1)/(p-1) := by
  have hpow : p≤p^h := by
    have ht := Nat.pow_le_pow_right (by omega : 0<p) hh
    simpa only [pow_one] using ht
  exact Nat.div_pos (by omega) (by omega)

theorem retainedCodeNeighbors_nonempty {p : ℕ} [Fact p.Prime] (hodd : p%2=1)
    (G : Submodule (ZMod p) (Fin (4*p) → ZMod p)) (h : ℕ)
    (hrank : finrank (ZMod p) G+h=2*p) (hh : 1≤h) :
    ∀ C : retainedCodeState G,(retainedCodeNeighbors G C).Nonempty := by
  intro C
  apply Finset.card_pos.mp
  rw [retainedCodeNeighbors_fixed_degree hodd G h hrank C]
  have hp : p.Prime := Fact.out
  exact code_walk_degree_pos hp.two_le hh

noncomputable def retainedCodeSignCount {p : ℕ} [Fact p.Prime]
    (G : Submodule (ZMod p) (Fin (4*p) → ZMod p)) (C : retainedCodeState G) : ℝ :=
  (codeSignCandidates C.val).card

theorem retainedCodeNeighbors_incidence {p : ℕ} [Fact p.Prime] (hodd : p%2=1)
    (G : Submodule (ZMod p) (Fin (4*p) → ZMod p)) (h : ℕ)
    (hrank : finrank (ZMod p) G+h=2*p) (C : retainedCodeState G) :
    (∑ D∈retainedCodeNeighbors G C,(retainedCodeSignCount G D-retainedCodeSignCount G C))=
      ((codeSignCandidates ((coordinateDotForm (ZMod p) (4*p)).orthogonal G)).card : ℝ)-
        retainedCodeSignCount G C-
          (retainedCodeSignCount G C-(codeSignCandidates G).card)*(p : ℝ)^(h-1) := by
  classical
  have hc := coordinate_self_dual_half_rank C.val C.property.1
  have hdiff : finrank (ZMod p) C.val-finrank (ZMod p) G=h := by omega
  have hi := restricted_neighbor_signed_incidence hodd C.val G C.property.1 C.property.2
  rw [hdiff] at hi
  have hiR : (∑ D∈restrictedCodeNeighbors C.val G,
      (((codeSignCandidates D).card : ℝ)-(codeSignCandidates C.val).card))=
      ((codeSignCandidates ((coordinateDotForm (ZMod p) (4*p)).orthogonal G)).card : ℝ)-
        (codeSignCandidates C.val).card-
          ((codeSignCandidates C.val).card-(codeSignCandidates G).card : ℝ)*(p : ℝ)^(h-1) := by
    exact_mod_cast hi
  have hsum := retainedCodeNeighbors_sign_sum G C
  have hsumR : (∑ D∈retainedCodeNeighbors G C,((codeSignCandidates D.val).card : ℝ))=
      ∑ D∈restrictedCodeNeighbors C.val G,((codeSignCandidates D).card : ℝ) := by
    exact_mod_cast hsum
  rw [Finset.sum_sub_distrib] at hiR
  simp only [Finset.sum_const,nsmul_eq_mul] at hiR
  unfold retainedCodeSignCount
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const,nsmul_eq_mul]
  rw [hsumR,retainedCodeNeighbors_card]
  exact hiR

theorem affine_drift_identity (d z P b c : ℝ) (hd : d≠0) (hz : 1+z≠0) :
    c+(P-c-(c-b)*z)/d=
      (b+(P-b)/(1+z))+((d-1-z)/d)*(c-(b+(P-b)/(1+z))) := by
  field_simp [hd,hz]
  ring

theorem code_walk_one_step {p : ℕ} [Fact p.Prime] (hodd : p%2=1)
    (G : Submodule (ZMod p) (Fin (4*p) → ZMod p)) (h : ℕ)
    (hrank : finrank (ZMod p) G+h=2*p) (hh : 1≤h) (C : retainedCodeState G) :
    let b : ℝ := (codeSignCandidates G).card
    let P : ℝ := (codeSignCandidates ((coordinateDotForm (ZMod p) (4*p)).orthogonal G)).card
    let d : ℝ := ((p^h-1)/(p-1) : ℕ)
    let z : ℝ := (p : ℝ)^(h-1)
    finiteNeighborAverage (retainedCodeNeighbors G) (retainedCodeSignCount G) C=
      (b+(P-b)/(1+z))+((d-1-z)/d)*(retainedCodeSignCount G C-(b+(P-b)/(1+z))) := by
  have hp : p.Prime := Fact.out
  have hdN := code_walk_degree_pos hp.two_le hh
  have hdR : (((p^h-1)/(p-1) : ℕ) : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hdN)
  have hz : (1+(p : ℝ)^(h-1))≠0 := by
    have hn : 0≤(p : ℝ)^(h-1) := pow_nonneg (Nat.cast_nonneg p) _
    linarith
  have hi := retainedCodeNeighbors_incidence hodd G h hrank C
  rw [Finset.sum_sub_distrib] at hi
  simp only [Finset.sum_const,nsmul_eq_mul] at hi
  rw [retainedCodeNeighbors_fixed_degree hodd G h hrank C] at hi
  have hmean : finiteNeighborAverage (retainedCodeNeighbors G) (retainedCodeSignCount G) C=
      retainedCodeSignCount G C+
        (((codeSignCandidates ((coordinateDotForm (ZMod p) (4*p)).orthogonal G)).card : ℝ)-
          retainedCodeSignCount G C-(retainedCodeSignCount G C-(codeSignCandidates G).card)*(p : ℝ)^(h-1))/
            (((p^h-1)/(p-1) : ℕ) : ℝ) := by
    unfold finiteNeighborAverage
    rw [retainedCodeNeighbors_fixed_degree hodd G h hrank C]
    apply (div_eq_iff hdR).mpr
    field_simp [hdR]
    nlinarith [hi]
  rw [hmean]
  exact affine_drift_identity _ _ _ _ _ hdR hz

theorem code_walk_degree_real_identity {p h : ℕ} (hp : 2≤p) :
    (((p^h-1)/(p-1) : ℕ) : ℝ)*((p : ℝ)-1)=(p : ℝ)^h-1 := by
  have hp1 : 1≤p := by omega
  have hpow : 1≤p^h := by have hh : 0<p^h := Nat.pow_pos (by omega);omega
  have hh : ((p^h-1)/(p-1))*(p-1)=p^h-1 := by
    rw [← Nat.geomSum_eq hp]
    exact geom_sum_mul_of_one_le hp1 h
  have hc := congrArg (fun n : ℕ => (n : ℝ)) hh
  simpa only [Nat.cast_mul,Nat.cast_sub hp1,Nat.cast_sub hpow,Nat.cast_pow,Nat.cast_one] using hc

theorem code_walk_rho_formula {p h : ℕ} (hp : 2≤p) (hh : 1≤h) :
    let d : ℝ := ((p^h-1)/(p-1) : ℕ)
    (d-1-(p : ℝ)^(h-1))/d=((p : ℝ)^(h-1)-p)/((p : ℝ)^h-1) := by
  have hdN := code_walk_degree_pos hp hh
  have hdR : (((p^h-1)/(p-1) : ℕ) : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hdN)
  have hpowN : p≤p^h := by
    have ht := Nat.pow_le_pow_right (by omega : 0<p) hh
    simpa only [pow_one] using ht
  have hpowR : (p : ℝ)≤(p : ℝ)^h := by exact_mod_cast hpowN
  have hpR : (2 : ℝ)≤p := by exact_mod_cast hp
  have hden : (p : ℝ)^h-1≠0 := by linarith
  have hdegree := code_walk_degree_real_identity (h := h) hp
  have heq : h-1+1=h := by omega
  have hpower : (p : ℝ)^h=(p : ℝ)*(p : ℝ)^(h-1) := by
    have ht := pow_succ (p : ℝ) (h-1)
    rw [heq] at ht
    simpa only [mul_comm] using ht
  apply (div_eq_div_iff hdR hden).mpr
  linear_combination (1+(p : ℝ)^(h-1))*hdegree+((((p^h-1)/(p-1) : ℕ) : ℝ))*hpower

theorem code_walk_rho_bounds {p h : ℕ} (hp : 2≤p) (hh : 2≤h) :
    let d : ℝ := ((p^h-1)/(p-1) : ℕ)
    let ρ := (d-1-(p : ℝ)^(h-1))/d
    (h=2 → ρ=0) ∧ (3≤h → 0<ρ ∧ ρ<1/(p : ℝ)) := by
  have hform := code_walk_rho_formula hp (by omega : 1≤h)
  dsimp only at hform ⊢
  rw [hform]
  constructor
  · intro heq
    subst h
    simp
  · intro hh3
    have hpR : (2 : ℝ)≤p := by exact_mod_cast hp
    have hpPos : (0 : ℝ)<p := by linarith
    have hzN : p^2≤p^(h-1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hzR : (p : ℝ)^2≤(p : ℝ)^(h-1) := by exact_mod_cast hzN
    have hz : (p : ℝ)<(p : ℝ)^(h-1) := by nlinarith
    have heq : h-1+1=h := by omega
    have hpower : (p : ℝ)^h=(p : ℝ)*(p : ℝ)^(h-1) := by
      have ht := pow_succ (p : ℝ) (h-1)
      rw [heq] at ht
      simpa only [mul_comm] using ht
    have hden : (0 : ℝ)<(p : ℝ)^h-1 := by rw [hpower];nlinarith
    refine ⟨div_pos (by linarith) hden,?_⟩
    apply (div_lt_div_iff₀ hden hpPos).mpr
    rw [hpower]
    nlinarith

theorem retained_code_walk_exact_expectation {p : ℕ} [Fact p.Prime] (hodd : p%2=1)
    (G : Submodule (ZMod p) (Fin (4*p) → ZMod p)) (h : ℕ)
    (hrank : finrank (ZMod p) G+h=2*p) (hh : 2≤h) (C₀ : retainedCodeState G) :
    let U := codeSignCandidates ((coordinateDotForm (ZMod p) (4*p)).orthogonal G)
    let A := codeSignCandidates G
    let W := (U \ A).card
    let d : ℝ := ((p^h-1)/(p-1) : ℕ)
    let μ : ℝ := (A.card : ℝ)+(W : ℝ)/(1+(p : ℝ)^(h-1))
    let ρ : ℝ := (d-1-(p : ℝ)^(h-1))/d
    (∀ t : ℕ,finiteWalkExpectation (retainedCodeNeighbors G) (retainedCodeSignCount G) t C₀=
      μ+ρ^t*(retainedCodeSignCount G C₀-μ)) ∧
    (h=2 → ρ=0) ∧ (3≤h → 0<ρ ∧ ρ<1/(p : ℝ)) := by
  let U := codeSignCandidates ((coordinateDotForm (ZMod p) (4*p)).orthogonal G)
  let A := codeSignCandidates G
  let W := (U \ A).card
  let d : ℝ := ((p^h-1)/(p-1) : ℕ)
  let μ : ℝ := (A.card : ℝ)+(W : ℝ)/(1+(p : ℝ)^(h-1))
  let ρ : ℝ := (d-1-(p : ℝ)^(h-1))/d
  have hG : G≤(coordinateDotForm (ZMod p) (4*p)).orthogonal G := by
    intro x hx y hy
    exact ((SetLike.ext_iff.mp C₀.property.1 x).mp (C₀.property.2 hx)) y (C₀.property.2 hy)
  have hAU : A⊆U := codeSignCandidates_mono G _ hG
  have hW : (W : ℝ)=(U.card : ℝ)-(A.card : ℝ) := by
    change ((U \ A).card : ℝ)=_
    rw [Finset.card_sdiff_of_subset hAU,Nat.cast_sub (Finset.card_le_card hAU)]
  have hstep (C : retainedCodeState G) :
      finiteNeighborAverage (retainedCodeNeighbors G) (retainedCodeSignCount G) C=
        μ+ρ*(retainedCodeSignCount G C-μ) := by
    dsimp only [μ,ρ,d]
    rw [hW]
    exact code_walk_one_step hodd G h hrank (by omega) C
  have hwalk := finiteWalkExpectation_affine_eigenfunction (retainedCodeNeighbors G) (retainedCodeSignCount G)
    (retainedCodeNeighbors_nonempty hodd G h hrank (by omega)) μ ρ hstep
  have hp : p.Prime := Fact.out
  have hb := code_walk_rho_bounds hp.two_le hh
  exact ⟨fun t => hwalk t C₀,hb.1,hb.2⟩

end CompletionTheory
