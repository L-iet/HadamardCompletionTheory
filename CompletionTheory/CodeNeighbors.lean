/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.ModularCodeParity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
@[expose] public section
set_option maxHeartbeats 2000000
namespace CompletionTheory
open Module Submodule

theorem pivot_isotropic_pool {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (htwo : (2 : K) ≠ 0)
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (C : Submodule K V) (hC : C=B.orthogonal C)
    (v : V) (hv : v∉C) (hvv : B v v=0) (w : V) (hww : B w w=0) :
    w∈B.orthogonal (bilinearPivotHyperplane B C v) ↔
      w∈C ∨ w∈bilinearCodePivot B C v := by
  classical
  let H := bilinearPivotHyperplane B C v
  let D := bilinearCodePivot B C v
  have hp := self_dual_bilinear_pivot B hB hnd C hC v hv hvv
  have hdim : finrank K C+finrank K C=finrank K V := by
    have hh := B.finrank_add_finrank_orthogonal' C
    rw [← hC,hnd.ker_eq_bot,inf_bot_eq,finrank_bot,add_zero] at hh
    exact hh
  have hinf : C ⊓ K ∙ v=⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hx.2
    by_cases ha0 : a=0
    · simpa [ha0] using ha.symm
    · have hc := C.smul_mem a⁻¹ (ha.symm ▸ hx.1)
      have hvc : v∈C := by simpa [smul_smul,inv_mul_cancel₀ ha0] using hc
      exact (hv hvc).elim
  have hsub : C ⊔ K ∙ v ≤ B.orthogonal H := by
    apply sup_le
    · intro x hx y hy
      have hx' : x∈B.orthogonal C := hC ▸ hx
      exact hx' y hy.1
    · intro x hx y hy
      obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [map_smul,smul_eq_mul,hB.eq y v]
      change a * B v y=0
      rw [hy.2,mul_zero]
  have heq : C ⊔ K ∙ v = B.orthogonal H := by
    apply Submodule.eq_of_le_of_finrank_le hsub
    have hv0 : v≠0 := by intro hz; exact hv (hz ▸ C.zero_mem)
    have hr := Submodule.finrank_sup_add_finrank_inf_eq C (K ∙ v)
    rw [hinf,finrank_bot,add_zero,finrank_span_singleton hv0] at hr
    rw [B.finrank_orthogonal hnd H,hr]
    have hh := hp.2.1
    change finrank K H+1=finrank K C at hh
    omega
  constructor
  · intro hw
    rw [← heq] at hw
    obtain ⟨c,hc,z,hz,rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hz
    rw [← ha] at hww ⊢
    by_cases ha0 : a=0
    · left; simpa [ha0] using hc
    · have hcc : B c c=0 := (hC ▸ hc) c hc
      have hcv : B c v=B v c := hB.eq c v
      have hcalc : 2*a*B v c=0 := by
        simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,
          smul_eq_mul,hcc,hvv,hcv,mul_zero,zero_mul,zero_add,add_zero] at hww
        linear_combination hww
      have hvc : B v c=0 := (mul_eq_zero.mp hcalc).resolve_left (mul_ne_zero htwo ha0)
      right
      exact Submodule.add_mem D (Submodule.mem_sup_left ⟨hc,hvc⟩)
        (Submodule.mem_sup_right (Submodule.mem_span_singleton.mpr ⟨a,rfl⟩))
  · rintro (hw|hw)
    · exact hsub (Submodule.mem_sup_left hw)
    · intro y hy
      have hw' : w∈B.orthogonal D := hp.1 ▸ hw
      exact hw' y (Submodule.mem_sup_left hy)

theorem pivot_unique_other_self_dual {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (htwo : (2 : K) ≠ 0)
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (C : Submodule K V) (hC : C=B.orthogonal C)
    (v : V) (hv : v∉C) (hvv : B v v=0)
    (E : Submodule K V) (hE : E=B.orthogonal E)
    (hHE : bilinearPivotHyperplane B C v ≤ E) (hne : E≠C) :
    E=bilinearCodePivot B C v := by
  classical
  let D := bilinearCodePivot B C v
  have hp := self_dual_bilinear_pivot B hB hnd C hC v hv hvv
  have dimself (F : Submodule K V) (hF : F=B.orthogonal F) :
      finrank K F+finrank K F=finrank K V := by
    have hh := B.finrank_add_finrank_orthogonal' F
    rw [← hF,hnd.ker_eq_bot,inf_bot_eq,finrank_bot,add_zero] at hh
    exact hh
  have hdimEC : finrank K E=finrank K C := by
    have := dimself E hE
    have := dimself C hC
    omega
  have hnsub : ¬E≤C := by
    intro hle
    exact hne (Submodule.eq_of_le_of_finrank_le hle hdimEC.ge)
  obtain ⟨e,heE,heC⟩ := SetLike.not_le_iff_exists.mp hnsub
  have pool (x : V) (hx : x∈E) : x∈C ∨ x∈D := by
    apply (pivot_isotropic_pool htwo B hB hnd C hC v hv hvv x ((hE ▸ hx) x hx)).mp
    intro y hy
    exact (hE ▸ hx) y (hHE hy)
  have heD : e∈D := (pool e heE).resolve_left heC
  have hED : E≤D := by
    intro x hx
    by_contra hxD
    have hxC := (pool x hx).resolve_right hxD
    rcases pool (x+e) (E.add_mem hx heE) with hsumC|hsumD
    · exact heC (by simpa using C.sub_mem hsumC hxC)
    · exact hxD (by simpa using D.sub_mem hsumD heD)
  apply Submodule.eq_of_le_of_finrank_le hED
  change finrank K (bilinearCodePivot B C v) ≤ finrank K E
  rw [hp.2.2.2.1,hdimEC]

theorem hyperplane_isotropic_pivot_exists {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (htwo : (2 : K) ≠ 0)
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (C H : Submodule K V) (hC : C=B.orthogonal C) (hHC : H≤C)
    (hcodim : finrank K H+1=finrank K C) :
    ∃ v : V,v∉C ∧ B v v=0 ∧ bilinearPivotHyperplane B C v=H := by
  classical
  have hdim : finrank K C+finrank K C=finrank K V := by
    have hh := B.finrank_add_finrank_orthogonal' C
    rw [← hC,hnd.ker_eq_bot,inf_bot_eq,finrank_bot,add_zero] at hh
    exact hh
  have hnle : ¬B.orthogonal H≤C := by
    intro hle
    have hh := Submodule.finrank_mono hle
    rw [B.finrank_orthogonal hnd H] at hh
    omega
  obtain ⟨w,hwH,hwC⟩ := SetLike.not_le_iff_exists.mp hnle
  have hwNotOrth : w∉B.orthogonal C := by rwa [← hC]
  have hex : ∃ e∈C,B e w≠0 := by
    by_contra hn
    apply hwNotOrth
    intro e he
    by_contra hne
    exact hn ⟨e,he,hne⟩
  obtain ⟨e,heC,hew⟩ := hex
  let a : K := B w w/(2*B e w)
  let v := w-a • e
  have hvC : v∉C := by
    intro hv
    apply hwC
    have hh := C.add_mem hv (C.smul_mem a heC)
    simpa [v] using hh
  have hee : B e e=0 := (hC ▸ heC) e heC
  have hvv : B v v=0 := by
    dsimp [v]
    simp only [map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul,hee,mul_zero,sub_zero]
    rw [hB.eq w e]
    dsimp [a]
    field_simp
    <;> ring
  have hHv : H≤bilinearPivotHyperplane B C v := by
    intro x hx
    refine ⟨hHC hx,?_⟩
    change B v x=0
    have hwx : B w x=0 := by rw [hB.eq w x];exact hwH x hx
    have hex : B e x=0 := (hC ▸ hHC hx) e heC
    simp [v,map_sub,map_smul,hwx,hex]
  have hp := self_dual_bilinear_pivot B hB hnd C hC v hvC hvv
  have heq : H=bilinearPivotHyperplane B C v := by
    apply Submodule.eq_of_le_of_finrank_le hHv
    have hh := hp.2.1
    omega
  exact ⟨v,hvC,hvv,heq.symm⟩

theorem hyperplane_two_self_dual_spaces {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (htwo : (2 : K) ≠ 0)
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (C H : Submodule K V) (hC : C=B.orthogonal C) (hHC : H≤C)
    (hcodim : finrank K H+1=finrank K C) :
    ∃ D : Submodule K V,D=B.orthogonal D ∧ D≠C ∧ C ⊓ D=H ∧
      (∀ w : V,B w w=0 → (w∈B.orthogonal H ↔ w∈C ∨ w∈D)) ∧
      ∀ E : Submodule K V,E=B.orthogonal E → H≤E → E≠C → E=D := by
  obtain ⟨v,hv,hvv,hH⟩ := hyperplane_isotropic_pivot_exists htwo B hB hnd C H hC hHC hcodim
  have hp := self_dual_bilinear_pivot B hB hnd C hC v hv hvv
  refine ⟨bilinearCodePivot B C v,hp.1,?_,hp.2.2.1.trans hH,?_,?_⟩
  · intro heq
    exact hv (heq ▸ hp.2.2.2.2)
  · intro w hww
    rw [← hH]
    exact pivot_isotropic_pool htwo B hB hnd C hC v hv hvv w hww
  · intro E hE hHE hne
    exact pivot_unique_other_self_dual htwo B hB hnd C hC v hv hvv E hE (hH ▸ hHE) hne

theorem signResidue_isotropic {p : ℕ} [Fact p.Prime] (x : Fin (4*p) → Bool) :
    coordinateDotForm (ZMod p) (4*p) (fun j => (modularBitSign (x j) : ZMod p))
      (fun j => (modularBitSign (x j) : ZMod p))=0 := by
  have hs (j : Fin (4*p)) : modularBitSign (x j)*modularBitSign (x j)=1 := by
    rcases modularBitSign_sign (x j) with h|h <;> simp [h]
  change (∑ j,(modularBitSign (x j) : ZMod p)*(modularBitSign (x j) : ZMod p))=0
  simp only [← Int.cast_mul,hs,Int.cast_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one,Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_self,mul_zero]

theorem two_code_sign_pool {p : ℕ} [Fact p.Prime] (hodd : p%2=1)
    (C G : Submodule (ZMod p) (Fin (4*p) → ZMod p))
    (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C) (hGC : G≤C)
    (hcodim : finrank (ZMod p) G+1=finrank (ZMod p) C) :
    ∃ D : Submodule (ZMod p) (Fin (4*p) → ZMod p),
      D=(coordinateDotForm (ZMod p) (4*p)).orthogonal D ∧ D≠C ∧ C ⊓ D=G ∧
      (∀ E : Submodule (ZMod p) (Fin (4*p) → ZMod p),
        E=(coordinateDotForm (ZMod p) (4*p)).orthogonal E → G≤E → E≠C → E=D) ∧
      codeSignCandidates ((coordinateDotForm (ZMod p) (4*p)).orthogonal G)=
        codeSignCandidates C ∪ codeSignCandidates D ∧
      codeSignCandidates C ∩ codeSignCandidates D=codeSignCandidates G ∧
      (codeSignCandidates D).card+(codeSignCandidates C).card=
        (codeSignCandidates ((coordinateDotForm (ZMod p) (4*p)).orthogonal G)).card+
          (codeSignCandidates G).card := by
  classical
  have hp : p.Prime := Fact.out
  have htwo : (2 : ZMod p)≠0 := by
    intro hz
    have hd : p∣2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have hp2 : p=2 := (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left hp.ne_one
    omega
  obtain ⟨D,hD,hne,hinter,hpool,hunique⟩ := hyperplane_two_self_dual_spaces htwo
    (coordinateDotForm (ZMod p) (4*p)) (coordinateDotForm_symm _ _)
      (coordinateDotForm_nondegenerate _ _) C G hC hGC hcodim
  have hunion : codeSignCandidates ((coordinateDotForm (ZMod p) (4*p)).orthogonal G)=
      codeSignCandidates C ∪ codeSignCandidates D := by
    ext x
    simp only [codeSignCandidates,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
    rw [hpool _ (signResidue_isotropic x)]
    tauto
  have hintersection : codeSignCandidates C ∩ codeSignCandidates D=codeSignCandidates G := by
    ext x
    simp only [codeSignCandidates,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_inter]
    have hm := SetLike.ext_iff.mp hinter (fun j => (modularBitSign (x j) : ZMod p))
    change (_∈C ∧ _∈D ↔ _∈G) at hm
    tauto
  refine ⟨D,hD,hne,hinter,hunique,hunion,hintersection,?_⟩
  have hh := Finset.card_union_add_card_inter (codeSignCandidates C) (codeSignCandidates D)
  rw [← hunion,hintersection] at hh
  omega

theorem two_code_pool_real_frames {p : ℕ} [Fact p.Prime] (hodd : p%2=1)
    (C D G : Submodule (ZMod p) (Fin (4*p) → ZMod p))
    (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C)
    (hD : D=(coordinateDotForm (ZMod p) (4*p)).orthogonal D)
    (hGC : G≤C) (hGD : G≤D)
    (a : Fin 5 → Fin (4*p) → Bool) (ha : ∀ i,a i∈codeSignCandidates G)
    (hgram : ∀ i j,(∑ k,modularBitSign (a i k)*modularBitSign (a j k))=
      if i=j then (4*p : ℤ) else 0) :
    IsPartialHadamard (signFamilyMatrix (codeSignCandidates C)) ∧
      IsPartialHadamard (signFamilyMatrix (codeSignCandidates D)) ∧
      5≤(codeSignCandidates C).card ∧ (codeSignCandidates C).card≤4*p ∧
      5≤(codeSignCandidates D).card ∧ (codeSignCandidates D).card≤4*p := by
  have hp : p.Prime := Fact.out
  have orth (E : Submodule (ZMod p) (Fin (4*p) → ZMod p))
      (hE : E=(coordinateDotForm (ZMod p) (4*p)).orthogonal E) :
      IsSelfOrthogonalModularCode E := by
    intro u hu v hv
    exact (hE ▸ hv) u hu
  have mem (E : Submodule (ZMod p) (Fin (4*p) → ZMod p)) (hle : G≤E)
      (i : Fin 5) : a i∈codeSignCandidates E := by
    classical
    obtain ⟨_,hi,hv⟩ := Finset.mem_filter.mp (ha i)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,hle hv⟩
  have hc := five_rows_remove_code_compatibility hp.pos hodd C (orth C hC) a (mem C hGC) hgram
  have hd := five_rows_remove_code_compatibility hp.pos hodd D (orth D hD) a (mem D hGD) hgram
  exact ⟨signFamilyMatrix_partial _ hc.1,signFamilyMatrix_partial _ hd.1,
    hc.2.1,hc.2.2,hd.2.1,hd.2.2⟩

theorem nonzero_functionals_same_kernel {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f g : Module.Dual K V) (hf : f≠0) (hg : g≠0) :
    LinearMap.ker f=LinearMap.ker g ↔ ∃ a : K,a≠0 ∧ g=a • f := by
  classical
  constructor
  · intro hker
    obtain ⟨e,he⟩ : ∃ e : V,f e≠0 := by
      by_contra hn
      apply hf
      ext x
      by_contra hx
      exact hn ⟨x,hx⟩
    have hge : g e≠0 := by
      intro hz
      have hm : e∈LinearMap.ker g := hz
      rw [← hker] at hm
      exact he hm
    refine ⟨g e/f e,div_ne_zero hge he,?_⟩
    ext x
    have hx : x-(f x/f e) • e∈LinearMap.ker f := by
      change f (x-(f x/f e) • e)=0
      simp [he]
    rw [hker] at hx
    change g (x-(f x/f e) • e)=0 at hx
    simp only [map_sub,map_smul,smul_eq_mul] at hx
    change g x=(g e/f e)*f x
    have hh : (g e/f e)*f x=(f x/f e)*g e := by ring
    rw [hh]
    exact sub_eq_zero.mp hx
  · rintro ⟨a,ha,rfl⟩
    ext x
    simp [ha]

theorem pivot_hyperplane_syndrome_label {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (C : Submodule K V) (hC : C=B.orthogonal C) (b : Basis ι K C)
    (v w : V) (hv : v∉C) (hw : w∉C) :
    bilinearPivotHyperplane B C v=bilinearPivotHyperplane B C w ↔
      ∃ a : K,a≠0 ∧ ∀ i,B w (b i)=a*B v (b i) := by
  let f : Module.Dual K C := (B v).comp C.subtype
  let g : Module.Dual K C := (B w).comp C.subtype
  have nonzero (x : V) (hx : x∉C) : (B x).comp C.subtype≠0 := by
    intro hz
    apply hx
    rw [hC]
    intro c hc
    have hh := LinearMap.congr_fun hz ⟨c,hc⟩
    change B x c=0 at hh
    rw [hB.eq c x]
    exact hh
  have hker : bilinearPivotHyperplane B C v=bilinearPivotHyperplane B C w ↔
      LinearMap.ker f=LinearMap.ker g := by
    constructor
    · intro h
      ext x
      have hh := SetLike.ext_iff.mp h x.val
      change (x.val∈C ∧ B v x.val=0 ↔ x.val∈C ∧ B w x.val=0) at hh
      simpa [f,g,x.property] using hh
    · intro h
      ext x
      by_cases hx : x∈C
      · have hh := SetLike.ext_iff.mp h (⟨x,hx⟩ : C)
        simpa [bilinearPivotHyperplane,f,g,hx] using hh
      · simp [bilinearPivotHyperplane,hx]
  rw [hker,nonzero_functionals_same_kernel f g (nonzero v hv) (nonzero w hw)]
  constructor
  · rintro ⟨a,ha,heq⟩
    refine ⟨a,ha,?_⟩
    intro i
    exact LinearMap.congr_fun heq (b i)
  · rintro ⟨a,ha,heq⟩
    refine ⟨a,ha,?_⟩
    apply b.ext
    intro i
    exact heq i

def IsBilinearCodeNeighbor {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (C D : Submodule K V) : Prop :=
  D=B.orthogonal D ∧ D≠C ∧ finrank K ↥(C ⊓ D)+1=finrank K C

theorem isotropic_vector_unique_neighbor {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (htwo : (2 : K) ≠ 0)
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (C : Submodule K V) (hC : C=B.orthogonal C)
    (v : V) (hv : v∉C) (hvv : B v v=0) :
    ∃! D : Submodule K V,IsBilinearCodeNeighbor B C D ∧ v∈D := by
  have hp := self_dual_bilinear_pivot B hB hnd C hC v hv hvv
  refine ⟨bilinearCodePivot B C v,⟨?_,hp.2.2.2.2⟩,?_⟩
  · refine ⟨hp.1,?_,?_⟩
    · intro heq
      exact hv (heq ▸ hp.2.2.2.2)
    · rw [hp.2.2.1]
      exact hp.2.1
  · intro E hE
    have hle : C ⊓ E≤bilinearPivotHyperplane B C v := by
      intro x hx
      refine ⟨hx.1,?_⟩
      have hxE : x∈B.orthogonal E := hE.1.1 ▸ hx.2
      exact hxE v hE.2
    have heq : C ⊓ E=bilinearPivotHyperplane B C v := by
      apply Submodule.eq_of_le_of_finrank_le hle
      have h1 := hE.1.2.2
      have h2 := hp.2.1
      omega
    have hHE : bilinearPivotHyperplane B C v≤E := by
      rw [← heq]
      exact inf_le_right
    exact pivot_unique_other_self_dual htwo B hB hnd C hC v hv hvv E hE.1.1 hHE hE.1.2.1

theorem sign_vector_unique_code_neighbor {p : ℕ} [Fact p.Prime] (hodd : p%2=1)
    (C : Submodule (ZMod p) (Fin (4*p) → ZMod p))
    (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C)
    (x : Fin (4*p) → Bool) (hx : (fun j => (modularBitSign (x j) : ZMod p))∉C) :
    ∃! D : Submodule (ZMod p) (Fin (4*p) → ZMod p),
      IsBilinearCodeNeighbor (coordinateDotForm (ZMod p) (4*p)) C D ∧
        (fun j => (modularBitSign (x j) : ZMod p))∈D := by
  have hp : p.Prime := Fact.out
  have htwo : (2 : ZMod p)≠0 := by
    intro hz
    have hd : p∣2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have hp2 : p=2 := (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left hp.ne_one
    omega
  exact isotropic_vector_unique_neighbor htwo (coordinateDotForm (ZMod p) (4*p))
    (coordinateDotForm_symm _ _) (coordinateDotForm_nondegenerate _ _) C hC
      _ hx (signResidue_isotropic x)

noncomputable def selfDualCodeNeighbors {p : ℕ} [Fact p.Prime]
    (C : Submodule (ZMod p) (Fin (4*p) → ZMod p)) :
    Finset (Submodule (ZMod p) (Fin (4*p) → ZMod p)) := by
  classical
  letI : Fintype (Submodule (ZMod p) (Fin (4*p) → ZMod p)) :=
    Fintype.ofInjective (fun E => (E : Set (Fin (4*p) → ZMod p))) SetLike.coe_injective
  exact Finset.univ.filter (IsBilinearCodeNeighbor (coordinateDotForm (ZMod p) (4*p)) C)

theorem codeSignCandidates_inf {p N : ℕ}
    (C D : Submodule (ZMod p) (Fin N → ZMod p)) :
    codeSignCandidates (C ⊓ D)=codeSignCandidates C ∩ codeSignCandidates D := by
  classical
  ext x
  simp only [codeSignCandidates,Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_inter,Submodule.mem_inf]
  tauto

noncomputable def normalizedSignCube (N : ℕ) : Finset (Fin N → Bool) := by
  classical
  exact Finset.univ.filter positiveFirstBit

theorem syndrome_neighbor_census {p : ℕ} [Fact p.Prime] (hodd : p%2=1)
    (C : Submodule (ZMod p) (Fin (4*p) → ZMod p))
    (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C) :
    (∑ D∈selfDualCodeNeighbors C,(codeSignCandidates D \ codeSignCandidates C).card)=
      (normalizedSignCube (4*p) \ codeSignCandidates C).card ∧
    (∀ D∈selfDualCodeNeighbors C,(codeSignCandidates D).card=
      (codeSignCandidates (C ⊓ D)).card+(codeSignCandidates D \ codeSignCandidates C).card) ∧
    (∀ D∈selfDualCodeNeighbors C,codeSignCandidates D \ codeSignCandidates C=∅ →
      (codeSignCandidates D).card≤(codeSignCandidates C).card) := by
  classical
  let s := selfDualCodeNeighbors C
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
    have hDm : IsBilinearCodeNeighbor (coordinateDotForm (ZMod p) (4*p)) C D :=
      (Finset.mem_filter.mp hD).2
    have hEm : IsBilinearCodeNeighbor (coordinateDotForm (ZMod p) (4*p)) C E :=
      (Finset.mem_filter.mp hE).2
    exact hne ((hunique D ⟨hDm,(Finset.mem_filter.mp hxD).2.2⟩).trans
      (hunique E ⟨hEm,(Finset.mem_filter.mp hxE).2.2⟩).symm)
  have hunion : s.biUnion t=normalizedSignCube (4*p) \ codeSignCandidates C := by
    ext x
    constructor
    · intro hx
      obtain ⟨D,hD,hxD⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨hxD,hxC⟩ := Finset.mem_sdiff.mp hxD
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,(Finset.mem_filter.mp hxD).2.1⟩,hxC⟩
    · intro hx
      obtain ⟨hxfirst,hxC⟩ := Finset.mem_sdiff.mp hx
      have hnC : (fun j => (modularBitSign (x j) : ZMod p))∉C := by
        intro hc
        exact hxC (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hxfirst).2,hc⟩)
      obtain ⟨D,hD,_⟩ := sign_vector_unique_code_neighbor hodd C hC x hnC
      apply Finset.mem_biUnion.mpr
      refine ⟨D,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hD.1⟩,?_⟩
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,(Finset.mem_filter.mp hxfirst).2,hD.2⟩,hxC⟩
  refine ⟨?_,?_,?_⟩
  · have hh := Finset.card_biUnion hdisjoint
    rw [hunion] at hh
    exact hh.symm
  · intro D _
    rw [codeSignCandidates_inf,Finset.inter_comm]
    exact (Finset.card_inter_add_card_sdiff (codeSignCandidates D) (codeSignCandidates C)).symm
  · intro D _ he
    apply Finset.card_le_card
    intro x hx
    by_contra hn
    have hm : x∈codeSignCandidates D \ codeSignCandidates C := Finset.mem_sdiff.mpr ⟨hx,hn⟩
    rw [he] at hm
    simp at hm

end CompletionTheory
