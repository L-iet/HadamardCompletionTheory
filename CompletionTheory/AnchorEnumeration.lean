/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.RationalDilation
public import CompletionTheory.InformationCoordinates
public import CompletionTheory.ResidualFactor
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Dimension.Constructions
@[expose] public section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory
open Matrix Module Submodule

theorem row_gram_linearIndependent {K δ κ : Type*} [Field K] [Fintype δ] [DecidableEq δ]
    [Fintype κ] (B : Matrix δ κ K) (n : K) (hn : n≠0) (hB : B*Bᵀ=n • 1) :
    LinearIndependent K B.row := by
  rw [← Matrix.vecMul_injective_iff]
  intro x y hxy
  have hh := congrArg (fun z => Matrix.vecMul z Bᵀ) hxy
  simp only [Matrix.vecMul_vecMul,hB,Matrix.vecMul_smul,Matrix.vecMul_one] at hh
  funext i
  have hi := congrFun hh i
  change n*x i=n*y i at hi
  exact mul_left_cancel₀ hn hi

theorem full_row_gram_anchor_exists {K δ κ : Type*} [Field K] [Fintype δ] [DecidableEq δ]
    [Fintype κ] (B : Matrix δ κ K) (n : K) (hn : n≠0) (hB : B*Bᵀ=n • 1) :
    ∃ a : δ → κ,Function.Injective a ∧ (B.submatrix id a).det≠0 := by
  classical
  have hli := row_gram_linearIndependent B n hn hB
  let V := Submodule.span K (Set.range B.row)
  obtain ⟨J,instJ,a,ha,hcard,hinj⟩ := exists_information_coordinates V
  letI : Fintype J := instJ
  have hdim : finrank K V=Fintype.card δ := finrank_span_eq_card hli
  let e : δ ≃ J := Fintype.equivOfCardEq (by omega : Fintype.card δ=Fintype.card J)
  let L : (κ → K) →ₗ[K] (δ → K) := LinearMap.pi (fun j => LinearMap.proj (a (e j)))
  have hLin : Set.InjOn L V := by
    intro u hu v hv huv
    have hres : (fun j : J => u (a j))=(fun j : J => v (a j)) := by
      funext j
      have hh := congrFun huv (e.symm j)
      change u (a (e (e.symm j)))=v (a (e (e.symm j))) at hh
      simpa only [Equiv.apply_symm_apply] using hh
    have hh : (⟨u,hu⟩ : V)=(⟨v,hv⟩ : V) := hinj hres
    exact congrArg Subtype.val hh
  have hmap := hli.map_injOn L hLin
  have hS : LinearIndependent K (B.submatrix id (fun j => a (e j))).row := hmap
  have hunit : IsUnit (B.submatrix id (fun j => a (e j))) := Matrix.linearIndependent_row_iff_isUnit.mp hS
  refine ⟨fun j => a (e j),ha.comp e.injective,?_⟩
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero

theorem residual_principal_anchor_exists {δ ι : Type*} [Fintype δ] [Fintype ι]
    [DecidableEq δ] [DecidableEq ι] [Nonempty δ]
    (P : Matrix ι (δ ⊕ ι) ℝ) (hP : IsPartialHadamard P) :
    ∃ a : δ → (δ ⊕ ι),Function.Injective a ∧ ((residualGram P).submatrix a a).det≠0 := by
  classical
  obtain ⟨B,hfactor,hrow⟩ := real_residual_factor P hP
  have hn : (Fintype.card (δ ⊕ ι) : ℝ)≠0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card (δ ⊕ ι)≠0)
  obtain ⟨a,ha,hdet⟩ := full_row_gram_anchor_exists B _ hn hrow
  have hsub : (residualGram P).submatrix a a=(B.submatrix id a)ᵀ*(B.submatrix id a) := by
    rw [← hfactor]
    ext i j
    simp only [Matrix.submatrix_apply,Matrix.mul_apply,Matrix.transpose_apply,id_eq]
  refine ⟨a,ha,?_⟩
  rw [hsub,Matrix.det_mul,Matrix.det_transpose]
  exact mul_ne_zero hdet hdet

def IsBinaryMatrix {K δ κ : Type*} [One K] [Neg K] (B : Matrix δ κ K) : Prop :=
  ∀ i j,B i j=1 ∨ B i j= -1

def signAnchorMatrix {K δ : Type*} [One K] [Neg K] (σ : δ×δ → Bool) : Matrix δ δ K :=
  fun i j => if σ (i,j) then -1 else 1

noncomputable def anchorSolve {K δ κ : Type*} [Field K] [Fintype δ] [DecidableEq δ]
    (C : Matrix κ κ K) (a : δ → κ) (S : Matrix δ δ K) : Matrix δ κ K :=
  (Sᵀ)⁻¹*C.submatrix a id

theorem sign_anchor_cardinality (δ : Type*) [Fintype δ] [DecidableEq δ] :
    Fintype.card (δ×δ → Bool)=2^(Fintype.card δ*Fintype.card δ) := by simp

theorem fixed_anchor_factorization_iff {K δ κ : Type*} [Field K] [Fintype δ] [DecidableEq δ]
    [Fintype κ] (C : Matrix κ κ K) (a : δ → κ) (hdet : (C.submatrix a a).det≠0) :
    (∃ B : Matrix δ κ K,IsBinaryMatrix B ∧ Bᵀ*B=C) ↔
      ∃ σ : δ×δ → Bool,(signAnchorMatrix (K := K) σ).det≠0 ∧
        IsBinaryMatrix (anchorSolve C a (signAnchorMatrix σ)) ∧
        (anchorSolve C a (signAnchorMatrix σ))ᵀ*anchorSolve C a (signAnchorMatrix σ)=C := by
  classical
  constructor
  · rintro ⟨B,hB,hgram⟩
    let S := B.submatrix id a
    have hS : IsBinaryMatrix S := fun i j => hB i (a j)
    have hprincipal : C.submatrix a a=Sᵀ*S := by
      rw [← hgram]
      ext i j
      simp only [S,Matrix.submatrix_apply,Matrix.mul_apply,Matrix.transpose_apply,id_eq]
    have hdetS : S.det≠0 := by
      intro hz
      apply hdet
      rw [hprincipal,Matrix.det_mul,Matrix.det_transpose,hz,zero_mul]
    have hcross : C.submatrix a id=Sᵀ*B := by
      rw [← hgram]
      ext i j
      simp only [S,Matrix.submatrix_apply,Matrix.mul_apply,Matrix.transpose_apply,id_eq]
    have hunit : IsUnit (Sᵀ).det := by
      rw [Matrix.det_transpose]
      exact isUnit_iff_ne_zero.mpr hdetS
    have hsolve : anchorSolve C a S=B := by
      rw [anchorSolve,hcross]
      exact Matrix.nonsing_inv_mul_cancel_left (Sᵀ) B hunit
    let σ : δ×δ → Bool := fun ij => decide (S ij.1 ij.2≠1)
    have hσ : signAnchorMatrix σ=S := by
      ext i j
      by_cases h : S i j=1
      · have hc : σ (i,j)=false := by simp [σ,h]
        simp only [signAnchorMatrix,hc,ite_false]
        exact h.symm
      · have hn : S i j= -1 := (hS i j).resolve_left h
        have hc : σ (i,j)=true := by simp [σ,h]
        simp only [signAnchorMatrix,hc,ite_true]
        exact hn.symm
    refine ⟨σ,?_,?_,?_⟩
    · simpa only [hσ] using hdetS
    · rw [hσ,hsolve]
      exact hB
    · rw [hσ,hsolve]
      exact hgram
  · rintro ⟨σ,_,hsign,hgram⟩
    exact ⟨anchorSolve C a (signAnchorMatrix σ),hsign,hgram⟩


theorem residualGram_entry_bound {δ ι : Type*} [Fintype δ] [Fintype ι]
    [DecidableEq δ] [DecidableEq ι] [Nonempty δ]
    (P : Matrix ι (δ ⊕ ι) ℝ) (hP : IsPartialHadamard P) (i j : δ ⊕ ι) :
    -(Fintype.card δ : ℝ)≤residualGram P i j ∧ residualGram P i j≤(Fintype.card δ : ℝ) := by
  obtain ⟨B,hfactor,_⟩ := real_residual_factor P hP
  have hdiag (i : δ ⊕ ι) : (∑ a,(B a i)^2)=(Fintype.card δ : ℝ) := by
    have hh := congrArg (fun M => M i i) hfactor
    simp only [Matrix.mul_apply,Matrix.transpose_apply] at hh
    simpa only [pow_two,residualGram_diagonal P hP.1 i] using hh
  have hcross : (∑ a,B a i*B a j)=residualGram P i j := by
    have hh := congrArg (fun M => M i j) hfactor
    simpa only [Matrix.mul_apply,Matrix.transpose_apply] using hh
  have hp := Finset.sum_nonneg (s := Finset.univ) (fun a _ => sq_nonneg (B a i+B a j))
  have hm := Finset.sum_nonneg (s := Finset.univ) (fun a _ => sq_nonneg (B a i-B a j))
  have heP (a : δ) : (B a i+B a j)^2=(B a i)^2+2*(B a i*B a j)+(B a j)^2 := by ring
  have heM (a : δ) : (B a i-B a j)^2=(B a i)^2-2*(B a i*B a j)+(B a j)^2 := by ring
  simp_rw [heP] at hp
  simp_rw [heM] at hm
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.mul_sum,hdiag,hdiag,hcross] at hp
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,hdiag,hdiag,hcross] at hm
  constructor <;> linarith

theorem residualGram_entry_alphabet {δ ι : Type*} [Fintype δ] [Fintype ι]
    [DecidableEq δ] [DecidableEq ι] [Nonempty δ]
    (P : Matrix ι (δ ⊕ ι) ℝ) (hP : IsPartialHadamard P)
    (heven : Even (Fintype.card (δ ⊕ ι))) (i j : δ ⊕ ι) :
    ∃ k : Fin (Fintype.card δ+1),residualGram P i j=(Fintype.card δ : ℝ)-2*(k.val : ℝ) := by
  by_cases hij : i=j
  · subst j
    exact ⟨⟨0,by omega⟩,by rw [residualGram_diagonal P hP.1]; norm_num⟩
  · obtain ⟨z,hz⟩ := residualGram_offDiagonal_parity P hP.1 heven i j hij
    obtain ⟨hl,hu⟩ := residualGram_entry_bound P hP i j
    have hzneg : z≤0 := by exact_mod_cast (show (z : ℝ)≤0 by linarith)
    have hzlow : -(Fintype.card δ : ℤ)≤z := by
      exact_mod_cast (show -(Fintype.card δ : ℝ)≤(z : ℝ) by linarith)
    let k := (-z).toNat
    have hk : k<Fintype.card δ+1 := by dsimp [k]; omega
    have hkI : (k : ℤ)= -z := Int.toNat_of_nonneg (by omega)
    have hkR : (k : ℝ)= -(z : ℝ) := by exact_mod_cast hkI
    exact ⟨⟨k,hk⟩,by simp only [hkR]; linarith⟩

noncomputable def residualCorrelationTypes (δ : Type*) [Fintype δ] [DecidableEq δ] : Finset (δ → ℝ) := by
  classical
  exact Finset.univ.image (fun k : δ → Fin (Fintype.card δ+1) =>
    fun i => (Fintype.card δ : ℝ)-2*(k i).val)

theorem residualCorrelationTypes_card (δ : Type*) [Fintype δ] [DecidableEq δ] :
    (residualCorrelationTypes δ).card≤(Fintype.card δ+1)^(Fintype.card δ) := by
  classical
  have hh := Finset.card_image_le (s := (Finset.univ : Finset (δ → Fin (Fintype.card δ+1))))
    (f := fun k => fun i => (Fintype.card δ : ℝ)-2*(k i).val)
  simpa only [residualCorrelationTypes,Finset.card_univ,Fintype.card_fun,Fintype.card_fin] using hh

theorem residualGram_columns_in_types {δ ι : Type*} [Fintype δ] [Fintype ι]
    [DecidableEq δ] [DecidableEq ι] [Nonempty δ]
    (P : Matrix ι (δ ⊕ ι) ℝ) (hP : IsPartialHadamard P)
    (heven : Even (Fintype.card (δ ⊕ ι))) (a : δ → (δ ⊕ ι)) (j : δ ⊕ ι) :
    (fun i => residualGram P (a i) j)∈residualCorrelationTypes δ := by
  classical
  choose k hk using (fun i : δ => residualGram_entry_alphabet P hP heven (a i) j)
  apply Finset.mem_image.mpr
  exact ⟨k,Finset.mem_univ _,funext (fun i => (hk i).symm)⟩


noncomputable def rationalResidualGram {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (P : Matrix ι κ ℝ) : Matrix κ κ ℚ :=
  (Fintype.card κ : ℚ) • 1-(rationalSignMatrix P)ᵀ*rationalSignMatrix P

theorem realOfRationalMatrix_transpose {ι κ : Type*} (A : Matrix ι κ ℚ) :
    realOfRationalMatrix Aᵀ=(realOfRationalMatrix A)ᵀ := rfl

theorem realOfRationalMatrix_injective {ι κ : Type*} :
    Function.Injective (realOfRationalMatrix : Matrix ι κ ℚ → Matrix ι κ ℝ) := by
  intro A B h
  ext i j
  apply Rat.cast_injective (α := ℝ)
  exact congrArg (fun M => M i j) h

theorem rational_matrix_det_cast {δ : Type*} [Fintype δ] [DecidableEq δ] (A : Matrix δ δ ℚ) :
    (A.det : ℝ)=(realOfRationalMatrix A).det := by
  exact (Rat.castHom ℝ).map_det A

theorem rationalResidualGram_cast {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (P : Matrix ι κ ℝ) (hs : IsSignMatrix P) : realOfRationalMatrix (rationalResidualGram P)=residualGram P := by
  have hP := rationalSignMatrix_cast P hs
  have hp (i : ι) (j : κ) : ((rationalSignMatrix P i j : ℚ) : ℝ)=P i j := congrArg (fun M => M i j) hP
  ext i j
  by_cases hij : i=j <;>
    simp [realOfRationalMatrix,rationalResidualGram,residualGram,Matrix.mul_apply,Matrix.smul_apply,
      Matrix.one_apply,smul_eq_mul,hp,hij]

theorem rationalSignMatrix_binary {ι κ : Type*} (B : Matrix ι κ ℝ) : IsBinaryMatrix (rationalSignMatrix B) := by
  classical
  intro i j
  unfold rationalSignMatrix
  split_ifs <;> simp

theorem residual_real_rational_factor_iff {δ ι : Type*} [Fintype δ] [Fintype ι]
    [DecidableEq δ] [DecidableEq ι] (P : Matrix ι (δ ⊕ ι) ℝ) (hs : IsSignMatrix P) :
    (∃ B : Matrix δ (δ ⊕ ι) ℝ,IsBinaryMatrix B ∧ Bᵀ*B=residualGram P) ↔
      ∃ B : Matrix δ (δ ⊕ ι) ℚ,IsBinaryMatrix B ∧ Bᵀ*B=rationalResidualGram P := by
  have hC := rationalResidualGram_cast P hs
  constructor
  · rintro ⟨B,hB,hG⟩
    let Q := rationalSignMatrix B
    have hc : realOfRationalMatrix Q=B := rationalSignMatrix_cast B hB
    refine ⟨Q,rationalSignMatrix_binary B,?_⟩
    apply realOfRationalMatrix_injective
    rw [realOfRationalMatrix_mul,realOfRationalMatrix_transpose,hc,hG,hC]
  · rintro ⟨Q,hQ,hG⟩
    refine ⟨realOfRationalMatrix Q,?_,?_⟩
    · intro i j
      rcases hQ i j with h|h <;> simp [realOfRationalMatrix,h]
    · rw [← realOfRationalMatrix_transpose,← realOfRationalMatrix_mul,hG,hC]

theorem residual_anchor_enumeration {δ ι : Type*} [Fintype δ] [Fintype ι]
    [DecidableEq δ] [DecidableEq ι] [Nonempty δ]
    (P : Matrix ι (δ ⊕ ι) ℝ) (hP : IsPartialHadamard P)
    (heven : Even (Fintype.card (δ ⊕ ι))) :
    ∃ a : δ → (δ ⊕ ι),Function.Injective a ∧ ((rationalResidualGram P).submatrix a a).det≠0 ∧
      ((∃ H : Matrix (δ ⊕ ι) (δ ⊕ ι) ℝ,Matrix.IsHadamard H ∧ ∀ i j,H (Sum.inr i) j=P i j) ↔
        ∃ σ : δ×δ → Bool,(signAnchorMatrix (K := ℚ) σ).det≠0 ∧
          IsBinaryMatrix (anchorSolve (rationalResidualGram P) a (signAnchorMatrix σ)) ∧
          (anchorSolve (rationalResidualGram P) a (signAnchorMatrix σ))ᵀ*
            anchorSolve (rationalResidualGram P) a (signAnchorMatrix σ)=rationalResidualGram P) ∧
      Fintype.card (δ×δ → Bool)=2^(Fintype.card δ*Fintype.card δ) ∧
      (residualCorrelationTypes δ).card≤(Fintype.card δ+1)^(Fintype.card δ) ∧
      ∀ j : δ ⊕ ι,(fun i => residualGram P (a i) j)∈residualCorrelationTypes δ := by
  classical
  obtain ⟨a,ha,hdet⟩ := residual_principal_anchor_exists P hP
  have hC := rationalResidualGram_cast P hP.1
  have hsub : realOfRationalMatrix ((rationalResidualGram P).submatrix a a)=(residualGram P).submatrix a a := by
    ext i j
    exact congrArg (fun M => M (a i) (a j)) hC
  have hdetQ : ((rationalResidualGram P).submatrix a a).det≠0 := by
    intro hz
    have hc := rational_matrix_det_cast ((rationalResidualGram P).submatrix a a)
    rw [hz,Rat.cast_zero,hsub] at hc
    exact hdet hc.symm
  refine ⟨a,ha,hdetQ,?_,sign_anchor_cardinality δ,residualCorrelationTypes_card δ,?_⟩
  · exact ((residual_factor_completion_iff P hP.1).symm.trans
      (residual_real_rational_factor_iff P hP.1)).trans
        (fixed_anchor_factorization_iff (rationalResidualGram P) a hdetQ)
  · intro j
    exact residualGram_columns_in_types P hP heven a j

end CompletionTheory
