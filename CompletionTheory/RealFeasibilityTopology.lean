/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.RealConferenceConversion
public import Mathlib.Tactic
public import Mathlib.Analysis.Matrix.Normed
@[expose] public section
set_option autoImplicit false
namespace CompletionTheory

theorem real_root_reduced_component_sections {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (p : Bool)
    (hW : normalizedTwoReal A*(normalizedTwoReal A).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (hn : 4∣Fintype.card (Fin 2×ι)) :
    ∃ k : TwoPlaneSectionKind, (k=.zero ∨ k=.full ∨ k=.horizontal ∨ k=.vertical) ∧
      ∀ x y : ℝ, realRootConsistency A root (twoPlaneMatrix p x y) ↔ twoPlaneSectionCondition k x y := by
  obtain ⟨k,hk⟩ := real_root_original_component_sections A root p
  have hNonDiag : k≠.diagonal := by
    intro h
    have hR : realRootConsistency A root (twoPlaneMatrix p 1 1) := by
      apply (hk 1 1).mpr
      simp [h,twoPlaneSectionCondition]
    have hFull := real_diagonal_root_forces_full_plane A root p false hR hW hn
    have bad := (hk 1 0).mp (hFull 1 0)
    norm_num [h,twoPlaneSectionCondition] at bad
  have hNonAnti : k≠.antidiagonal := by
    intro h
    have hR : realRootConsistency A root (twoPlaneMatrix p 1 (-1)) := by
      apply (hk 1 (-1)).mpr
      norm_num [h,twoPlaneSectionCondition]
    have hFull := real_diagonal_root_forces_full_plane A root p true hR hW hn
    have bad := (hk 1 0).mp (hFull 1 0)
    norm_num [h,twoPlaneSectionCondition] at bad
  refine ⟨k,?_,hk⟩
  cases k <;> simp_all

theorem real_root_nonzero_section_has_axis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (p : Bool)
    (hW : normalizedTwoReal A*(normalizedTwoReal A).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (hn : 4∣Fintype.card (Fin 2×ι)) (x y : ℝ) (hxy : x≠0 ∨ y≠0)
    (hR : realRootConsistency A root (twoPlaneMatrix p x y)) :
    realRootConsistency A root (twoPlaneMatrix p 1 0) ∨
      realRootConsistency A root (twoPlaneMatrix p 0 1) := by
  obtain ⟨k,hk,hSections⟩ := real_root_reduced_component_sections A root p hW hn
  have h := (hSections x y).mp hR
  rcases hk with hk|hk|hk|hk
  · simp only [hk,twoPlaneSectionCondition] at h
    rcases hxy with hx|hy
    · exact False.elim (hx h.1)
    · exact False.elim (hy h.2)
  · left; apply (hSections 1 0).mpr; simp [hk,twoPlaneSectionCondition]
  · left; apply (hSections 1 0).mpr; simp [hk,twoPlaneSectionCondition]
  · right; apply (hSections 0 1).mpr; simp [hk,twoPlaneSectionCondition]


theorem real_orthogonal_two_plane (R : Matrix (Fin 2) (Fin 2) ℝ)
    (hR : R*R.transpose=1) :
    ∃ p : Bool, ∃ x y : ℝ, R=twoPlaneMatrix p x y ∧ x^2+y^2=1 := by
  have hn0 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hR
  have hn1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) hR
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_two,Matrix.one_apply,ite_true] at hn0 hn1
  have hdet : R.det*R.det=1 := by
    have h := congrArg Matrix.det hR
    simpa only [Matrix.det_mul,Matrix.det_transpose,Matrix.det_one] using h
  have hd := mul_self_eq_one_iff.mp hdet
  have hn : R 0 0^2+R 0 1^2=1 := by nlinarith [hn0]
  rcases hd with hd|hd
  · have hVal : R 0 0*R 1 1-R 0 1*R 1 0=1 := by simpa only [Matrix.det_fin_two] using hd
    have hs1 : (R 0 0-R 1 1)^2=0 := by nlinarith [sq_nonneg (R 0 1+R 1 0)]
    have hs2 : (R 0 1+R 1 0)^2=0 := by nlinarith [sq_nonneg (R 0 0-R 1 1)]
    have he1 := sq_eq_zero_iff.mp hs1
    have he2 := sq_eq_zero_iff.mp hs2
    refine ⟨false,R 0 0,R 0 1,?_,hn⟩
    ext a b; fin_cases a <;> fin_cases b <;> simp [twoPlaneMatrix] <;> linarith
  · have hVal : R 0 0*R 1 1-R 0 1*R 1 0= -1 := by simpa only [Matrix.det_fin_two] using hd
    have hs1 : (R 0 0+R 1 1)^2=0 := by nlinarith [sq_nonneg (R 0 1-R 1 0)]
    have hs2 : (R 0 1-R 1 0)^2=0 := by nlinarith [sq_nonneg (R 0 0+R 1 1)]
    have he1 := sq_eq_zero_iff.mp hs1
    have he2 := sq_eq_zero_iff.mp hs2
    refine ⟨true,R 0 0,R 0 1,?_,hn⟩
    ext a b; fin_cases a <;> fin_cases b <;> simp [twoPlaneMatrix] <;> linarith


theorem two_plane_axes_signed_int : ∀ p b : Bool, ∃ d : SignedTwoState,
    twoPlaneMatrix p (if b then 0 else 1) (if b then 1 else 0)=signedTwoInt d := by decide +kernel

theorem two_plane_axes_signed_real (p b : Bool) : ∃ d : SignedTwoState,
    twoPlaneMatrix p (if b then 0 else 1) (if b then 1 else 0)=signedTwoReal d := by
  obtain ⟨d,hd⟩ := two_plane_axes_signed_int p b
  refine ⟨d,?_⟩
  ext i j
  change twoPlaneMatrix p (if b then 0 else 1) (if b then 1 else 0) i j=(signedTwoInt d i j : ℝ)
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M i j) hd
  cases p <;> cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [twoPlaneMatrix] at he ⊢ <;> exact_mod_cast he

theorem forced_real_signed_cast {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (d : SignedTwoState) (i : ι) :
    (forcedSignedTwo A root d i).map (Int.castRingHom ℝ)=forcedRealTwo A root (signedTwoReal d) i := by
  by_cases hi : i=root
  · subst i; simp [forcedSignedTwo,forcedRealTwo,signedTwoReal]
  · simp only [forcedSignedTwo,forcedRealTwo,if_neg hi,Matrix.map_mul,← Matrix.transpose_map,signedTwoReal]
    ext a b
    simp [Matrix.mul_apply,Matrix.map_apply,Matrix.transpose_apply,Int.cast_sum,Int.cast_mul]

theorem real_signed_root_integer_consistent {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (d : SignedTwoState)
    (h : realRootConsistency A root (signedTwoReal d)) :
    SignedTwoConsistent A (forcedSignedTwo A root d) := by
  intro i j hij
  have he := h i j hij
  rw [← forced_real_signed_cast A root d i,← forced_real_signed_cast A root d j] at he
  ext a b
  have hc := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M a b) he
  simp only [Matrix.add_apply,Matrix.mul_apply,Matrix.transpose_apply,Matrix.map_apply,
    signedTwoReal,Matrix.zero_apply] at hc ⊢
  change (∑ k : Fin 2, (signedTwoInt (A i j) a k : ℝ)*(forcedSignedTwo A root d j b k : ℝ))+
    (∑ k : Fin 2, (forcedSignedTwo A root d i a k : ℝ)*(signedTwoInt (A j i) b k : ℝ))=0 at hc
  exact_mod_cast hc

theorem real_orthogonal_root_has_signed_solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι)
    (hW : normalizedTwoReal A*(normalizedTwoReal A).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (hn : 4∣Fintype.card (Fin 2×ι)) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (hOrtho : R*R.transpose=1) (hR : realRootConsistency A root R) :
    ∃ d : SignedTwoState, IsSignedTwoMatrixSolution A (forcedSignedTwo A root d) := by
  obtain ⟨p,x,y,hPlane,hUnit⟩ := real_orthogonal_two_plane R hOrtho
  have hNonzero : x≠0 ∨ y≠0 := by by_contra h; push_neg at h; rw [h.1,h.2] at hUnit; norm_num at hUnit
  rw [hPlane] at hR
  have hAxis := real_root_nonzero_section_has_axis A root p hW hn x y hNonzero hR
  have hExists : ∃ b : Bool, realRootConsistency A root
      (twoPlaneMatrix p (if b then 0 else 1) (if b then 1 else 0)) := by
    rcases hAxis with h|h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  obtain ⟨b,hb⟩ := hExists
  obtain ⟨d,hd⟩ := two_plane_axes_signed_real p b
  rw [hd] at hb
  exact ⟨d,fun i => forcedSignedTwo_is_state A root i d,real_signed_root_integer_consistent A root d hb⟩


noncomputable def realFillRoot (S : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1/2 : ℝ) • (S*walshTwoReal)

theorem real_fill_root_walsh (S : Matrix (Fin 2) (Fin 2) ℝ) : realFillRoot S*walshTwoReal=S := by
  have hFF : walshTwoReal*walshTwoReal=(2:ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    simpa only [walsh_two_real_symmetric] using walshTwoReal_gram
  simp only [realFillRoot,Matrix.smul_mul,Matrix.mul_assoc,hFF,Matrix.mul_smul,Matrix.mul_one,smul_smul]
  norm_num

theorem real_fill_root_orthogonal (S : Matrix (Fin 2) (Fin 2) ℝ)
    (hS : S*S.transpose=(2:ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    realFillRoot S*(realFillRoot S).transpose=1 := by
  calc
    _=((1/2)*(1/2):ℝ) • ((S*walshTwoReal)*(S*walshTwoReal).transpose) := by
      simp only [realFillRoot,Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
    _=((1/2)*(1/2):ℝ) • (S*(walshTwoReal*walshTwoReal.transpose)*S.transpose) := by
      rw [Matrix.transpose_mul]; congr 1; noncomm_ring
    _=1 := by
      rw [walshTwoReal_gram,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul,hS,smul_smul,smul_smul]
      norm_num

theorem actual_real_completion_has_signed_filling {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι)
    (hW : normalizedTwoReal A*(normalizedTwoReal A).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (hn : 4∣Fintype.card (Fin 2×ι))
    (H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ)
    (hH : H*H.transpose=(Fintype.card (Fin 2×ι) : ℝ) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (hRet : ∀ p q, p.2≠q.2 → H p q=normalizedTwoReal A p q) :
    ∃ K : Matrix (Fin 2×ι) (Fin 2×ι) ℝ, IsZeroBlockHadamardFilling (normalizedTwoReal A) K := by
  letI : Nonempty ι := ⟨root⟩
  let S : ι → Matrix (Fin 2) (Fin 2) ℝ := fun i => twoBlock H i i
  have hPatch : H=normalizedTwoReal A+Matrix.blockDiagonal S :=
    zeroBlockFilling_patch _ H (normalizedTwoReal_diagonal A) hRet
  rw [hPatch] at hH
  obtain ⟨hS,hCross⟩ := (diagonal_patch_gram_iff (normalizedTwoReal A) S
    (Fintype.card (Fin 2×ι) : ℝ) (normalizedTwoReal_diagonal A) hW).mp hH
  let R : ι → Matrix (Fin 2) (Fin 2) ℝ := fun i => realFillRoot (S i)
  have hFamily : ∀ i j, i≠j → signedTwoReal (A i j)*(R j).transpose+
      R i*(signedTwoReal (A j i)).transpose=0 := by
    intro i j hij
    have h := hCross i j hij
    rw [normalizedTwoReal_offdiagonal A i j hij,normalizedTwoReal_offdiagonal A j i (Ne.symm hij),
      ← real_fill_root_walsh (S i),← real_fill_root_walsh (S j),walsh_product_cross] at h
    ext a b
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M a b) h
    change (2:ℝ)*(_)=0 at he
    change _=0
    linarith
  have hRoot := real_consistent_family_forced A root R hFamily
  obtain ⟨d,hd⟩ := real_orthogonal_root_has_signed_solution A root hW hn (R root)
    (real_fill_root_orthogonal (S root) (hS root)) hRoot
  exact ⟨filledTwoReal A (forcedSignedTwo A root d),two_block_solution_hadamard A hW _ hd,
    filledTwoReal_retains_offdiagonal A _⟩


theorem actual_real_sign_feasibility_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι)
    (hW : normalizedTwoReal A*(normalizedTwoReal A).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (hn : 4∣Fintype.card (Fin 2×ι)) :
    (∃ H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ,
      H*H.transpose=(Fintype.card (Fin 2×ι) : ℝ) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) ∧
      ∀ p q, p.2≠q.2 → H p q=normalizedTwoReal A p q) ↔
    ∃ K : Matrix (Fin 2×ι) (Fin 2×ι) ℝ, IsZeroBlockHadamardFilling (normalizedTwoReal A) K := by
  constructor
  · rintro ⟨H,hGram,hRet⟩
    exact actual_real_completion_has_signed_filling A root hW hn H hGram hRet
  · rintro ⟨K,hK,hRet⟩
    refine ⟨K,?_,hRet⟩
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hK.mul_conjTranspose

noncomputable def realRootCompletion {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (R : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 2×ι) (Fin 2×ι) ℝ :=
  normalizedTwoReal A+Matrix.blockDiagonal (fun i => forcedRealTwo A root R i*walshTwoReal)

theorem forced_real_two_orthogonal {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (hR : R*R.transpose=1) (i : ι) :
    forcedRealTwo A root R i*(forcedRealTwo A root R i).transpose=1 := by
  by_cases hi : i=root
  · simpa only [forcedRealTwo,if_pos hi] using hR
  · have hRT : R.transpose*R=1 := mul_eq_one_comm.mp hR
    simp only [forcedRealTwo,if_neg hi,Matrix.transpose_mul,Matrix.transpose_neg,Matrix.transpose_transpose]
    calc
      _=signedTwoReal (A i root)*(R.transpose*(signedTwoReal (A root i)*(signedTwoReal (A root i)).transpose)*R)*
          (signedTwoReal (A i root)).transpose := by noncomm_ring
      _=1 := by rw [(signed_two_real_orthogonal (A root i)).1,Matrix.mul_one,hRT,Matrix.mul_one,
        (signed_two_real_orthogonal (A i root)).1]


theorem real_root_completion_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι)
    (hW : normalizedTwoReal A*(normalizedTwoReal A).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : R*R.transpose=1)
    (hC : realRootConsistency A root R) :
    realRootCompletion A root R*(realRootCompletion A root R).transpose=
      (Fintype.card (Fin 2×ι) : ℝ) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) := by
  apply (diagonal_patch_gram_iff (normalizedTwoReal A)
    (fun i => forcedRealTwo A root R i*walshTwoReal)
    (Fintype.card (Fin 2×ι) : ℝ) (normalizedTwoReal_diagonal A) hW).mpr
  constructor
  · intro i
    rw [Matrix.transpose_mul]
    calc
      _=forcedRealTwo A root R i*(walshTwoReal*walshTwoReal.transpose)*(forcedRealTwo A root R i).transpose := by noncomm_ring
      _=_ := by rw [walshTwoReal_gram,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul,forced_real_two_orthogonal A root R hR]
  · intro i j hij
    rw [normalizedTwoReal_offdiagonal A i j hij,normalizedTwoReal_offdiagonal A j i (Ne.symm hij),walsh_product_cross,hC i j hij]
    exact smul_zero _

theorem real_root_completion_retains {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (p q : Fin 2×ι) (hpq : p.2≠q.2) :
    realRootCompletion A root R p q=normalizedTwoReal A p q := by
  simp [realRootCompletion,Matrix.blockDiagonal_apply,hpq]

theorem real_root_completion_root_inverse {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (R : Matrix (Fin 2) (Fin 2) ℝ) :
    realFillRoot (twoBlock (realRootCompletion A root R) root root)=R := by
  have hBlock : twoBlock (realRootCompletion A root R) root root=R*walshTwoReal := by
    ext a b
    have hz := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M a b) (normalizedTwoReal_diagonal A root)
    simp [twoBlock,realRootCompletion,Matrix.blockDiagonal_apply,forcedRealTwo] at hz ⊢
    exact hz
  rw [hBlock]
  have h := real_fill_root_walsh R
  simpa only [realFillRoot,Matrix.smul_mul,Matrix.mul_assoc] using h


theorem real_family_eq_forced {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (R : ι → Matrix (Fin 2) (Fin 2) ℝ)
    (h : ∀ i j, i≠j → signedTwoReal (A i j)*(R j).transpose+
      R i*(signedTwoReal (A j i)).transpose=0) (i : ι) :
    R i=forcedRealTwo A root (R root) i := by
  by_cases hi : i=root
  · subst i; simp [forcedRealTwo]
  · rw [forcedRealTwo,if_neg hi]
    have ht := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M.transpose) (h root i (Ne.symm hi))
    simp only [Matrix.transpose_add,Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_zero] at ht
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M*signedTwoReal (A root i)) ht
    simp only [Matrix.add_mul,Matrix.zero_mul,Matrix.mul_assoc,(signed_two_real_orthogonal (A root i)).2,Matrix.mul_one] at hh
    have he := eq_neg_of_add_eq_zero_left hh
    simpa only [Matrix.neg_mul,Matrix.mul_assoc] using he

theorem actual_real_completion_root_inverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι)
    (hW : normalizedTwoReal A*(normalizedTwoReal A).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ)
    (hH : H*H.transpose=(Fintype.card (Fin 2×ι) : ℝ) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (hRet : ∀ p q, p.2≠q.2 → H p q=normalizedTwoReal A p q) :
    let R := realFillRoot (twoBlock H root root)
    R*R.transpose=1 ∧ realRootConsistency A root R ∧ H=realRootCompletion A root R := by
  let S : ι → Matrix (Fin 2) (Fin 2) ℝ := fun i => twoBlock H i i
  have hPatch : H=normalizedTwoReal A+Matrix.blockDiagonal S :=
    zeroBlockFilling_patch _ H (normalizedTwoReal_diagonal A) hRet
  rw [hPatch] at hH
  obtain ⟨hS,hCross⟩ := (diagonal_patch_gram_iff (normalizedTwoReal A) S
    (Fintype.card (Fin 2×ι) : ℝ) (normalizedTwoReal_diagonal A) hW).mp hH
  let R : ι → Matrix (Fin 2) (Fin 2) ℝ := fun i => realFillRoot (S i)
  have hFamily : ∀ i j, i≠j → signedTwoReal (A i j)*(R j).transpose+
      R i*(signedTwoReal (A j i)).transpose=0 := by
    intro i j hij
    have h := hCross i j hij
    rw [normalizedTwoReal_offdiagonal A i j hij,normalizedTwoReal_offdiagonal A j i (Ne.symm hij),
      ← real_fill_root_walsh (S i),← real_fill_root_walsh (S j),walsh_product_cross] at h
    ext a b
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M a b) h
    change (2:ℝ)*(_)=0 at he
    change _=0
    linarith
  refine ⟨real_fill_root_orthogonal (S root) (hS root),real_consistent_family_forced A root R hFamily,?_⟩
  change H=realRootCompletion A root (R root)
  calc
    H=normalizedTwoReal A+Matrix.blockDiagonal S := hPatch
    _=realRootCompletion A root (R root) := by
      unfold realRootCompletion
      apply congrArg (fun V : ι → Matrix (Fin 2) (Fin 2) ℝ => normalizedTwoReal A+Matrix.blockDiagonal V)
      funext i
      rw [← real_family_eq_forced A root R hFamily i]
      exact (real_fill_root_walsh (S i)).symm

theorem continuous_real_root_completion {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) : Continuous (realRootCompletion A root) := by
  apply continuous_matrix
  intro p q
  simp only [realRootCompletion,Matrix.add_apply,Matrix.blockDiagonal_apply]
  split_ifs
  · apply Continuous.add continuous_const
    simp only [Matrix.mul_apply,forcedRealTwo]
    split_ifs <;> fun_prop
  · exact continuous_const

theorem continuous_real_root_inverse {ι : Type*} (root : ι) :
    Continuous (fun H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ => realFillRoot (twoBlock H root root)) := by
  apply continuous_matrix
  intro a b
  simp only [realFillRoot,Matrix.smul_apply,smul_eq_mul,Matrix.mul_apply,twoBlock]
  fun_prop


def IsRealRootSolution {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (R : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  R*R.transpose=1 ∧ realRootConsistency A root R

def IsRealBlockCompletion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) : Prop :=
  H*H.transpose=(Fintype.card (Fin 2×ι) : ℝ) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) ∧
    ∀ p q, p.2≠q.2 → H p q=normalizedTwoReal A p q

noncomputable def realCompletionHomeomorph {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι)
    (hW : normalizedTwoReal A*(normalizedTwoReal A).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ)) :
    {R : Matrix (Fin 2) (Fin 2) ℝ // IsRealRootSolution A root R} ≃ₜ
      {H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ // IsRealBlockCompletion A H} where
  toFun R := ⟨realRootCompletion A root R.val,
    real_root_completion_gram A root hW R.val R.property.1 R.property.2,
    real_root_completion_retains A root R.val⟩
  invFun H := ⟨realFillRoot (twoBlock H.val root root),
    (actual_real_completion_root_inverse A root hW H.val H.property.1 H.property.2).1,
    (actual_real_completion_root_inverse A root hW H.val H.property.1 H.property.2).2.1⟩
  left_inv R := Subtype.ext (real_root_completion_root_inverse A root R.val)
  right_inv H := Subtype.ext (actual_real_completion_root_inverse A root hW H.val H.property.1 H.property.2).2.2.symm
  continuous_toFun := ((continuous_real_root_completion A root).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_real_root_inverse root).comp continuous_subtype_val).subtype_mk _


def reducedCircleCondition (k : TwoPlaneSectionKind) (x y : ℝ) : Prop :=
  match k with
  | .zero => False
  | .full => x^2+y^2=1
  | .horizontal => y=0 ∧ (x=1 ∨ x= -1)
  | .vertical => x=0 ∧ (y=1 ∨ y= -1)
  | .diagonal => False
  | .antidiagonal => False

theorem reduced_section_circle_condition (k : TwoPlaneSectionKind)
    (hk : k=.zero ∨ k=.full ∨ k=.horizontal ∨ k=.vertical) (x y : ℝ) :
    (twoPlaneSectionCondition k x y ∧ x^2+y^2=1) ↔ reducedCircleCondition k x y := by
  rcases hk with hk|hk|hk|hk <;> subst k
  · simp only [twoPlaneSectionCondition,reducedCircleCondition,iff_false]
    rintro ⟨⟨rfl,rfl⟩,h⟩; norm_num at h
  · simp [twoPlaneSectionCondition,reducedCircleCondition]
  · constructor
    · rintro ⟨⟨_,hy⟩,h⟩
      refine ⟨hy,?_⟩
      have hx : x*x=1 := by nlinarith [h]
      exact mul_self_eq_one_iff.mp hx
    · rintro ⟨rfl,hx|hx⟩ <;> subst x <;> norm_num [twoPlaneSectionCondition]
  · constructor
    · rintro ⟨⟨hx,_⟩,h⟩
      refine ⟨hx,?_⟩
      have hy : y*y=1 := by nlinarith [h]
      exact mul_self_eq_one_iff.mp hy
    · rintro ⟨rfl,hy|hy⟩ <;> subst y <;> norm_num [twoPlaneSectionCondition]

theorem two_plane_matrix_unit_gram (p : Bool) (x y : ℝ) :
    twoPlaneMatrix p x y*(twoPlaneMatrix p x y).transpose=1 ↔ x^2+y^2=1 := by
  constructor
  · intro h
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
    cases p <;> norm_num [twoPlaneMatrix,Matrix.mul_apply,Fin.sum_univ_two] at he <;> nlinarith
  · intro h
    cases p <;> ext a b <;> fin_cases a <;> fin_cases b <;>
      norm_num [twoPlaneMatrix,Matrix.mul_apply,Fin.sum_univ_two] <;> nlinarith

theorem real_completion_component_geometry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι)
    (hW : normalizedTwoReal A*(normalizedTwoReal A).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (hn : 4∣Fintype.card (Fin 2×ι)) :
    ∃ k : Bool → TwoPlaneSectionKind,
      (∀ p, k p=.zero ∨ k p=.full ∨ k p=.horizontal ∨ k p=.vertical) ∧
      (∀ p x y, IsRealRootSolution A root (twoPlaneMatrix p x y) ↔ reducedCircleCondition (k p) x y) ∧
      (∀ R, IsRealRootSolution A root R ↔ ∃ p x y, R=twoPlaneMatrix p x y ∧ reducedCircleCondition (k p) x y) := by
  classical
  have h (p : Bool) := real_root_reduced_component_sections A root p hW hn
  choose k hk hSections using h
  refine ⟨k,hk,?_,?_⟩
  · intro p x y
    rw [IsRealRootSolution,two_plane_matrix_unit_gram,hSections]
    exact and_comm.trans (reduced_section_circle_condition (k p) (hk p) x y)
  · intro R
    constructor
    · rintro ⟨hGram,hCons⟩
      obtain ⟨p,x,y,hR,hUnit⟩ := real_orthogonal_two_plane R hGram
      refine ⟨p,x,y,hR,?_⟩
      apply (reduced_section_circle_condition (k p) (hk p) x y).mp
      exact ⟨(hSections p x y).mp (hR ▸ hCons),hUnit⟩
    · rintro ⟨p,x,y,rfl,hCond⟩
      have hBoth := (reduced_section_circle_condition (k p) (hk p) x y).mpr hCond
      exact ⟨(two_plane_matrix_unit_gram p x y).mpr hBoth.2,(hSections p x y).mpr hBoth.1⟩


def IsAxisUnitPoint (x y : ℝ) : Prop :=
  (x=1 ∧ y=0) ∨ (x= -1 ∧ y=0) ∨ (x=0 ∧ y=1) ∨ (x=0 ∧ y= -1)

theorem two_plane_walsh_sign_iff (p : Bool) (x y : ℝ) :
    (∀ a b : Fin 2, IsSign ((twoPlaneMatrix p x y*walshTwoReal) a b)) ↔ IsAxisUnitPoint x y := by
  constructor
  · intro h
    have h00 := h 0 0
    have h01 := h 0 1
    have he00 : (twoPlaneMatrix p x y*walshTwoReal) 0 0=x+y := by
      cases p <;> simp [twoPlaneMatrix,walshTwoReal,walshTwoInt,Matrix.mul_apply,Fin.sum_univ_two]
    have he01 : (twoPlaneMatrix p x y*walshTwoReal) 0 1=x-y := by
      cases p <;> simp [twoPlaneMatrix,walshTwoReal,walshTwoInt,Matrix.mul_apply,Fin.sum_univ_two,sub_eq_add_neg]
    rw [he00] at h00
    rw [he01] at h01
    rcases h00 with h00|h00 <;> rcases h01 with h01|h01
    · exact Or.inl ⟨by linarith,by linarith⟩
    · exact Or.inr (Or.inr (Or.inl ⟨by linarith,by linarith⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by linarith,by linarith⟩))
    · exact Or.inr (Or.inl ⟨by linarith,by linarith⟩)
  · intro h a b
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
      cases p <;> fin_cases a <;> fin_cases b <;>
      norm_num [IsSign,twoPlaneMatrix,walshTwoReal,walshTwoInt,Matrix.mul_apply,Fin.sum_univ_two]

def componentSignedPoints (k : TwoPlaneSectionKind) : Finset (ℤ×ℤ) :=
  match k with
  | .zero => ∅
  | .full => {(1,0),(-1,0),(0,1),(0,-1)}
  | .horizontal => {(1,0),(-1,0)}
  | .vertical => {(0,1),(0,-1)}
  | .diagonal => ∅
  | .antidiagonal => ∅

theorem component_signed_points_card : ∀ k : TwoPlaneSectionKind,
    (componentSignedPoints k).card=(match k with | .full => 4 | .horizontal => 2 | .vertical => 2 | _ => 0) := by decide +kernel

theorem integer_plane_completion_injective {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (p : Bool) :
    Function.Injective (fun z : ℤ×ℤ => realRootCompletion A root (twoPlaneMatrix p (z.1 : ℝ) (z.2 : ℝ))) := by
  intro z w h
  have he := congrArg (fun H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ => realFillRoot (twoBlock H root root)) h
  rw [real_root_completion_root_inverse,real_root_completion_root_inverse] at he
  have hx := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) he
  have hy := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) he
  have hx' : (z.1 : ℝ)=(w.1 : ℝ) := by cases p <;> simpa [twoPlaneMatrix] using hx
  have hy' : (z.2 : ℝ)=(w.2 : ℝ) := by cases p <;> simpa [twoPlaneMatrix] using hy
  exact Prod.ext (by exact_mod_cast hx') (by exact_mod_cast hy')

noncomputable def componentSignCompletions {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (p : Bool) (k : TwoPlaneSectionKind) :
    Finset (Matrix (Fin 2×ι) (Fin 2×ι) ℝ) := by
  classical
  exact (componentSignedPoints k).image (fun z => realRootCompletion A root (twoPlaneMatrix p (z.1 : ℝ) (z.2 : ℝ)))

theorem component_sign_completions_card {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (p : Bool) (k : TwoPlaneSectionKind) :
    (componentSignCompletions A root p k).card=(match k with | .full => 4 | .horizontal => 2 | .vertical => 2 | _ => 0) := by
  classical
  unfold componentSignCompletions
  rw [Finset.card_image_of_injective _ (integer_plane_completion_injective A root p)]
  exact component_signed_points_card k


theorem real_fill_root_right_walsh (R : Matrix (Fin 2) (Fin 2) ℝ) : realFillRoot (R*walshTwoReal)=R := by
  simpa only [realFillRoot,Matrix.smul_mul,Matrix.mul_assoc] using real_fill_root_walsh R

theorem real_root_completion_root_block {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (R : Matrix (Fin 2) (Fin 2) ℝ) :
    twoBlock (realRootCompletion A root R) root root=R*walshTwoReal := by
  ext a b
  have hz := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M a b) (normalizedTwoReal_diagonal A root)
  simp [twoBlock,realRootCompletion,Matrix.blockDiagonal_apply,forcedRealTwo] at hz ⊢
  exact hz

theorem real_root_completion_signed_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι)
    (hW : normalizedTwoReal A*(normalizedTwoReal A).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (p : Bool) (x y : ℝ) (hUnit : x^2+y^2=1)
    (hCons : realRootConsistency A root (twoPlaneMatrix p x y)) :
    Matrix.IsHadamard (realRootCompletion A root (twoPlaneMatrix p x y)) ↔ IsAxisUnitPoint x y := by
  letI : Nonempty ι := ⟨root⟩
  let R := twoPlaneMatrix p x y
  have hR : R*R.transpose=1 := (two_plane_matrix_unit_gram p x y).mpr hUnit
  constructor
  · intro hHad
    apply (two_plane_walsh_sign_iff p x y).mp
    intro a b
    have hSign := Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hHad.apply_mem (a,root) (b,root))
    change IsSign ((twoBlock (realRootCompletion A root R) root root) a b) at hSign
    rw [real_root_completion_root_block] at hSign
    exact hSign
  · intro hAxis
    have hSigns : IsSignMatrix (R*walshTwoReal) := (two_plane_walsh_sign_iff p x y).mpr hAxis
    have hGram : (R*walshTwoReal)*(R*walshTwoReal).transpose=(2:ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      rw [Matrix.transpose_mul]
      calc
        _=R*(walshTwoReal*walshTwoReal.transpose)*R.transpose := by noncomm_ring
        _=_ := by rw [walshTwoReal_gram,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul,hR]
    obtain ⟨d,hd⟩ := sign_two_by_two_factor (R*walshTwoReal) hSigns hGram
    have hRD : R=signedTwoReal d := by
      have h := congrArg realFillRoot hd
      simpa only [real_fill_root_right_walsh] using h
    have hRoot : realRootConsistency A root (signedTwoReal d) := hRD ▸ hCons
    have hInt := real_signed_root_integer_consistent A root d hRoot
    have hSol : IsSignedTwoMatrixSolution A (forcedSignedTwo A root d) :=
      ⟨fun i => forcedSignedTwo_is_state A root i d,hInt⟩
    have hHad := two_block_solution_hadamard A hW (forcedSignedTwo A root d) hSol
    have hEq : filledTwoReal A (forcedSignedTwo A root d)=realRootCompletion A root R := by
      rw [filledTwoReal_patch,hRD]
      apply congrArg (fun V : ι → Matrix (Fin 2) (Fin 2) ℝ => normalizedTwoReal A+Matrix.blockDiagonal V)
      funext i
      rw [forced_real_signed_cast]
    rw [hEq] at hHad
    exact hHad


open scoped Matrix.Norms.Elementwise

noncomputable def cayleyCircleX (x y t : ℝ) : ℝ := ((1-t^2)*x-2*t*y)/(1+t^2)
noncomputable def cayleyCircleY (x y t : ℝ) : ℝ := (2*t*x+(1-t^2)*y)/(1+t^2)

theorem cayley_circle_unit (x y t : ℝ) (h : x^2+y^2=1) :
    cayleyCircleX x y t^2+cayleyCircleY x y t^2=1 := by
  have hden : (1+t^2 : ℝ)≠0 := by positivity
  unfold cayleyCircleX cayleyCircleY
  calc
    _=((x^2+y^2)*((1-t^2)^2+4*t^2))/(1+t^2)^2 := by field_simp [hden]; ring
    _=1 := by rw [h]; field_simp; ring

theorem cayley_circle_fixed_only_zero (x y t : ℝ) (h : x^2+y^2=1)
    (hx : cayleyCircleX x y t=x) (hy : cayleyCircleY x y t=y) : t=0 := by
  have hden : (1+t^2 : ℝ)≠0 := by positivity
  have hX := (div_eq_iff hden).mp hx
  have hY := (div_eq_iff hden).mp hy
  have hYX := congrArg (fun z : ℝ => z*x) hY
  have hXY := congrArg (fun z : ℝ => z*y) hX
  have he : 2*t*(x^2+y^2)=0 := by nlinarith [hYX,hXY]
  rw [h,mul_one] at he
  linarith

theorem cayley_circle_continuous (x y : ℝ) :
    Continuous (fun t : ℝ => (cayleyCircleX x y t,cayleyCircleY x y t)) := by
  unfold cayleyCircleX cayleyCircleY
  apply Continuous.prodMk
  all_goals
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro t; positivity

theorem real_full_plane_completion_nonisolated {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι)
    (hW : normalizedTwoReal A*(normalizedTwoReal A).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (p : Bool) (hFull : ∀ x y : ℝ, realRootConsistency A root (twoPlaneMatrix p x y))
    (x y : ℝ) (hUnit : x^2+y^2=1) :
    ∀ ε : ℝ, 0<ε → ∃ K : Matrix (Fin 2×ι) (Fin 2×ι) ℝ,
      IsRealBlockCompletion A K ∧ K≠realRootCompletion A root (twoPlaneMatrix p x y) ∧
      dist K (realRootCompletion A root (twoPlaneMatrix p x y))<ε := by
  let f : ℝ → Matrix (Fin 2×ι) (Fin 2×ι) ℝ := fun t =>
    realRootCompletion A root (twoPlaneMatrix p (cayleyCircleX x y t) (cayleyCircleY x y t))
  have hc : Continuous f := by
    apply (continuous_real_root_completion A root).comp
    apply continuous_matrix
    intro a b
    have hcx := continuous_fst.comp (cayley_circle_continuous x y)
    have hcy := continuous_snd.comp (cayley_circle_continuous x y)
    cases p <;> fin_cases a <;> fin_cases b <;> simp only [twoPlaneMatrix, Bool.false_eq_true, ite_false, ite_true, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.cons_val_fin_one]
    all_goals first | exact hcx | exact hcy | exact hcx.neg | exact hcy.neg
  have h0 : f 0=realRootCompletion A root (twoPlaneMatrix p x y) := by simp [f,cayleyCircleX,cayleyCircleY]
  intro ε hε
  obtain ⟨δ,hδ,hBall⟩ := Metric.continuousAt_iff.mp hc.continuousAt ε hε
  let t : ℝ := δ/2
  have ht : t≠0 := by dsimp [t]; positivity
  have htδ : dist t 0<δ := by rw [Real.dist_eq,sub_zero,abs_of_pos (by dsimp [t]; positivity)]; dsimp [t]; linarith
  refine ⟨f t,?_,?_,?_⟩
  · exact ⟨real_root_completion_gram A root hW _
      ((two_plane_matrix_unit_gram p _ _).mpr (cayley_circle_unit x y t hUnit)) (hFull _ _),
      real_root_completion_retains A root _⟩
  · intro he
    have hRoot := congrArg (fun H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ => realFillRoot (twoBlock H root root)) he
    simp only [f,real_root_completion_root_inverse] at hRoot
    have hx := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hRoot
    have hy := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hRoot
    have hx' : cayleyCircleX x y t=x := by cases p <;> simpa [twoPlaneMatrix] using hx
    have hy' : cayleyCircleY x y t=y := by cases p <;> simpa [twoPlaneMatrix] using hy
    exact ht (cayley_circle_fixed_only_zero x y t hUnit hx' hy')
  · simpa only [h0] using hBall htδ


theorem actual_nonsign_real_completion_nonisolated {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι)
    (hW : normalizedTwoReal A*(normalizedTwoReal A).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (hn : 4∣Fintype.card (Fin 2×ι))
    (H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) (hH : IsRealBlockCompletion A H)
    (hNotHad : ¬Matrix.IsHadamard H) :
    ∀ ε : ℝ, 0<ε → ∃ K : Matrix (Fin 2×ι) (Fin 2×ι) ℝ,
      IsRealBlockCompletion A K ∧ K≠H ∧ dist K H<ε := by
  obtain ⟨hRootGram,hRootCons,hReconstruct⟩ := actual_real_completion_root_inverse A root hW H hH.1 hH.2
  obtain ⟨p,x,y,hPlane,hUnit⟩ := real_orthogonal_two_plane _ hRootGram
  have hCons : realRootConsistency A root (twoPlaneMatrix p x y) := hPlane ▸ hRootCons
  have hRepr : H=realRootCompletion A root (twoPlaneMatrix p x y) := by
    rw [← hPlane]; exact hReconstruct
  have hNotAxis : ¬IsAxisUnitPoint x y := by
    intro ha
    apply hNotHad
    rw [hRepr]
    exact (real_root_completion_signed_iff A root hW p x y hUnit hCons).mpr ha
  obtain ⟨k,hk,hSections⟩ := real_root_reduced_component_sections A root p hW hn
  have hc := (reduced_section_circle_condition k hk x y).mp ⟨(hSections x y).mp hCons,hUnit⟩
  have hFull : k=.full := by
    rcases hk with hk|hk|hk|hk <;> subst k
    · simp [reducedCircleCondition] at hc
    · rfl
    · rcases hc with ⟨rfl,hx|hx⟩ <;> subst x <;>
        exact False.elim (hNotAxis (by simp [IsAxisUnitPoint]))
    · rcases hc with ⟨rfl,hy|hy⟩ <;> subst y <;>
        exact False.elim (hNotAxis (by simp [IsAxisUnitPoint]))
  have hAll (a b : ℝ) : realRootConsistency A root (twoPlaneMatrix p a b) := by
    apply (hSections a b).mpr
    simp [hFull,twoPlaneSectionCondition]
  rw [hRepr]
  exact real_full_plane_completion_nonisolated A root hW p hAll x y hUnit


theorem component_signed_points_spec (k : TwoPlaneSectionKind) (x y : ℝ) :
    (∃ z : ℤ×ℤ, z∈componentSignedPoints k ∧ x=(z.1 : ℝ) ∧ y=(z.2 : ℝ)) ↔
      reducedCircleCondition k x y ∧ IsAxisUnitPoint x y := by
  constructor
  · rintro ⟨z,hz,rfl,rfl⟩
    cases k with
    | zero => simp [componentSignedPoints] at hz
    | diagonal => simp [componentSignedPoints] at hz
    | antidiagonal => simp [componentSignedPoints] at hz
    | full =>
      simp only [componentSignedPoints,Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl|rfl|rfl|rfl <;> norm_num [reducedCircleCondition,IsAxisUnitPoint]
    | horizontal =>
      simp only [componentSignedPoints,Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl|rfl <;> norm_num [reducedCircleCondition,IsAxisUnitPoint]
    | vertical =>
      simp only [componentSignedPoints,Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl|rfl <;> norm_num [reducedCircleCondition,IsAxisUnitPoint]
  · rintro ⟨hc,ha⟩
    rcases ha with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · refine ⟨(1,0),?_,by norm_num,by norm_num⟩
      cases k <;> simp_all [reducedCircleCondition,componentSignedPoints]
    · refine ⟨(-1,0),?_,by norm_num,by norm_num⟩
      cases k <;> simp_all [reducedCircleCondition,componentSignedPoints]
    · refine ⟨(0,1),?_,by norm_num,by norm_num⟩
      cases k <;> simp_all [reducedCircleCondition,componentSignedPoints]
    · refine ⟨(0,-1),?_,by norm_num,by norm_num⟩
      cases k <;> simp_all [reducedCircleCondition,componentSignedPoints]

theorem component_sign_completions_exact {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι)
    (hW : normalizedTwoReal A*(normalizedTwoReal A).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (p : Bool) (k : TwoPlaneSectionKind)
    (hk : k=.zero ∨ k=.full ∨ k=.horizontal ∨ k=.vertical)
    (hSection : ∀ x y, realRootConsistency A root (twoPlaneMatrix p x y) ↔ twoPlaneSectionCondition k x y)
    (K : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) :
    K∈componentSignCompletions A root p k ↔
      ∃ x y : ℝ, K=realRootCompletion A root (twoPlaneMatrix p x y) ∧
        IsRealRootSolution A root (twoPlaneMatrix p x y) ∧ Matrix.IsHadamard K := by
  classical
  constructor
  · intro hK
    simp only [componentSignCompletions,Finset.mem_image] at hK
    obtain ⟨z,hz,rfl⟩ := hK
    have hPoints := (component_signed_points_spec k (z.1 : ℝ) (z.2 : ℝ)).mp ⟨z,hz,rfl,rfl⟩
    have hBoth := (reduced_section_circle_condition k hk _ _).mpr hPoints.1
    have hCons := (hSection _ _).mpr hBoth.1
    refine ⟨(z.1 : ℝ),(z.2 : ℝ),rfl,⟨(two_plane_matrix_unit_gram p _ _).mpr hBoth.2,hCons⟩,?_⟩
    exact (real_root_completion_signed_iff A root hW p _ _ hBoth.2 hCons).mpr hPoints.2
  · rintro ⟨x,y,rfl,hRoot,hHad⟩
    have hUnit := (two_plane_matrix_unit_gram p x y).mp hRoot.1
    have hAxis := (real_root_completion_signed_iff A root hW p x y hUnit hRoot.2).mp hHad
    have hCond := (reduced_section_circle_condition k hk x y).mp ⟨(hSection x y).mp hRoot.2,hUnit⟩
    obtain ⟨z,hz,hx,hy⟩ := (component_signed_points_spec k x y).mpr ⟨hCond,hAxis⟩
    simp only [componentSignCompletions,Finset.mem_image]
    exact ⟨z,hz,by rw [hx,hy]⟩


theorem axis_section_root_isolated {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (p : Bool) (k : TwoPlaneSectionKind)
    (hk : k=.horizontal ∨ k=.vertical)
    (hSection : ∀ x y, realRootConsistency A root (twoPlaneMatrix p x y) ↔ twoPlaneSectionCondition k x y)
    (x y : ℝ) (hBase : IsRealRootSolution A root (twoPlaneMatrix p x y))
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsRealRootSolution A root R)
    (hNear : dist R (twoPlaneMatrix p x y)<1) : R=twoPlaneMatrix p x y := by
  obtain ⟨q,u,v,rfl,hUnit⟩ := real_orthogonal_two_plane R hR.1
  have hEntry (a b : Fin 2) : |twoPlaneMatrix q u v a b-twoPlaneMatrix p x y a b|<1 := by
    have h := lt_of_le_of_lt (Matrix.norm_entry_le_entrywise_sup_norm
      (twoPlaneMatrix q u v-twoPlaneMatrix p x y) (i:=a) (j:=b)) hNear
    simpa only [dist_eq_norm,Matrix.sub_apply,Real.norm_eq_abs] using h
  have hUnitBase := (two_plane_matrix_unit_gram p x y).mp hBase.1
  have hBaseC := (reduced_section_circle_condition k (by rcases hk with h|h; exact Or.inr (Or.inr (Or.inl h)); exact Or.inr (Or.inr (Or.inr h))) x y).mp
    ⟨(hSection x y).mp hBase.2,hUnitBase⟩
  by_cases hqp : q=p
  · subst q
    have hNew := (reduced_section_circle_condition k (by rcases hk with h|h; exact Or.inr (Or.inr (Or.inl h)); exact Or.inr (Or.inr (Or.inr h))) u v).mp
      ⟨(hSection u v).mp hR.2,hUnit⟩
    rcases hk with rfl|rfl
    · rcases hBaseC with ⟨rfl,hx|hx⟩ <;> subst x <;>
        rcases hNew with ⟨rfl,hu|hu⟩ <;> subst u <;>
        have h00 := hEntry 0 0 <;> cases p <;> simp_all [twoPlaneMatrix] <;> norm_num at *
    · rcases hBaseC with ⟨rfl,hy|hy⟩ <;> subst y <;>
        rcases hNew with ⟨rfl,hv|hv⟩ <;> subst v <;>
        have h01 := hEntry 0 1 <;> cases p <;> simp_all [twoPlaneMatrix] <;> norm_num at *
  · have h00 := abs_lt.mp (hEntry 0 0)
    have h11 := abs_lt.mp (hEntry 1 1)
    have h01 := abs_lt.mp (hEntry 0 1)
    have h10 := abs_lt.mp (hEntry 1 0)
    rcases hk with rfl|rfl
    · rcases hBaseC with ⟨rfl,hx|hx⟩ <;> subst x <;>
        cases p <;> cases q <;> simp_all [twoPlaneMatrix] <;> grind
    · rcases hBaseC with ⟨rfl,hy|hy⟩ <;> subst y <;>
        cases p <;> cases q <;> simp_all [twoPlaneMatrix] <;> grind


theorem axis_section_completion_isolated {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι)
    (hW : normalizedTwoReal A*(normalizedTwoReal A).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (p : Bool) (k : TwoPlaneSectionKind) (hk : k=.horizontal ∨ k=.vertical)
    (hSection : ∀ x y, realRootConsistency A root (twoPlaneMatrix p x y) ↔ twoPlaneSectionCondition k x y)
    (x y : ℝ) (hBase : IsRealRootSolution A root (twoPlaneMatrix p x y)) :
    ∃ δ : ℝ, 0<δ ∧ ∀ K : Matrix (Fin 2×ι) (Fin 2×ι) ℝ,
      IsRealBlockCompletion A K → dist K (realRootCompletion A root (twoPlaneMatrix p x y))<δ →
      K=realRootCompletion A root (twoPlaneMatrix p x y) := by
  let H := realRootCompletion A root (twoPlaneMatrix p x y)
  have hc := (continuous_real_root_inverse (ι:=ι) root).continuousAt (x:=H)
  obtain ⟨δ,hδ,hBall⟩ := Metric.continuousAt_iff.mp hc 1 zero_lt_one
  refine ⟨δ,hδ,?_⟩
  intro K hK hNear
  have hExtract := actual_real_completion_root_inverse A root hW K hK.1 hK.2
  have hRootNear := hBall hNear
  rw [real_root_completion_root_inverse] at hRootNear
  have hRootEq := axis_section_root_isolated A root p k hk hSection x y hBase
    (realFillRoot (twoBlock K root root)) ⟨hExtract.1,hExtract.2.1⟩ hRootNear
  rw [hExtract.2.2,hRootEq]


def componentSignCount (k : TwoPlaneSectionKind) : ℕ :=
  match k with
  | .full => 4
  | .horizontal => 2
  | .vertical => 2
  | _ => 0

theorem real_feasibility_and_solution_topology {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι)
    (hW : normalizedTwoReal A*(normalizedTwoReal A).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (hn : 4∣Fintype.card (Fin 2×ι)) :
    ((∃ H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ, IsRealBlockCompletion A H) ↔
      ∃ K : Matrix (Fin 2×ι) (Fin 2×ι) ℝ, IsZeroBlockHadamardFilling (normalizedTwoReal A) K) ∧
    Nonempty ({R : Matrix (Fin 2) (Fin 2) ℝ // IsRealRootSolution A root R} ≃ₜ
      {H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ // IsRealBlockCompletion A H}) ∧
    (∃ k : Bool → TwoPlaneSectionKind,
      (∀ p, k p=.zero ∨ k p=.full ∨ k p=.horizontal ∨ k p=.vertical) ∧
      (∀ R, IsRealRootSolution A root R ↔
        ∃ p x y, R=twoPlaneMatrix p x y ∧ reducedCircleCondition (k p) x y) ∧
      ∀ p,
        (∀ x y, realRootConsistency A root (twoPlaneMatrix p x y) ↔ twoPlaneSectionCondition (k p) x y) ∧
        (∀ K : Matrix (Fin 2×ι) (Fin 2×ι) ℝ,
          K∈componentSignCompletions A root p (k p) ↔
            ∃ x y : ℝ, K=realRootCompletion A root (twoPlaneMatrix p x y) ∧
              IsRealRootSolution A root (twoPlaneMatrix p x y) ∧ Matrix.IsHadamard K) ∧
        (componentSignCompletions A root p (k p)).card=
          componentSignCount (k p) ∧
        ((k p=.horizontal ∨ k p=.vertical) → ∀ x y : ℝ,
          IsRealRootSolution A root (twoPlaneMatrix p x y) →
          ∃ δ : ℝ, 0<δ ∧ ∀ K : Matrix (Fin 2×ι) (Fin 2×ι) ℝ,
            IsRealBlockCompletion A K → dist K (realRootCompletion A root (twoPlaneMatrix p x y))<δ →
            K=realRootCompletion A root (twoPlaneMatrix p x y)) ∧
        (k p=.full → ∀ x y : ℝ, x^2+y^2=1 → ∀ ε : ℝ, 0<ε →
          ∃ K : Matrix (Fin 2×ι) (Fin 2×ι) ℝ, IsRealBlockCompletion A K ∧
            K≠realRootCompletion A root (twoPlaneMatrix p x y) ∧
            dist K (realRootCompletion A root (twoPlaneMatrix p x y))<ε)) ∧
    (∀ H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ, IsRealBlockCompletion A H → ¬Matrix.IsHadamard H →
      ∀ ε : ℝ, 0<ε → ∃ K : Matrix (Fin 2×ι) (Fin 2×ι) ℝ,
        IsRealBlockCompletion A K ∧ K≠H ∧ dist K H<ε) := by
  classical
  refine ⟨actual_real_sign_feasibility_iff A root hW hn,⟨realCompletionHomeomorph A root hW⟩,?_,
    actual_nonsign_real_completion_nonisolated A root hW hn⟩
  have h (p : Bool) := real_root_reduced_component_sections A root p hW hn
  choose k hk hSections using h
  refine ⟨k,hk,?_,?_⟩
  · intro R
    constructor
    · rintro ⟨hGram,hCons⟩
      obtain ⟨p,x,y,hR,hUnit⟩ := real_orthogonal_two_plane R hGram
      refine ⟨p,x,y,hR,?_⟩
      apply (reduced_section_circle_condition (k p) (hk p) x y).mp
      exact ⟨(hSections p x y).mp (hR ▸ hCons),hUnit⟩
    · rintro ⟨p,x,y,rfl,hCond⟩
      have hBoth := (reduced_section_circle_condition (k p) (hk p) x y).mpr hCond
      exact ⟨(two_plane_matrix_unit_gram p x y).mpr hBoth.2,(hSections p x y).mpr hBoth.1⟩
  · intro p
    refine ⟨hSections p,component_sign_completions_exact A root hW p (k p) (hk p) (hSections p),
      component_sign_completions_card A root p (k p),?_,?_⟩
    · intro hAxis x y hBase
      exact axis_section_completion_isolated A root hW p (k p) hAxis (hSections p) x y hBase
    · intro hFull x y hUnit
      apply real_full_plane_completion_nonisolated A root hW p _ x y hUnit
      intro a b
      apply (hSections p a b).mpr
      simp [hFull,twoPlaneSectionCondition]

end CompletionTheory
