/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.SignedTwoBlocks
public import CompletionTheory.RationalSignCertificates
public import Mathlib.Tactic
public import Mathlib.LinearAlgebra.Matrix.Notation
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option autoImplicit false
namespace CompletionTheory

inductive TwoPlaneSectionKind where
  | zero | full | horizontal | vertical | diagonal | antidiagonal
  deriving DecidableEq

instance : Fintype TwoPlaneSectionKind :=
  ⟨{.zero,.full,.horizontal,.vertical,.diagonal,.antidiagonal}, by intro k; cases k <;> simp⟩

def twoPlaneSectionCondition (k : TwoPlaneSectionKind) (x y : ℝ) : Prop :=
  match k with
  | .zero => x=0 ∧ y=0
  | .full => (0:ℝ)=0 ∧ (0:ℝ)=0
  | .horizontal => (0:ℝ)=0 ∧ y=0
  | .vertical => x=0 ∧ (0:ℝ)=0
  | .diagonal => x=y ∧ (0:ℝ)=0
  | .antidiagonal => x= -y ∧ (0:ℝ)=0

def twoPlaneSectionMeet (k l : TwoPlaneSectionKind) : TwoPlaneSectionKind :=
  if k=.zero ∨ l=.zero then .zero else
  if k=.full then l else if l=.full then k else if k=l then k else .zero

def twoPlaneMatrix {R : Type*} [Ring R] (p : Bool) (x y : R) : Matrix (Fin 2) (Fin 2) R :=
  if p then !![x,y;y,-x] else !![x,y;-y,x]

def signedTwoRat (d : SignedTwoState) : Matrix (Fin 2) (Fin 2) ℚ := (signedTwoInt d).map (Int.castRingHom ℚ)

def twoPlaneConstraintCoefficients (p : Bool) (L Q : SignedTwoState) : Matrix (Fin 2×Fin 2) (Fin 2) ℚ :=
  fun ab j =>
    let B : Matrix (Fin 2) (Fin 2) ℚ := twoPlaneMatrix p (if j=0 then 1 else 0) (if j=1 then 1 else 0)
    (B+signedTwoRat L*B.transpose*signedTwoRat Q) ab.1 ab.2

def coefficientSectionKind (C : Matrix (Fin 2×Fin 2) (Fin 2) ℚ) : TwoPlaneSectionKind :=
  if (∀ r, C r 0=0) ∧ (∀ r, C r 1=0) then .full else
  if (∀ r, C r 0=0) then .horizontal else
  if (∀ r, C r 1=0) then .vertical else
  if (∀ r, C r 0= -C r 1) then .diagonal else
  if (∀ r, C r 0=C r 1) then .antidiagonal else .zero

def sectionNormal (k : TwoPlaneSectionKind) : Matrix (Fin 2) (Fin 2) ℚ :=
  match k with
  | .zero => 1
  | .full => 0
  | .horizontal => !![0,1;0,0]
  | .vertical => !![1,0;0,0]
  | .diagonal => !![1,-1;0,0]
  | .antidiagonal => !![1,1;0,0]

def twoCoefficientRows : List (Fin 2×Fin 2) := [(0,0),(0,1),(1,0),(1,1)]

def coefficientNonzeroRow (C : Matrix (Fin 2×Fin 2) (Fin 2) ℚ) (j : Fin 2) : Fin 2×Fin 2 :=
  (twoCoefficientRows.find? (fun r => decide (C r j≠0))).getD (0,0)

def coefficientDeterminant (C : Matrix (Fin 2×Fin 2) (Fin 2) ℚ) (r s : Fin 2×Fin 2) : ℚ :=
  C r 0*C s 1-C r 1*C s 0

def coefficientIndependentRows (C : Matrix (Fin 2×Fin 2) (Fin 2) ℚ) : (Fin 2×Fin 2)×(Fin 2×Fin 2) :=
  ((twoCoefficientRows.flatMap (fun r => twoCoefficientRows.map (fun s => (r,s)))).find?
    (fun rs => decide (coefficientDeterminant C rs.1 rs.2≠0))).getD ((0,0),(0,0))

def coefficientToNormal (C : Matrix (Fin 2×Fin 2) (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2×Fin 2) ℚ :=
  let k := coefficientSectionKind C
  if k=.full then 0 else if k=.zero then
    let rs := coefficientIndependentRows C
    fun j r => if j=0 then
      (C rs.2 1*(if r=rs.1 then 1 else 0)-C rs.1 1*(if r=rs.2 then 1 else 0))/coefficientDeterminant C rs.1 rs.2
    else (-C rs.2 0*(if r=rs.1 then 1 else 0)+C rs.1 0*(if r=rs.2 then 1 else 0))/coefficientDeterminant C rs.1 rs.2
  else
    let j : Fin 2 := if k=.horizontal then 1 else 0
    let r0 := coefficientNonzeroRow C j
    fun a r => if a=0 ∧ r=r0 then 1/C r0 j else 0

def normalToCoefficient (C : Matrix (Fin 2×Fin 2) (Fin 2) ℚ) : Matrix (Fin 2×Fin 2) (Fin 2) ℚ :=
  let k := coefficientSectionKind C
  if k=.full then 0 else if k=.zero then C else
    fun r j => if j=0 then C r (if k=.horizontal then 1 else 0) else 0

theorem two_plane_constraint_rowspace_certificate : ∀ (p : Bool) (L Q : SignedTwoState),
    let C := twoPlaneConstraintCoefficients p L Q
    C=normalToCoefficient C*sectionNormal (coefficientSectionKind C) ∧
      sectionNormal (coefficientSectionKind C)=coefficientToNormal C*C := by
  decide +kernel

theorem rational_rowspace_real_kernel_iff {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    (C : Matrix m n ℚ) (D : Matrix k n ℚ) (E : Matrix m k ℚ) (F : Matrix k m ℚ)
    (hC : C=E*D) (hD : D=F*C) (v : n → ℝ) :
    (C.map rationalRealCast).mulVec v=0 ↔ (D.map rationalRealCast).mulVec v=0 := by
  have hCR : C.map rationalRealCast=E.map rationalRealCast*D.map rationalRealCast := by
    simpa only [Matrix.map_mul] using congrArg (fun M : Matrix m n ℚ => M.map rationalRealCast) hC
  have hDR : D.map rationalRealCast=F.map rationalRealCast*C.map rationalRealCast := by
    simpa only [Matrix.map_mul] using congrArg (fun M : Matrix k n ℚ => M.map rationalRealCast) hD
  constructor
  · intro h
    rw [hDR,← Matrix.mulVec_mulVec,h,Matrix.mulVec_zero]
  · intro h
    rw [hCR,← Matrix.mulVec_mulVec,h,Matrix.mulVec_zero]

theorem section_normal_real_iff (k : TwoPlaneSectionKind) (x y : ℝ) :
    ((sectionNormal k).map rationalRealCast).mulVec (![x,y] : Fin 2 → ℝ)=0 ↔ twoPlaneSectionCondition k x y := by
  cases k <;> simp [sectionNormal,twoPlaneSectionCondition,Matrix.mulVec,dotProduct,
    Fin.sum_univ_succ,funext_iff,Fin.forall_fin_two,rationalRealCast]
  all_goals constructor <;> intro h <;> linarith

theorem two_plane_rational_coefficients_section (p : Bool) (L Q : SignedTwoState) (x y : ℝ) :
    ((twoPlaneConstraintCoefficients p L Q).map rationalRealCast).mulVec (![x,y] : Fin 2 → ℝ)=0 ↔
      twoPlaneSectionCondition (coefficientSectionKind (twoPlaneConstraintCoefficients p L Q)) x y := by
  have h := two_plane_constraint_rowspace_certificate p L Q
  rw [rational_rowspace_real_kernel_iff _ _ _ _ h.1 h.2]
  exact section_normal_real_iff _ x y

def twoPlaneOperator {R : Type*} [Ring R] (p : Bool)
    (L Q : Matrix (Fin 2) (Fin 2) R) (x y : R) : Matrix (Fin 2) (Fin 2) R :=
  twoPlaneMatrix p x y+L*(twoPlaneMatrix p x y).transpose*Q

theorem map_two_plane_matrix {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (p : Bool) (x y : R) : (twoPlaneMatrix p x y).map f=twoPlaneMatrix p (f x) (f y) := by
  cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [twoPlaneMatrix]

theorem map_two_plane_operator {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (p : Bool) (L Q : Matrix (Fin 2) (Fin 2) R) (x y : R) :
    (twoPlaneOperator p L Q x y).map f=
      twoPlaneOperator p (L.map f) (Q.map f) (f x) (f y) := by
  have hBasis (a b : Fin 2) : f (twoPlaneMatrix p x y a b)=twoPlaneMatrix p (f x) (f y) a b := by
    simpa only [Matrix.map_apply] using congrArg (fun M : Matrix (Fin 2) (Fin 2) S => M a b)
      (map_two_plane_matrix f p x y)
  ext a b
  simp only [twoPlaneOperator,Matrix.map_apply,Matrix.add_apply,Matrix.mul_apply,
    Matrix.transpose_apply,map_add,map_sum,map_mul,hBasis]

theorem signed_two_rat_cast (d : SignedTwoState) : (signedTwoRat d).map rationalRealCast=signedTwoReal d := by
  ext i j
  simp [signedTwoRat,signedTwoReal,rationalRealCast]

theorem two_plane_matrix_linear (p : Bool) (x y : ℝ) :
    twoPlaneMatrix p x y=x • twoPlaneMatrix p 1 0+y • twoPlaneMatrix p 0 1 := by
  cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [twoPlaneMatrix] <;> ring

theorem two_plane_operator_linear (p : Bool) (L Q : Matrix (Fin 2) (Fin 2) ℝ) (x y : ℝ) :
    twoPlaneOperator p L Q x y=x • twoPlaneOperator p L Q 1 0+y • twoPlaneOperator p L Q 0 1 := by
  unfold twoPlaneOperator
  rw [two_plane_matrix_linear p x y]
  simp only [Matrix.transpose_add,Matrix.transpose_smul,Matrix.mul_add,Matrix.mul_smul,
    Matrix.add_mul,Matrix.smul_mul,smul_add]
  abel

theorem two_plane_coefficients_real_columns (p : Bool) (L Q : SignedTwoState)
    (ab : Fin 2×Fin 2) (j : Fin 2) :
    (twoPlaneConstraintCoefficients p L Q).map rationalRealCast ab j=
      if j=0 then twoPlaneOperator p (signedTwoReal L) (signedTwoReal Q) 1 0 ab.1 ab.2 else
        twoPlaneOperator p (signedTwoReal L) (signedTwoReal Q) 0 1 ab.1 ab.2 := by
  fin_cases j
  · have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M ab.1 ab.2)
      (map_two_plane_operator rationalRealCast p (signedTwoRat L) (signedTwoRat Q) 1 0)
    simpa [twoPlaneConstraintCoefficients,twoPlaneOperator,signed_two_rat_cast] using h
  · have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M ab.1 ab.2)
      (map_two_plane_operator rationalRealCast p (signedTwoRat L) (signedTwoRat Q) 0 1)
    simpa [twoPlaneConstraintCoefficients,twoPlaneOperator,signed_two_rat_cast] using h

theorem two_plane_coefficients_real_apply (p : Bool) (L Q : SignedTwoState) (x y : ℝ) (ab : Fin 2×Fin 2) :
    ((twoPlaneConstraintCoefficients p L Q).map rationalRealCast).mulVec (![x,y] : Fin 2 → ℝ) ab=
      twoPlaneOperator p (signedTwoReal L) (signedTwoReal Q) x y ab.1 ab.2 := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M ab.1 ab.2)
    (two_plane_operator_linear p (signedTwoReal L) (signedTwoReal Q) x y)
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul] at h
  have h0 := two_plane_coefficients_real_columns p L Q ab 0
  have h1 := two_plane_coefficients_real_columns p L Q ab 1
  norm_num at h0 h1
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  rw [h0,h1]
  nlinarith only [h]

theorem two_plane_operator_section (p : Bool) (L Q : SignedTwoState) (x y : ℝ) :
    twoPlaneOperator p (signedTwoReal L) (signedTwoReal Q) x y=0 ↔
      twoPlaneSectionCondition (coefficientSectionKind (twoPlaneConstraintCoefficients p L Q)) x y := by
  rw [← two_plane_rational_coefficients_section]
  constructor
  · intro h
    funext ab
    rw [two_plane_coefficients_real_apply,h]
    rfl
  · intro h
    ext a b
    have hh := congrFun h (a,b)
    rw [two_plane_coefficients_real_apply] at hh
    exact hh


theorem two_plane_section_meet (k l : TwoPlaneSectionKind) (x y : ℝ) :
    (twoPlaneSectionCondition k x y ∧ twoPlaneSectionCondition l x y) ↔
      twoPlaneSectionCondition (twoPlaneSectionMeet k l) x y := by
  cases k <;> cases l <;> simp only [twoPlaneSectionMeet,twoPlaneSectionCondition,reduceCtorEq,or_true,true_or,or_false,false_or,ite_true,ite_false]
  all_goals
    constructor
    · rintro ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩
      constructor <;> first | trivial | linarith
    · rintro ⟨h1,h2⟩
      constructor <;> constructor <;> first | trivial | linarith

def twoPlaneSectionList : List TwoPlaneSectionKind → TwoPlaneSectionKind
  | [] => .full
  | k::ks => twoPlaneSectionMeet k (twoPlaneSectionList ks)

theorem two_plane_section_list (ks : List TwoPlaneSectionKind) (x y : ℝ) :
    (∀ k∈ks, twoPlaneSectionCondition k x y) ↔ twoPlaneSectionCondition (twoPlaneSectionList ks) x y := by
  induction ks with
  | nil => simp [twoPlaneSectionList,twoPlaneSectionCondition]
  | cons k ks ih =>
      simp only [List.forall_mem_cons,twoPlaneSectionList]
      rw [ih,two_plane_section_meet]

theorem finite_two_plane_section_intersection {ι : Type*} [Fintype ι]
    (f : ι → TwoPlaneSectionKind) :
    ∃ k : TwoPlaneSectionKind, ∀ x y : ℝ,
      (∀ i, twoPlaneSectionCondition (f i) x y) ↔ twoPlaneSectionCondition k x y := by
  classical
  let ks := (Finset.univ.image f).toList
  refine ⟨twoPlaneSectionList ks,?_⟩
  intro x y
  rw [← two_plane_section_list]
  simp [ks]

theorem finite_matrix_kernel_component_sections {ι : Type*} [Fintype ι]
    (L Q : ι → SignedTwoState) (p : Bool) :
    ∃ k : TwoPlaneSectionKind, ∀ x y : ℝ,
      (∀ i, twoPlaneOperator p (signedTwoReal (L i)) (signedTwoReal (Q i)) x y=0) ↔
        twoPlaneSectionCondition k x y := by
  obtain ⟨k,hk⟩ := finite_two_plane_section_intersection
    (fun i => coefficientSectionKind (twoPlaneConstraintCoefficients p (L i) (Q i)))
  refine ⟨k,?_⟩
  intro x y
  rw [← hk]
  constructor
  · intro h i; exact (two_plane_operator_section p (L i) (Q i) x y).mp (h i)
  · intro h i; exact (two_plane_operator_section p (L i) (Q i) x y).mpr (h i)

abbrev RootTriangleIndex {ι : Type*} (root : ι) :=
  {ij : ι×ι // ij.1≠root ∧ ij.2≠root ∧ ij.1≠ij.2}

noncomputable def rootTriangleLeft {ι : Type*} (A : ι → ι → SignedTwoState)
    (root : ι) (ij : RootTriangleIndex root) : Matrix (Fin 2) (Fin 2) ℝ :=
  signedTwoReal (A root ij.val.2)*(signedTwoReal (A ij.val.1 ij.val.2)).transpose*
    signedTwoReal (A ij.val.1 root)

noncomputable def rootTriangleRight {ι : Type*} (A : ι → ι → SignedTwoState)
    (root : ι) (ij : RootTriangleIndex root) : Matrix (Fin 2) (Fin 2) ℝ :=
  signedTwoReal (A root ij.val.1)*(signedTwoReal (A ij.val.2 ij.val.1)).transpose*
    signedTwoReal (A ij.val.2 root)

noncomputable def realRootTriangleKernel {ι : Type*} (A : ι → ι → SignedTwoState)
    (root : ι) (R : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ ij : RootTriangleIndex root, R+rootTriangleLeft A root ij*R.transpose*rootTriangleRight A root ij=0

theorem signed_two_real_triple_transpose_closed (a b c : SignedTwoState) :
    ∃ d : SignedTwoState, signedTwoReal d=signedTwoReal a*(signedTwoReal b).transpose*signedTwoReal c := by
  obtain ⟨b',hb⟩ := signedTwoInt_transpose_closed b
  obtain ⟨e,he⟩ := signedTwoInt_product_closed a b'
  obtain ⟨d,hd⟩ := signedTwoInt_product_closed e c
  have hInt : signedTwoInt d=signedTwoInt a*(signedTwoInt b).transpose*signedTwoInt c := by rw [hd,he,hb]
  refine ⟨d,?_⟩
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (Int.castRingHom ℝ)) hInt
  simpa only [signedTwoReal,Matrix.map_mul,← Matrix.transpose_map] using h

theorem real_root_component_sections {ι : Type*} [Fintype ι]
    (A : ι → ι → SignedTwoState) (root : ι) (p : Bool) :
    ∃ k : TwoPlaneSectionKind, ∀ x y : ℝ,
      realRootTriangleKernel A root (twoPlaneMatrix p x y) ↔ twoPlaneSectionCondition k x y := by
  classical
  have hL (ij : RootTriangleIndex root) : ∃ d : SignedTwoState, signedTwoReal d=rootTriangleLeft A root ij :=
    signed_two_real_triple_transpose_closed (A root ij.val.2) (A ij.val.1 ij.val.2) (A ij.val.1 root)
  have hQ (ij : RootTriangleIndex root) : ∃ d : SignedTwoState, signedTwoReal d=rootTriangleRight A root ij :=
    signed_two_real_triple_transpose_closed (A root ij.val.1) (A ij.val.2 ij.val.1) (A ij.val.2 root)
  choose L hL using hL
  choose Q hQ using hQ
  obtain ⟨k,hk⟩ := finite_matrix_kernel_component_sections L Q p
  refine ⟨k,?_⟩
  intro x y
  rw [← hk]
  simp only [realRootTriangleKernel,twoPlaneOperator,hL,hQ]


theorem signed_two_real_orthogonal (d : SignedTwoState) :
    signedTwoReal d*(signedTwoReal d).transpose=1 ∧ (signedTwoReal d).transpose*signedTwoReal d=1 := by
  rcases d with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;> constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [signedTwoReal,signedTwoInt,Matrix.mul_apply,Fin.sum_univ_succ]

theorem real_root_cross_factorization (A B C D E F R : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A*A.transpose=1 ∧ A.transpose*A=1)
    (hB : B*B.transpose=1 ∧ B.transpose*B=1)
    (hC : C*C.transpose=1 ∧ C.transpose*C=1) :
    A*(-C*R.transpose*B).transpose+(-D*R.transpose*E)*F.transpose=0 ↔
      R+(B*A.transpose*D)*R.transpose*(E*F.transpose*C)=0 := by
  let U := A*B.transpose
  let O := R+(B*A.transpose*D)*R.transpose*(E*F.transpose*C)
  let X := A*(-C*R.transpose*B).transpose+(-D*R.transpose*E)*F.transpose
  have hUB : U*(B*A.transpose*D)=D := by
    calc
      _=A*(B.transpose*B)*A.transpose*D := by dsimp [U]; noncomm_ring
      _=D := by rw [hB.2]; simp only [Matrix.mul_one,hA.1,Matrix.one_mul]
  have hU : U.transpose*U=1 := by
    calc
      _=B*(A.transpose*A)*B.transpose := by dsimp [U]; rw [Matrix.transpose_mul,Matrix.transpose_transpose]; noncomm_ring
      _=1 := by rw [hA.2]; simpa only [Matrix.mul_one] using hB.1
  have hFactor : X= -U*O*C.transpose := by
    symm
    calc
      _= -(U*R*C.transpose)-((U*(B*A.transpose*D))*R.transpose*(E*F.transpose)*(C*C.transpose)) := by
        dsimp [O]; noncomm_ring
      _= -(U*R*C.transpose)-D*R.transpose*E*F.transpose := by rw [hUB,hC.1]; noncomm_ring
      _=X := by
        dsimp [X,U]
        simp only [Matrix.transpose_mul,Matrix.transpose_neg,Matrix.transpose_transpose]
        noncomm_ring
  change X=0 ↔ O=0
  constructor
  · intro hX
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => U.transpose*M*C) hX
    have hSimpl : U.transpose*X*C= -O := by
      rw [hFactor]
      calc
        _= -((U.transpose*U)*O*(C.transpose*C)) := by noncomm_ring
        _= -O := by rw [hU,hC.2]; simp
    rw [hSimpl,Matrix.mul_zero,Matrix.zero_mul] at hh
    exact neg_eq_zero.mp hh
  · intro hO
    rw [hFactor,hO,Matrix.mul_zero,Matrix.zero_mul]

noncomputable def forcedRealTwo {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (R : Matrix (Fin 2) (Fin 2) ℝ) (i : ι) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  if i=root then R else -signedTwoReal (A i root)*R.transpose*signedTwoReal (A root i)

noncomputable def realRootConsistency {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (R : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ i j, i≠j → signedTwoReal (A i j)*(forcedRealTwo A root R j).transpose+
    forcedRealTwo A root R i*(signedTwoReal (A j i)).transpose=0

theorem real_root_pair_cross {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (j : ι) (hj : j≠root) :
    signedTwoReal (A root j)*(forcedRealTwo A root R j).transpose+
      R*(signedTwoReal (A j root)).transpose=0 := by
  rw [forcedRealTwo,if_neg hj]
  calc
    _= -((signedTwoReal (A root j)*(signedTwoReal (A root j)).transpose)*R*
        (signedTwoReal (A j root)).transpose)+R*(signedTwoReal (A j root)).transpose := by
      simp only [Matrix.transpose_mul,Matrix.transpose_neg,Matrix.transpose_transpose]
      noncomm_ring
    _=0 := by rw [(signed_two_real_orthogonal (A root j)).1]; simp

theorem real_root_consistency_iff_triangles {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (R : Matrix (Fin 2) (Fin 2) ℝ) :
    realRootConsistency A root R ↔ realRootTriangleKernel A root R := by
  constructor
  · intro h ij
    have hc := h ij.val.1 ij.val.2 ij.property.2.2
    simp only [forcedRealTwo,if_neg ij.property.1,if_neg ij.property.2.1] at hc
    have hOp := (real_root_cross_factorization
      (signedTwoReal (A ij.val.1 ij.val.2)) (signedTwoReal (A root ij.val.2))
      (signedTwoReal (A ij.val.2 root)) (signedTwoReal (A ij.val.1 root))
      (signedTwoReal (A root ij.val.1)) (signedTwoReal (A ij.val.2 ij.val.1)) R
      (signed_two_real_orthogonal _) (signed_two_real_orthogonal _) (signed_two_real_orthogonal _)).mp hc
    exact hOp
  · intro h i j hij
    by_cases hi : i=root
    · subst i
      have hj : j≠root := Ne.symm hij
      simpa only [forcedRealTwo,if_pos rfl,if_neg hj,ite_true,ite_false] using real_root_pair_cross A root R j hj
    · by_cases hj : j=root
      · subst j
        have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M.transpose) (real_root_pair_cross A root R i hi)
        simpa only [Matrix.transpose_add,Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_zero,
          forcedRealTwo,if_pos rfl,if_neg hi,ite_true,ite_false,add_comm] using hh
      · let ij : RootTriangleIndex root := ⟨(i,j),hi,hj,hij⟩
        have hOp := h ij
        have hc := (real_root_cross_factorization
          (signedTwoReal (A i j)) (signedTwoReal (A root j)) (signedTwoReal (A j root))
          (signedTwoReal (A i root)) (signedTwoReal (A root i)) (signedTwoReal (A j i)) R
          (signed_two_real_orthogonal _) (signed_two_real_orthogonal _) (signed_two_real_orthogonal _)).mpr hOp
        simpa only [forcedRealTwo,if_neg hi,if_neg hj] using hc

theorem real_root_original_component_sections {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (p : Bool) :
    ∃ k : TwoPlaneSectionKind, ∀ x y : ℝ,
      realRootConsistency A root (twoPlaneMatrix p x y) ↔ twoPlaneSectionCondition k x y := by
  obtain ⟨k,hk⟩ := real_root_component_sections A root p
  refine ⟨k,?_⟩
  intro x y
  rw [real_root_consistency_iff_triangles]
  exact hk x y

end CompletionTheory
