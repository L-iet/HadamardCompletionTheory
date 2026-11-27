/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.QuaternaryCompletion
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic
@[expose] public section
set_option maxHeartbeats 4000000
set_option autoImplicit false
namespace CompletionTheory
open Matrix
abbrev GaussianRational := QuadraticAlgebra ℚ (-1) 0
instance (priority := high) gaussianRationalDecidableEq : DecidableEq GaussianRational :=
  fun x y => if hr : x.re=y.re then
    if hi : x.im=y.im then isTrue (QuadraticAlgebra.ext hr hi)
    else isFalse (fun h => hi (congrArg QuadraticAlgebra.im h))
  else isFalse (fun h => hr (congrArg QuadraticAlgebra.re h))
instance gaussianRational_irreducible : Fact (∀ r : ℚ,r^2≠(-1)+0*r) := by
  constructor
  intro r hr
  nlinarith [sq_nonneg r]
noncomputable def gaussianRationalEmbed : GaussianRational →ₐ[ℚ] ℂ :=
  QuadraticAlgebra.lift ⟨Complex.I,by norm_num⟩

theorem gaussianRationalEmbed_injective : Function.Injective gaussianRationalEmbed :=
  gaussianRationalEmbed.injective

theorem gaussianRationalEmbed_coordinates (z : GaussianRational) :
    gaussianRationalEmbed z=(z.re : ℂ)+(z.im : ℂ)*Complex.I := by
  simp [gaussianRationalEmbed,QuadraticAlgebra.lift,Algebra.smul_def]

def gaussianImaginary : GaussianRational := ⟨0,1⟩

def IsGaussianFourthRoot (z : GaussianRational) : Prop :=
  z=1 ∨ z= -1 ∨ z=gaussianImaginary ∨ z= -gaussianImaginary

instance gaussianFourthRoot_decidable (z : GaussianRational) : Decidable (IsGaussianFourthRoot z) :=
  inferInstanceAs (Decidable (z=1 ∨ z= -1 ∨ z=gaussianImaginary ∨ z= -gaussianImaginary))

theorem gaussianRationalEmbed_imaginary : gaussianRationalEmbed gaussianImaginary=Complex.I := by
  simp [gaussianRationalEmbed_coordinates,gaussianImaginary]

theorem gaussianRationalEmbed_star (z : GaussianRational) :
    gaussianRationalEmbed (star z)=star (gaussianRationalEmbed z) := by
  simp [gaussianRationalEmbed_coordinates,QuadraticAlgebra.re_star,QuadraticAlgebra.im_star]

theorem gaussianRationalEmbed_mulVec {ι κ : Type*} [Fintype κ]
    (A : Matrix ι κ GaussianRational) (z : κ → GaussianRational) (i : ι) :
    gaussianRationalEmbed (A.mulVec z i)=
      ((A.map gaussianRationalEmbed).mulVec (gaussianRationalEmbed ∘ z)) i := by
  simp [Matrix.mulVec,dotProduct,map_sum,map_mul,Function.comp_def]

theorem gaussianFourthRoot_iff (z : GaussianRational) :
    IsGaussianFourthRoot z ↔ IsFourthRoot (gaussianRationalEmbed z) := by
  constructor
  · intro hz
    rcases hz with rfl|rfl|rfl|rfl <;>
      simp [IsFourthRoot,gaussianRationalEmbed_imaginary]
  · intro hz
    rcases hz with h|h|h|h
    · exact Or.inl (gaussianRationalEmbed_injective (by simpa using h))
    · exact Or.inr (Or.inl (gaussianRationalEmbed_injective (by simpa using h)))
    · exact Or.inr (Or.inr (Or.inl (gaussianRationalEmbed_injective (by
        simpa only [gaussianRationalEmbed_imaginary] using h))))
    · exact Or.inr (Or.inr (Or.inr (gaussianRationalEmbed_injective (by
        simpa only [map_neg,gaussianRationalEmbed_imaginary] using h))))

theorem gaussianKernel_reflection {ι κ : Type*} [Fintype κ]
    (A : Matrix ι κ GaussianRational) (z : κ → GaussianRational) :
    (A.map gaussianRationalEmbed).mulVec (gaussianRationalEmbed ∘ z)=0 ↔
      A.mulVec z=0 := by
  constructor
  · intro h
    funext i
    apply gaussianRationalEmbed_injective
    have hi := congrFun h i
    rw [← gaussianRationalEmbed_mulVec] at hi
    simpa using hi
  · intro h
    funext i
    rw [← gaussianRationalEmbed_mulVec,h]
    simp

theorem gaussianConjTranspose_map {ι κ : Type*} (A : Matrix ι κ GaussianRational) :
    A.conjTranspose.map gaussianRationalEmbed=(A.map gaussianRationalEmbed).conjTranspose := by
  ext i j
  simp [Matrix.conjTranspose_apply,gaussianRationalEmbed_star]


variable {K : Type*} [Field K] {m n : ℕ}

def gaussianPivotLift (A : Matrix (Fin (m+1)) (Fin (n+1)) K)
    (j : Fin (n+1)) (u : Fin n → K) : Fin (n+1) → K :=
  Fin.insertNth j (-(∑ k, A 0 (j.succAbove k)*u k)/A 0 j) u

def gaussianSchur (A : Matrix (Fin (m+1)) (Fin (n+1)) K)
    (j : Fin (n+1)) : Matrix (Fin m) (Fin n) K :=
  fun i k => A i.succ (j.succAbove k)-A i.succ j/A 0 j*A 0 (j.succAbove k)

theorem gaussianPivotLift_head (A : Matrix (Fin (m+1)) (Fin (n+1)) K)
    (j : Fin (n+1)) (hp : A 0 j≠0) (u : Fin n → K) :
    A.mulVec (gaussianPivotLift A j u) 0=0 := by
  simp only [Matrix.mulVec,dotProduct]
  rw [Fin.sum_univ_succAbove _ j]
  simp only [gaussianPivotLift,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]
  field_simp
  ring

theorem gaussianPivotLift_tail (A : Matrix (Fin (m+1)) (Fin (n+1)) K)
    (j : Fin (n+1)) (u : Fin n → K) (i : Fin m) :
    A.mulVec (gaussianPivotLift A j u) i.succ=(gaussianSchur A j).mulVec u i := by
  simp only [Matrix.mulVec,dotProduct]
  rw [Fin.sum_univ_succAbove _ j]
  simp only [gaussianPivotLift,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove,
    gaussianSchur,sub_mul,Finset.sum_sub_distrib]
  have hs : (∑ k,A i.succ j/A 0 j*A 0 (j.succAbove k)*u k)=
      A i.succ j/A 0 j*(∑ k,A 0 (j.succAbove k)*u k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hs]
  ring

theorem gaussianPivotLift_recover (A : Matrix (Fin (m+1)) (Fin (n+1)) K)
    (j : Fin (n+1)) (hp : A 0 j≠0) (x : Fin (n+1) → K)
    (hx : A.mulVec x 0=0) :
    gaussianPivotLift A j (fun k => x (j.succAbove k))=x := by
  apply Fin.insertNth_eq_iff.mpr
  constructor
  · change -(∑ k,A 0 (j.succAbove k)*x (j.succAbove k))/A 0 j=x j
    apply (div_eq_iff hp).mpr
    have hh := hx
    change (∑ k,A 0 k*x k)=0 at hh
    rw [Fin.sum_univ_succAbove _ j] at hh
    linear_combination -hh
  · rfl

theorem gaussianSchur_surjective (A : Matrix (Fin (m+1)) (Fin (n+1)) K)
    (j : Fin (n+1)) (hp : A 0 j≠0) (hA : Function.Surjective A.mulVecLin) :
    Function.Surjective (gaussianSchur A j).mulVecLin := by
  intro y
  obtain ⟨x,hx⟩ := hA (Fin.cons 0 y)
  change A.mulVec x=Fin.cons 0 y at hx
  have hzero : A.mulVec x 0=0 := by simpa using congrFun hx 0
  have hrec := gaussianPivotLift_recover A j hp x hzero
  refine ⟨fun k => x (j.succAbove k),?_⟩
  change (gaussianSchur A j).mulVec (fun k => x (j.succAbove k))=y
  funext i
  rw [← gaussianPivotLift_tail,hrec]
  simpa using congrFun hx i.succ

theorem gaussian_nonzero_pivot (A : Matrix (Fin (m+1)) (Fin (n+1)) K)
    (hA : Function.Surjective A.mulVecLin) : ∃ j,A 0 j≠0 := by
  by_contra hn
  push Not at hn
  obtain ⟨x,hx⟩ := hA (Fin.cons 1 (fun _ => 0))
  have hh := congrFun hx 0
  change (∑ j,A 0 j*x j)=1 at hh
  simp [hn] at hh


def gaussianFirstPivot [DecidableEq K]
    (A : Matrix (Fin (m+1)) (Fin (n+1)) K)
    (hA : Function.Surjective A.mulVecLin) : Fin (n+1) :=
  (Finset.univ.filter (fun j => A 0 j≠0)).min' (by
    obtain ⟨j,hj⟩ := gaussian_nonzero_pivot A hA
    exact ⟨j,by simp [hj]⟩)

theorem gaussianFirstPivot_nonzero [DecidableEq K]
    (A : Matrix (Fin (m+1)) (Fin (n+1)) K)
    (hA : Function.Surjective A.mulVecLin) : A 0 (gaussianFirstPivot A hA)≠0 := by
  unfold gaussianFirstPivot
  exact (Finset.mem_filter.mp (Finset.min'_mem (Finset.univ.filter (fun j : Fin (n+1) => A 0 j≠0)) _)).2

def gaussianPivotLinear (A : Matrix (Fin (m+1)) (Fin (n+1)) K)
    (j : Fin (n+1)) : (Fin n → K) →ₗ[K] (Fin (n+1) → K) where
  toFun := gaussianPivotLift A j
  map_add' u v := by
    funext i
    refine Fin.succAboveCases j ?_ (fun k => ?_) i
    · simp [gaussianPivotLift,Finset.mul_sum,Finset.sum_add_distrib,mul_add,add_div,add_comm]
    · simp [gaussianPivotLift]
  map_smul' a u := by
    funext i
    refine Fin.succAboveCases j ?_ (fun k => ?_) i
    · simp only [gaussianPivotLift,Fin.insertNth_apply_same,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
      have hs : (∑ k,A 0 (j.succAbove k)*(a*u k))=
          a*(∑ k,A 0 (j.succAbove k)*u k) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [hs]
      ring
    · simp [gaussianPivotLift]


structure ExactGaussianKernelData {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) where
  freeCount : ℕ
  positions : Fin freeCount → Fin n
  positions_injective : Function.Injective positions
  reconstruct : (Fin freeCount → K) →ₗ[K] (Fin n → K)
  reconstruct_coordinates : ∀ y k,reconstruct y (positions k)=y k
  reconstruct_kernel : ∀ y,A.mulVec (reconstruct y)=0
  reconstruct_complete : ∀ x,A.mulVec x=0 → reconstruct (x ∘ positions)=x
  freeCount_add_rows : freeCount+m=n

def gaussianKernelDataZero (A : Matrix (Fin 0) (Fin n) K) : ExactGaussianKernelData A where
  freeCount := n
  positions := id
  positions_injective := Function.injective_id
  reconstruct := LinearMap.id
  reconstruct_coordinates := fun _ _ => rfl
  reconstruct_kernel := by intro y; funext i; exact Fin.elim0 i
  reconstruct_complete := by intro x hx; rfl
  freeCount_add_rows := by omega

def gaussianKernelDataStep (A : Matrix (Fin (m+1)) (Fin (n+1)) K)
    (j : Fin (n+1)) (hp : A 0 j≠0)
    (D : ExactGaussianKernelData (gaussianSchur A j)) : ExactGaussianKernelData A where
  freeCount := D.freeCount
  positions := j.succAbove ∘ D.positions
  positions_injective := j.succAbove_right_injective.comp D.positions_injective
  reconstruct := (gaussianPivotLinear A j).comp D.reconstruct
  reconstruct_coordinates := by
    intro y k
    change gaussianPivotLift A j (D.reconstruct y) (j.succAbove (D.positions k))=y k
    simp only [gaussianPivotLift,Fin.insertNth_apply_succAbove]
    exact D.reconstruct_coordinates y k
  reconstruct_kernel := by
    intro y
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · exact gaussianPivotLift_head A j hp (D.reconstruct y)
    · change A.mulVec (gaussianPivotLift A j (D.reconstruct y)) k.succ=0
      rw [gaussianPivotLift_tail]
      exact congrFun (D.reconstruct_kernel y) k
  reconstruct_complete := by
    intro x hx
    have hzero : A.mulVec x 0=0 := congrFun hx 0
    have hrec := gaussianPivotLift_recover A j hp x hzero
    have hker : (gaussianSchur A j).mulVec (fun k => x (j.succAbove k))=0 := by
      funext i
      rw [← gaussianPivotLift_tail,hrec]
      exact congrFun hx i.succ
    have hD := D.reconstruct_complete (fun k => x (j.succAbove k)) hker
    change gaussianPivotLift A j
      (D.reconstruct ((fun k => x (j.succAbove k)) ∘ D.positions))=x
    rw [hD]
    exact hrec
  freeCount_add_rows := by
    have hd := D.freeCount_add_rows
    omega


def gaussianKernelData [DecidableEq K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (hA : Function.Surjective A.mulVecLin) :
    ExactGaussianKernelData A := by
  induction m generalizing n with
  | zero => exact gaussianKernelDataZero A
  | succ m ih =>
    cases n with
    | zero =>
      have hFalse : False := by
        obtain ⟨x,hx⟩ := hA (Fin.cons 1 (fun _ => 0))
        have hh := congrFun hx 0
        have hbad : (0 : K)=1 := by simpa [Matrix.mulVec,dotProduct] using hh
        exact zero_ne_one hbad
      exact hFalse.elim
    | succ n =>
      let j := gaussianFirstPivot A hA
      have hp : A 0 j≠0 := gaussianFirstPivot_nonzero A hA
      exact gaussianKernelDataStep A j hp
        (ih (gaussianSchur A j) (gaussianSchur_surjective A j hp hA))

def gaussianKernelCoordinateEquiv {m n : ℕ} {A : Matrix (Fin m) (Fin n) K}
    (D : ExactGaussianKernelData A) :
    LinearMap.ker A.mulVecLin ≃ₗ[K] (Fin D.freeCount → K) where
  toFun x := x.val ∘ D.positions
  invFun y := ⟨D.reconstruct y,D.reconstruct_kernel y⟩
  left_inv x := by
    apply Subtype.ext
    exact D.reconstruct_complete x.val x.property
  right_inv y := by
    funext k
    exact D.reconstruct_coordinates y k
  map_add' x y := rfl
  map_smul' a x := rfl



def gaussianFourthAlphabet (a : Fin 4) : GaussianRational :=
  ![1,-1,gaussianImaginary,-gaussianImaginary] a

theorem gaussianFourthAlphabet_root (a : Fin 4) :
    IsGaussianFourthRoot (gaussianFourthAlphabet a) := by
  fin_cases a <;> simp [gaussianFourthAlphabet,IsGaussianFourthRoot]

theorem gaussianFourthAlphabet_surjective (z : GaussianRational)
    (hz : IsGaussianFourthRoot z) : ∃ a : Fin 4,gaussianFourthAlphabet a=z := by
  rcases hz with h|h|h|h
  · exact ⟨0,by simpa [gaussianFourthAlphabet] using h.symm⟩
  · exact ⟨1,by simpa [gaussianFourthAlphabet] using h.symm⟩
  · exact ⟨2,by simpa [gaussianFourthAlphabet] using h.symm⟩
  · exact ⟨3,by simpa [gaussianFourthAlphabet] using h.symm⟩

theorem gaussianFourthRoot_star_self {z : GaussianRational}
    (hz : IsGaussianFourthRoot z) : star z*z=1 := by
  apply gaussianRationalEmbed_injective
  simpa only [map_mul,gaussianRationalEmbed_star,map_one] using
    fourthRoot_star_self ((gaussianFourthRoot_iff z).mp hz)

theorem gaussianFourthRoot_star_mul {z w : GaussianRational}
    (hz : IsGaussianFourthRoot z) (hw : IsGaussianFourthRoot w) :
    IsGaussianFourthRoot (star z*w) := by
  apply (gaussianFourthRoot_iff _).mpr
  simpa only [map_mul,gaussianRationalEmbed_star] using
    fourthRoot_star_mul ((gaussianFourthRoot_iff z).mp hz) ((gaussianFourthRoot_iff w).mp hw)

def exactGaussianFourthCandidates {m n : ℕ} {A : Matrix (Fin m) (Fin n) GaussianRational}
    (D : ExactGaussianKernelData A) (j : Fin D.freeCount) : Finset (Fin n → GaussianRational) :=
  (Finset.univ.image (fun b : {k : Fin D.freeCount // k≠j} → Fin 4 =>
    D.reconstruct (fun k => if h : k=j then 1 else gaussianFourthAlphabet (b ⟨k,h⟩)))).filter
    (fun v => ∀ i,IsGaussianFourthRoot (v i))

theorem exactGaussianFourthCandidates_sound {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) GaussianRational} (D : ExactGaussianKernelData A)
    (j : Fin D.freeCount) (v : Fin n → GaussianRational)
    (hv : v∈exactGaussianFourthCandidates D j) :
    (∀ i,IsGaussianFourthRoot (v i)) ∧ A.mulVec v=0 ∧ v (D.positions j)=1 := by
  obtain ⟨hm,hr⟩ := Finset.mem_filter.mp hv
  obtain ⟨b,_,hb⟩ := Finset.mem_image.mp hm
  refine ⟨hr,?_,?_⟩
  · rw [← hb]
    exact D.reconstruct_kernel _
  · rw [← hb,D.reconstruct_coordinates]
    simp

theorem exactGaussianFourthCandidates_card {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) GaussianRational} (D : ExactGaussianKernelData A)
    (j : Fin D.freeCount) : (exactGaussianFourthCandidates D j).card≤4^(n-m-1) := by
  have hc : Fintype.card {k : Fin D.freeCount // k≠j}=D.freeCount-1 := by
    simp [Fintype.card_subtype_compl]
  have hd : D.freeCount=n-m := by have hh := D.freeCount_add_rows; omega
  exact (Finset.card_filter_le _ _).trans
    (Finset.card_image_le.trans (by simp [hc,hd]))

theorem exactGaussianFourthCandidates_complete {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) GaussianRational} (D : ExactGaussianKernelData A)
    (j : Fin D.freeCount) :
    (exactGaussianFourthCandidates D j).Nonempty ↔
      ∃ z : Fin n → GaussianRational,(∀ i,IsGaussianFourthRoot (z i)) ∧ A.mulVec z=0 := by
  constructor
  · rintro ⟨v,hv⟩
    have hh := exactGaussianFourthCandidates_sound D j v hv
    exact ⟨v,hh.1,hh.2.1⟩
  · rintro ⟨z,hz,hker⟩
    let u := star (z (D.positions j)) • z
    have hu : ∀ i,IsGaussianFourthRoot (u i) :=
      fun i => gaussianFourthRoot_star_mul (hz _) (hz i)
    have hkeru : A.mulVec u=0 := by simp [u,Matrix.mulVec_smul,hker]
    have huj : u (D.positions j)=1 := gaussianFourthRoot_star_self (hz _)
    have hchoose : ∀ k : {k : Fin D.freeCount // k≠j},
        ∃ a : Fin 4,gaussianFourthAlphabet a=u (D.positions k.val) :=
      fun k => gaussianFourthAlphabet_surjective _ (hu _)
    choose b hb using hchoose
    have heq : (fun k => if h : k=j then 1 else gaussianFourthAlphabet (b ⟨k,h⟩))=
        u ∘ D.positions := by
      funext k
      split_ifs with hk
      · subst k
        exact huj.symm
      · exact hb ⟨k,hk⟩
    refine ⟨u,Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨b,Finset.mem_univ _,?_⟩,hu⟩⟩
    rw [heq]
    exact D.reconstruct_complete u hkeru


def fourthAssignmentList {κ : Type*} [DecidableEq κ] : List κ → List (κ → Fin 4)
  | [] => [fun _ => 0]
  | k::ks => ([0,1,2,3] : List (Fin 4)).flatMap
      (fun a => (fourthAssignmentList ks).map (fun b => Function.update b k a))

theorem fourthAssignmentList_length {κ : Type*} [DecidableEq κ] (ks : List κ) :
    (fourthAssignmentList ks).length=4^ks.length := by
  induction ks with
  | nil => simp [fourthAssignmentList]
  | cons k ks ih =>
    simp [fourthAssignmentList,ih,pow_succ]
    omega

theorem fourthAssignmentList_cover {κ : Type*} [DecidableEq κ]
    (ks : List κ) (b : κ → Fin 4) :
    ∃ c∈fourthAssignmentList ks,∀ k∈ks,c k=b k := by
  induction ks with
  | nil => exact ⟨fun _ => 0,by simp [fourthAssignmentList],by simp⟩
  | cons k ks ih =>
    obtain ⟨c,hc,he⟩ := ih
    have ha : b k∈([0,1,2,3] : List (Fin 4)) := by
      have hh : ∀ a : Fin 4,a∈([0,1,2,3] : List (Fin 4)) := by
        intro a
        fin_cases a <;> simp
      exact hh _
    refine ⟨Function.update c k (b k),?_,?_⟩
    · exact List.mem_flatMap.mpr ⟨b k,ha,List.mem_map.mpr ⟨c,hc,rfl⟩⟩
    · intro i hi
      rcases List.mem_cons.mp hi with rfl|hi
      · simp
      · by_cases hik : i=k
        · subst i; simp
        · simpa [Function.update_of_ne hik] using he i hi

def countedFind {α : Type*} (p : α → Prop) [DecidablePred p] : List α → Option α × ℕ
  | [] => (none,0)
  | x::xs => if p x then (some x,1) else
      let r := countedFind p xs
      (r.1,r.2+1)

theorem countedFind_count_le {α : Type*} (p : α → Prop) [DecidablePred p]
    (xs : List α) : (countedFind p xs).2≤xs.length := by
  induction xs with
  | nil => simp [countedFind]
  | cons x xs ih =>
    by_cases hx : p x
    · simp [countedFind,hx]
    · simpa [countedFind,hx] using Nat.succ_le_succ ih

theorem countedFind_sound {α : Type*} (p : α → Prop) [DecidablePred p]
    (xs : List α) (v : α) (h : (countedFind p xs).1=some v) : p v ∧ v∈xs := by
  induction xs with
  | nil => simp [countedFind] at h
  | cons x xs ih =>
    by_cases hx : p x
    · have hv : x=v := Option.some.inj (by simpa [countedFind,hx] using h)
      subst v
      exact ⟨hx,by simp⟩
    · have hh : (countedFind p xs).1=some v := by simpa [countedFind,hx] using h
      obtain ⟨hp,hm⟩ := ih hh
      exact ⟨hp,List.mem_cons_of_mem _ hm⟩

theorem countedFind_none_iff {α : Type*} (p : α → Prop) [DecidablePred p]
    (xs : List α) : (countedFind p xs).1=none ↔ ∀ x∈xs,¬p x := by
  induction xs with
  | nil => simp [countedFind]
  | cons x xs ih =>
    by_cases hx : p x
    · simp [countedFind,hx]
    · simp [countedFind,hx,ih]

theorem fourthAssignmentList_mem_of_cover {κ : Type*} [DecidableEq κ]
    (ks : List κ) (hks : ∀ k,k∈ks) (b : κ → Fin 4) : b∈fourthAssignmentList ks := by
  obtain ⟨c,hc,he⟩ := fourthAssignmentList_cover ks b
  have hh : c=b := funext (fun k => he k (hks k))
  simpa only [hh] using hc

def gaussianAssignmentKeys {m n : ℕ} {A : Matrix (Fin m) (Fin n) GaussianRational}
    (D : ExactGaussianKernelData A) (j : Fin D.freeCount) :
    List {k : Fin D.freeCount // k≠j} := Finset.univ.sort (·≤·)

theorem gaussianAssignmentKeys_mem {m n : ℕ} {A : Matrix (Fin m) (Fin n) GaussianRational}
    (D : ExactGaussianKernelData A) (j : Fin D.freeCount)
    (k : {k : Fin D.freeCount // k≠j}) : k∈gaussianAssignmentKeys D j := by
  simp [gaussianAssignmentKeys]

def gaussianCandidateList {m n : ℕ} {A : Matrix (Fin m) (Fin n) GaussianRational}
    (D : ExactGaussianKernelData A) (j : Fin D.freeCount) : List (Fin n → GaussianRational) :=
  (fourthAssignmentList (gaussianAssignmentKeys D j)).map
    (fun b => D.reconstruct (fun k => if h : k=j then 1 else gaussianFourthAlphabet (b ⟨k,h⟩)))

theorem gaussianCandidateList_length {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) GaussianRational} (D : ExactGaussianKernelData A)
    (j : Fin D.freeCount) : (gaussianCandidateList D j).length=4^(n-m-1) := by
  have hc : Fintype.card {k : Fin D.freeCount // k≠j}=D.freeCount-1 := by
    simp [Fintype.card_subtype_compl]
  have hd : D.freeCount=n-m := by have hh := D.freeCount_add_rows; omega
  simp [gaussianCandidateList,fourthAssignmentList_length,gaussianAssignmentKeys,hc,hd]

theorem gaussianCandidateList_mem_iff {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) GaussianRational} (D : ExactGaussianKernelData A)
    (j : Fin D.freeCount) (v : Fin n → GaussianRational) :
    v∈gaussianCandidateList D j ↔
      ∃ b : {k : Fin D.freeCount // k≠j} → Fin 4,
        D.reconstruct (fun k => if h : k=j then 1 else gaussianFourthAlphabet (b ⟨k,h⟩))=v := by
  constructor
  · intro hv
    obtain ⟨b,_,hb⟩ := List.mem_map.mp hv
    exact ⟨b,hb⟩
  · rintro ⟨b,rfl⟩
    exact List.mem_map.mpr ⟨b,fourthAssignmentList_mem_of_cover _ (gaussianAssignmentKeys_mem D j) b,rfl⟩

theorem gaussianCandidateList_filter_iff {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) GaussianRational} (D : ExactGaussianKernelData A)
    (j : Fin D.freeCount) (v : Fin n → GaussianRational) :
    v∈exactGaussianFourthCandidates D j ↔
      v∈gaussianCandidateList D j ∧ ∀ i,IsGaussianFourthRoot (v i) := by
  simp [exactGaussianFourthCandidates,gaussianCandidateList_mem_iff]

def exactGaussianFourthSearch {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) GaussianRational} (D : ExactGaussianKernelData A)
    (j : Fin D.freeCount) : Option (Fin n → GaussianRational) × ℕ :=
  countedFind (fun v => ∀ i,IsGaussianFourthRoot (v i)) (gaussianCandidateList D j)

theorem exactGaussianFourthSearch_count {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) GaussianRational} (D : ExactGaussianKernelData A)
    (j : Fin D.freeCount) : (exactGaussianFourthSearch D j).2≤4^(n-m-1) := by
  exact (countedFind_count_le _ _).trans_eq (gaussianCandidateList_length D j)

theorem exactGaussianFourthSearch_sound {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) GaussianRational} (D : ExactGaussianKernelData A)
    (j : Fin D.freeCount) (v : Fin n → GaussianRational)
    (h : (exactGaussianFourthSearch D j).1=some v) :
    (∀ i,IsGaussianFourthRoot (v i)) ∧ A.mulVec v=0 ∧ v (D.positions j)=1 := by
  obtain ⟨hr,hm⟩ := countedFind_sound _ _ _ h
  exact exactGaussianFourthCandidates_sound D j v
    ((gaussianCandidateList_filter_iff D j v).mpr ⟨hm,hr⟩)

theorem exactGaussianFourthSearch_none_iff {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) GaussianRational} (D : ExactGaussianKernelData A)
    (j : Fin D.freeCount) : (exactGaussianFourthSearch D j).1=none ↔
      ¬∃ z : Fin n → GaussianRational,(∀ i,IsGaussianFourthRoot (z i)) ∧ A.mulVec z=0 := by
  rw [exactGaussianFourthSearch,countedFind_none_iff]
  constructor
  · intro h hex
    obtain ⟨z,hz⟩ := (exactGaussianFourthCandidates_complete D j).mpr hex
    have hh := (gaussianCandidateList_filter_iff D j z).mp hz
    exact h z hh.1 hh.2
  · intro h z hz hr
    apply h
    apply (exactGaussianFourthCandidates_complete D j).mp
    exact ⟨z,(gaussianCandidateList_filter_iff D j z).mpr ⟨hz,hr⟩⟩


theorem gaussianGram_transport {n m : ℕ} (V : Matrix (Fin n) (Fin m) GaussianRational)
    (hgram : V.conjTranspose*V=(n : GaussianRational) • (1 : Matrix (Fin m) (Fin m) GaussianRational)) :
    (V.map gaussianRationalEmbed).conjTranspose*(V.map gaussianRationalEmbed)=
      (n : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) := by
  rw [← gaussianConjTranspose_map,← Matrix.map_mul,hgram]
  ext j k
  by_cases h : j=k <;> simp [Matrix.one_apply,h]

theorem gaussianAdjoint_surjective {n m : ℕ} (hn : 0<n)
    (V : Matrix (Fin n) (Fin m) GaussianRational)
    (hgram : V.conjTranspose*V=(n : GaussianRational) • (1 : Matrix (Fin m) (Fin m) GaussianRational)) :
    Function.Surjective V.conjTranspose.mulVecLin := by
  have hnz : (n : GaussianRational)≠0 := by exact_mod_cast hn.ne'
  let M := (n : GaussianRational)⁻¹ • V
  have hPM : V.conjTranspose*M=1 := by
    simp only [M,Matrix.mul_smul,hgram,smul_smul,inv_mul_cancel₀ hnz,one_smul]
  intro y
  refine ⟨M.mulVec y,?_⟩
  change V.conjTranspose.mulVec (M.mulVec y)=y
  rw [Matrix.mulVec_mulVec,hPM,Matrix.one_mulVec]

theorem complexFourthRoot_has_gaussian (z : ℂ) (hz : IsFourthRoot z) :
    ∃ w : GaussianRational,IsGaussianFourthRoot w ∧ gaussianRationalEmbed w=z := by
  rcases hz with rfl|rfl|rfl|rfl
  · exact ⟨1,by simp [IsGaussianFourthRoot],by simp⟩
  · exact ⟨-1,by simp [IsGaussianFourthRoot],by simp⟩
  · exact ⟨gaussianImaginary,by simp [IsGaussianFourthRoot],gaussianRationalEmbed_imaginary⟩
  · exact ⟨-gaussianImaginary,by simp [IsGaussianFourthRoot],by simp [gaussianRationalEmbed_imaginary]⟩

theorem small_defect_gaussian_extension_exists (hClassical : RealSmallDefectExtension)
    {n m : ℕ} (hn : Even n) (hm : m<n) (hr : n-m≤3)
    (V : Matrix (Fin n) (Fin m) GaussianRational)
    (hV : ∀ i j,IsGaussianFourthRoot (V i j))
    (hgram : V.conjTranspose*V=(n : GaussianRational) • (1 : Matrix (Fin m) (Fin m) GaussianRational)) :
    ∃ z : Fin n → GaussianRational,(∀ i,IsGaussianFourthRoot (z i)) ∧ V.conjTranspose.mulVec z=0 := by
  obtain ⟨z,hz,horth⟩ := small_defect_quaternary_extension hClassical hn hm hr
    (V.map gaussianRationalEmbed) (fun i j => (gaussianFourthRoot_iff _).mp (hV i j))
    (gaussianGram_transport V hgram)
  have hpre : ∀ i,∃ w : GaussianRational,IsGaussianFourthRoot w ∧ gaussianRationalEmbed w=z i :=
    fun i => complexFourthRoot_has_gaussian _ (hz i)
  choose w hw using hpre
  refine ⟨w,fun i => (hw i).1,?_⟩
  apply (gaussianKernel_reflection V.conjTranspose w).mp
  rw [gaussianConjTranspose_map]
  have heq : gaussianRationalEmbed ∘ w=z := funext (fun i => (hw i).2)
  rw [heq]
  exact horth

def gaussianQuaternaryExtensionStep {n m : ℕ} (hm : m<n)
    (V : Matrix (Fin n) (Fin m) GaussianRational)
    (hgram : V.conjTranspose*V=(n : GaussianRational) • (1 : Matrix (Fin m) (Fin m) GaussianRational)) :
    Option (Fin n → GaussianRational) × ℕ :=
  let D := gaussianKernelData V.conjTranspose (gaussianAdjoint_surjective (by omega) V hgram)
  let j : Fin D.freeCount := ⟨0,by have hd := D.freeCount_add_rows; omega⟩
  exactGaussianFourthSearch D j

theorem gaussianQuaternaryExtensionStep_count {n m : ℕ} (hm : m<n)
    (V : Matrix (Fin n) (Fin m) GaussianRational)
    (hgram : V.conjTranspose*V=(n : GaussianRational) • (1 : Matrix (Fin m) (Fin m) GaussianRational)) :
    (gaussianQuaternaryExtensionStep hm V hgram).2≤4^(n-m-1) := by
  unfold gaussianQuaternaryExtensionStep
  exact exactGaussianFourthSearch_count _ _

theorem gaussianQuaternaryExtensionStep_sound {n m : ℕ} (hm : m<n)
    (V : Matrix (Fin n) (Fin m) GaussianRational)
    (hgram : V.conjTranspose*V=(n : GaussianRational) • (1 : Matrix (Fin m) (Fin m) GaussianRational))
    (z : Fin n → GaussianRational) (h : (gaussianQuaternaryExtensionStep hm V hgram).1=some z) :
    (∀ i,IsGaussianFourthRoot (z i)) ∧ V.conjTranspose.mulVec z=0 := by
  unfold gaussianQuaternaryExtensionStep at h
  have hh := exactGaussianFourthSearch_sound _ _ z h
  exact ⟨hh.1,hh.2.1⟩

theorem gaussianQuaternaryExtensionStep_success (hClassical : RealSmallDefectExtension)
    {n m : ℕ} (hn : Even n) (hm : m<n) (hr : n-m≤3)
    (V : Matrix (Fin n) (Fin m) GaussianRational)
    (hV : ∀ i j,IsGaussianFourthRoot (V i j))
    (hgram : V.conjTranspose*V=(n : GaussianRational) • (1 : Matrix (Fin m) (Fin m) GaussianRational)) :
    ∃ z,(gaussianQuaternaryExtensionStep hm V hgram).1=some z ∧
      (∀ i,IsGaussianFourthRoot (z i)) ∧ V.conjTranspose.mulVec z=0 := by
  have hex := small_defect_gaussian_extension_exists hClassical hn hm hr V hV hgram
  have hnone : (gaussianQuaternaryExtensionStep hm V hgram).1≠none := by
    intro h
    unfold gaussianQuaternaryExtensionStep at h
    exact (exactGaussianFourthSearch_none_iff _ _).mp h hex
  cases he : (gaussianQuaternaryExtensionStep hm V hgram).1 with
  | none => exact False.elim (hnone he)
  | some z => exact ⟨z,rfl,gaussianQuaternaryExtensionStep_sound hm V hgram z he⟩


theorem gaussianGram_reflect {n m : ℕ} (V : Matrix (Fin n) (Fin m) GaussianRational)
    (hgram : (V.map gaussianRationalEmbed).conjTranspose*(V.map gaussianRationalEmbed)=
      (n : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) :
    V.conjTranspose*V=(n : GaussianRational) • (1 : Matrix (Fin m) (Fin m) GaussianRational) := by
  have hh : (V.conjTranspose*V).map gaussianRationalEmbed=
      (n : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) := by
    rw [Matrix.map_mul,gaussianConjTranspose_map]
    exact hgram
  apply Matrix.ext
  intro j k
  apply gaussianRationalEmbed_injective
  have h := congrFun (congrFun hh j) k
  by_cases hjk : j=k <;> simpa [Matrix.one_apply,hjk] using h

def gaussianAppendColumn {n m : ℕ} (V : Matrix (Fin n) (Fin m) GaussianRational)
    (z : Fin n → GaussianRational) : Matrix (Fin n) (Fin (m+1)) GaussianRational :=
  fun i => Fin.snoc (V i) (z i)

theorem gaussianAppendColumn_map {n m : ℕ} (V : Matrix (Fin n) (Fin m) GaussianRational)
    (z : Fin n → GaussianRational) :
    (gaussianAppendColumn V z).map gaussianRationalEmbed=
      appendFourthColumn (V.map gaussianRationalEmbed) (gaussianRationalEmbed ∘ z) := by
  ext i j
  refine Fin.lastCases ?_ (fun k => ?_) j <;>
    simp [gaussianAppendColumn,appendFourthColumn,Function.comp_def]

theorem gaussianAppendColumn_roots {n m : ℕ} (V : Matrix (Fin n) (Fin m) GaussianRational)
    (z : Fin n → GaussianRational) (hV : ∀ i j,IsGaussianFourthRoot (V i j))
    (hz : ∀ i,IsGaussianFourthRoot (z i)) :
    ∀ i j,IsGaussianFourthRoot (gaussianAppendColumn V z i j) := by
  intro i j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simpa [gaussianAppendColumn] using hz i
  · simpa [gaussianAppendColumn] using hV i k

theorem gaussianAppendColumn_gram {n m : ℕ} (V : Matrix (Fin n) (Fin m) GaussianRational)
    (z : Fin n → GaussianRational) (hz : ∀ i,IsGaussianFourthRoot (z i))
    (hgram : V.conjTranspose*V=(n : GaussianRational) • (1 : Matrix (Fin m) (Fin m) GaussianRational))
    (horth : V.conjTranspose.mulVec z=0) :
    (gaussianAppendColumn V z).conjTranspose*(gaussianAppendColumn V z)=
      (n : GaussianRational) • (1 : Matrix (Fin (m+1)) (Fin (m+1)) GaussianRational) := by
  apply gaussianGram_reflect
  rw [gaussianAppendColumn_map]
  apply appendFourthColumn_gram
  · intro i
    exact (gaussianFourthRoot_iff _).mp (hz i)
  · exact gaussianGram_transport V hgram
  · rw [← gaussianConjTranspose_map]
    exact (gaussianKernel_reflection V.conjTranspose z).mpr horth


def gaussianQuaternaryComplete {n m : ℕ} (hm : m≤n)
    (V : Matrix (Fin n) (Fin m) GaussianRational)
    (hgram : V.conjTranspose*V=(n : GaussianRational) • (1 : Matrix (Fin m) (Fin m) GaussianRational)) :
    Option (Matrix (Fin n) (Fin n) GaussianRational) × ℕ :=
  if hlt : m<n then
    let R := gaussianQuaternaryExtensionStep hlt V hgram
    match hz : R.1 with
    | none => (none,R.2)
    | some z =>
      have hs := gaussianQuaternaryExtensionStep_sound hlt V hgram z hz
      let W := gaussianAppendColumn V z
      have hWG := gaussianAppendColumn_gram V z hs.1 hgram hs.2
      let R' := gaussianQuaternaryComplete (by omega) W hWG
      (R'.1,R.2+R'.2)
  else
    have heq : m=n := by omega
    (some (V.submatrix id (Fin.cast heq.symm)),0)
termination_by n-m
decreasing_by omega

def gaussianCompletionTestBudget (r : ℕ) : ℕ := ∑ k∈Finset.range r,4^k

theorem gaussianCompletionTestBudget_zero : gaussianCompletionTestBudget 0=0 := by
  simp [gaussianCompletionTestBudget]

theorem gaussianCompletionTestBudget_succ (r : ℕ) :
    gaussianCompletionTestBudget (r+1)=gaussianCompletionTestBudget r+4^r := by
  simp [gaussianCompletionTestBudget,Finset.sum_range_succ]

theorem gaussianCompletionTestBudget_le_twentyone {r : ℕ} (hr : r≤3) :
    gaussianCompletionTestBudget r≤21 := by
  interval_cases r <;> norm_num [gaussianCompletionTestBudget,Finset.sum_range_succ]


theorem gaussianQuaternaryComplete_count {n m : ℕ} (hm : m≤n)
    (V : Matrix (Fin n) (Fin m) GaussianRational)
    (hgram : V.conjTranspose*V=(n : GaussianRational) • (1 : Matrix (Fin m) (Fin m) GaussianRational)) :
    (gaussianQuaternaryComplete hm V hgram).2≤gaussianCompletionTestBudget (n-m) := by
  generalize hd : n-m=d
  induction d using Nat.strong_induction_on generalizing m with
  | h d ih =>
    by_cases hlt : m<n
    · have hnext : m+1≤n := by omega
      have hdnext : n-m=(n-(m+1))+1 := by omega
      have hstep := gaussianQuaternaryExtensionStep_count hlt V hgram
      rw [gaussianQuaternaryComplete,dif_pos hlt]
      dsimp only
      split
      next hz =>
        change (gaussianQuaternaryExtensionStep hlt V hgram).2≤gaussianCompletionTestBudget d
        rw [← hd,hdnext,gaussianCompletionTestBudget_succ]
        have hexp : n-m-1=n-(m+1) := by omega
        rw [hexp] at hstep
        omega
      next z hz =>
        have hs := gaussianQuaternaryExtensionStep_sound hlt V hgram z hz
        have hWG := gaussianAppendColumn_gram V z hs.1 hgram hs.2
        have hrec := ih (n-(m+1)) (by omega) hnext (gaussianAppendColumn V z) hWG rfl
        change (gaussianQuaternaryExtensionStep hlt V hgram).2+
          (gaussianQuaternaryComplete hnext (gaussianAppendColumn V z) hWG).2≤gaussianCompletionTestBudget d
        rw [← hd,hdnext,gaussianCompletionTestBudget_succ]
        have hexp : n-m-1=n-(m+1) := by omega
        rw [hexp] at hstep
        omega
    · have hmn : m=n := by omega
      rw [gaussianQuaternaryComplete,dif_neg hlt]
      simp


theorem gaussianQuaternaryComplete_correct (hClassical : RealSmallDefectExtension)
    {n m : ℕ} (hn : Even n) (hm : m≤n) (hr : n-m≤3)
    (V : Matrix (Fin n) (Fin m) GaussianRational)
    (hV : ∀ i j,IsGaussianFourthRoot (V i j))
    (hgram : V.conjTranspose*V=(n : GaussianRational) • (1 : Matrix (Fin m) (Fin m) GaussianRational)) :
    ∃ H : Matrix (Fin n) (Fin n) GaussianRational,
      (gaussianQuaternaryComplete hm V hgram).1=some H ∧
      (∀ i j,IsGaussianFourthRoot (H i j)) ∧
      H.conjTranspose*H=(n : GaussianRational) • (1 : Matrix (Fin n) (Fin n) GaussianRational) ∧
      ∀ i j,H i (Fin.castLE hm j)=V i j := by
  generalize hd : n-m=d
  induction d using Nat.strong_induction_on generalizing m with
  | h d ih =>
    by_cases hmn : m=n
    · subst m
      refine ⟨V,?_,hV,hgram,?_⟩
      · rw [gaussianQuaternaryComplete,dif_neg (Nat.lt_irrefl n)]
        rfl
      · intro i j
        rfl
    · have hlt : m<n := by omega
      have hnext : m+1≤n := by omega
      have hrnext : n-(m+1)≤3 := by omega
      obtain ⟨z,hz,hroot,horth⟩ := gaussianQuaternaryExtensionStep_success
        hClassical hn hlt hr V hV hgram
      let W := gaussianAppendColumn V z
      have hW := gaussianAppendColumn_roots V z hV hroot
      have hWG := gaussianAppendColumn_gram V z hroot hgram horth
      obtain ⟨H,hRec,hH,hHG,hret⟩ := ih (n-(m+1)) (by omega) hnext hrnext W hW hWG rfl
      refine ⟨H,?_,hH,hHG,?_⟩
      · rw [gaussianQuaternaryComplete,dif_pos hlt]
        dsimp only
        split
        next hfail =>
          rw [hz] at hfail
          contradiction
        next w hw =>
          have hwz : w=z := Option.some.inj (hw.symm.trans hz)
          subst w
          exact hRec
      · intro i j
        have hh := hret i j.castSucc
        have heq : Fin.castLE hnext j.castSucc=Fin.castLE hm j := by
          ext
          rfl
        simpa only [W,gaussianAppendColumn,Fin.snoc_castSucc,heq] using hh

theorem exact_quaternary_completion_algorithm (hClassical : RealSmallDefectExtension)
    {n m : ℕ} (hn : Even n) (hm : m≤n) (hr : n-m≤3)
    (V : Matrix (Fin n) (Fin m) GaussianRational)
    (hV : ∀ i j,IsGaussianFourthRoot (V i j))
    (hgram : V.conjTranspose*V=(n : GaussianRational) • (1 : Matrix (Fin m) (Fin m) GaussianRational)) :
    (∃ H : Matrix (Fin n) (Fin n) GaussianRational,
      (gaussianQuaternaryComplete hm V hgram).1=some H ∧
      (∀ i j,IsGaussianFourthRoot (H i j)) ∧
      H.conjTranspose*H=(n : GaussianRational) • (1 : Matrix (Fin n) (Fin n) GaussianRational) ∧
      ∀ i j,H i (Fin.castLE hm j)=V i j) ∧
      (gaussianQuaternaryComplete hm V hgram).2≤21 := by
  exact ⟨gaussianQuaternaryComplete_correct hClassical hn hm hr V hV hgram,
    (gaussianQuaternaryComplete_count hm V hgram).trans
      (gaussianCompletionTestBudget_le_twentyone hr)⟩


theorem gaussianEncoding_of_fourth_roots {n m : ℕ} (V : Matrix (Fin n) (Fin m) ℂ)
    (hV : ∀ i j,IsFourthRoot (V i j)) :
    ∃ W : Matrix (Fin n) (Fin m) GaussianRational,
      (∀ i j,IsGaussianFourthRoot (W i j)) ∧ W.map gaussianRationalEmbed=V := by
  have hh : ∀ i j,∃ w : GaussianRational,
      IsGaussianFourthRoot w ∧ gaussianRationalEmbed w=V i j :=
    fun i j => complexFourthRoot_has_gaussian _ (hV i j)
  choose W hW using hh
  exact ⟨W,fun i j => (hW i j).1,by
    apply Matrix.ext
    intro i j
    exact (hW i j).2⟩

theorem exact_quaternary_completion_algorithm_for_complex_input
    (hClassical : RealSmallDefectExtension) {n m : ℕ}
    (hn : Even n) (hm : m≤n) (hr : n-m≤3)
    (V : Matrix (Fin n) (Fin m) ℂ) (hV : ∀ i j,IsFourthRoot (V i j))
    (hgram : V.conjTranspose*V=(n : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) :
    ∃ (W : Matrix (Fin n) (Fin m) GaussianRational)
      (hWG : W.conjTranspose*W=(n : GaussianRational) •
        (1 : Matrix (Fin m) (Fin m) GaussianRational)),
      (∀ i j,IsGaussianFourthRoot (W i j)) ∧ W.map gaussianRationalEmbed=V ∧
      ∃ H : Matrix (Fin n) (Fin n) GaussianRational,
        (gaussianQuaternaryComplete hm W hWG).1=some H ∧
        (∀ i j,IsFourthRoot (gaussianRationalEmbed (H i j))) ∧
        (H.map gaussianRationalEmbed).conjTranspose*(H.map gaussianRationalEmbed)=
          (n : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) ∧
        (∀ i j,gaussianRationalEmbed (H i (Fin.castLE hm j))=V i j) ∧
        (gaussianQuaternaryComplete hm W hWG).2≤21 := by
  obtain ⟨W,hW,hmap⟩ := gaussianEncoding_of_fourth_roots V hV
  have hWG : W.conjTranspose*W=(n : GaussianRational) •
      (1 : Matrix (Fin m) (Fin m) GaussianRational) := by
    apply gaussianGram_reflect
    rw [hmap]
    exact hgram
  obtain ⟨⟨H,hRun,hH,hHG,hret⟩,hcount⟩ :=
    exact_quaternary_completion_algorithm hClassical hn hm hr W hW hWG
  refine ⟨W,hWG,hW,hmap,H,hRun,?_,gaussianGram_transport H hHG,?_,hcount⟩
  · intro i j
    exact (gaussianFourthRoot_iff _).mp (hH i j)
  · intro i j
    rw [hret]
    exact congrFun (congrFun hmap i) j

end CompletionTheory
