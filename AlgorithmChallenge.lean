/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib
@[expose] public section
set_option maxHeartbeats 4000000
set_option autoImplicit false
namespace CompletionTheory
open Matrix
def IsFourthRoot (z : ℂ) : Prop := z=1 ∨ z= -1 ∨ z=Complex.I ∨ z= -Complex.I
def IsCubeVector {K ι : Type*} [One K] [Neg K] (v : ι → K) : Prop := ∀ i,v i=1 ∨ v i= -1
def appendFourthColumn {n m : ℕ} (V : Matrix (Fin n) (Fin m) ℂ)
    (z : Fin n → ℂ) : Matrix (Fin n) (Fin (m+1)) ℂ :=
  fun i => Fin.snoc (V i) (z i)


def RealSmallDefectExtension : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℝ),
    4 ∣ Fintype.card ι → Fintype.card κ < Fintype.card ι →
    Fintype.card ι-Fintype.card κ ≤ 7 →
    (∀ i j,A i j=1 ∨ A i j= -1) →
    A.transpose*A=(Fintype.card ι : ℝ) • (1 : Matrix κ κ ℝ) →
    ∃ w : ι → ℝ,IsCubeVector w ∧ A.transpose.mulVec w=0


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

theorem gaussianRationalEmbed_injective : Function.Injective gaussianRationalEmbed := by sorry

theorem gaussianRationalEmbed_coordinates (z : GaussianRational) :
    gaussianRationalEmbed z=(z.re : ℂ)+(z.im : ℂ)*Complex.I := by sorry

def gaussianImaginary : GaussianRational := ⟨0,1⟩

def IsGaussianFourthRoot (z : GaussianRational) : Prop :=
  z=1 ∨ z= -1 ∨ z=gaussianImaginary ∨ z= -gaussianImaginary

instance gaussianFourthRoot_decidable (z : GaussianRational) : Decidable (IsGaussianFourthRoot z) :=
  inferInstanceAs (Decidable (z=1 ∨ z= -1 ∨ z=gaussianImaginary ∨ z= -gaussianImaginary))

theorem gaussianRationalEmbed_imaginary : gaussianRationalEmbed gaussianImaginary=Complex.I := by sorry

theorem gaussianRationalEmbed_star (z : GaussianRational) :
    gaussianRationalEmbed (star z)=star (gaussianRationalEmbed z) := by sorry

theorem gaussianRationalEmbed_mulVec {ι κ : Type*} [Fintype κ]
    (A : Matrix ι κ GaussianRational) (z : κ → GaussianRational) (i : ι) :
    gaussianRationalEmbed (A.mulVec z i)=
      ((A.map gaussianRationalEmbed).mulVec (gaussianRationalEmbed ∘ z)) i := by sorry

theorem gaussianFourthRoot_iff (z : GaussianRational) :
    IsGaussianFourthRoot z ↔ IsFourthRoot (gaussianRationalEmbed z) := by sorry

theorem gaussianKernel_reflection {ι κ : Type*} [Fintype κ]
    (A : Matrix ι κ GaussianRational) (z : κ → GaussianRational) :
    (A.map gaussianRationalEmbed).mulVec (gaussianRationalEmbed ∘ z)=0 ↔
      A.mulVec z=0 := by sorry

theorem gaussianConjTranspose_map {ι κ : Type*} (A : Matrix ι κ GaussianRational) :
    A.conjTranspose.map gaussianRationalEmbed=(A.map gaussianRationalEmbed).conjTranspose := by sorry

variable {K : Type*} [Field K] {m n : ℕ}

def gaussianPivotLift (A : Matrix (Fin (m+1)) (Fin (n+1)) K)
    (j : Fin (n+1)) (u : Fin n → K) : Fin (n+1) → K :=
  Fin.insertNth j (-(∑ k, A 0 (j.succAbove k)*u k)/A 0 j) u

def gaussianSchur (A : Matrix (Fin (m+1)) (Fin (n+1)) K)
    (j : Fin (n+1)) : Matrix (Fin m) (Fin n) K :=
  fun i k => A i.succ (j.succAbove k)-A i.succ j/A 0 j*A 0 (j.succAbove k)

theorem gaussianPivotLift_head (A : Matrix (Fin (m+1)) (Fin (n+1)) K)
    (j : Fin (n+1)) (hp : A 0 j≠0) (u : Fin n → K) :
    A.mulVec (gaussianPivotLift A j u) 0=0 := by sorry

theorem gaussianPivotLift_tail (A : Matrix (Fin (m+1)) (Fin (n+1)) K)
    (j : Fin (n+1)) (u : Fin n → K) (i : Fin m) :
    A.mulVec (gaussianPivotLift A j u) i.succ=(gaussianSchur A j).mulVec u i := by sorry

theorem gaussianPivotLift_recover (A : Matrix (Fin (m+1)) (Fin (n+1)) K)
    (j : Fin (n+1)) (hp : A 0 j≠0) (x : Fin (n+1) → K)
    (hx : A.mulVec x 0=0) :
    gaussianPivotLift A j (fun k => x (j.succAbove k))=x := by sorry

theorem gaussianSchur_surjective (A : Matrix (Fin (m+1)) (Fin (n+1)) K)
    (j : Fin (n+1)) (hp : A 0 j≠0) (hA : Function.Surjective A.mulVecLin) :
    Function.Surjective (gaussianSchur A j).mulVecLin := by sorry

theorem gaussian_nonzero_pivot (A : Matrix (Fin (m+1)) (Fin (n+1)) K)
    (hA : Function.Surjective A.mulVecLin) : ∃ j,A 0 j≠0 := by sorry

def gaussianFirstPivot [DecidableEq K]
    (A : Matrix (Fin (m+1)) (Fin (n+1)) K)
    (hA : Function.Surjective A.mulVecLin) : Fin (n+1) :=
  (Finset.univ.filter (fun j => A 0 j≠0)).min' (by
    obtain ⟨j,hj⟩ := gaussian_nonzero_pivot A hA
    exact ⟨j,by simp [hj]⟩)

theorem gaussianFirstPivot_nonzero [DecidableEq K]
    (A : Matrix (Fin (m+1)) (Fin (n+1)) K)
    (hA : Function.Surjective A.mulVecLin) : A 0 (gaussianFirstPivot A hA)≠0 := by sorry

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
    IsGaussianFourthRoot (gaussianFourthAlphabet a) := by sorry

theorem gaussianFourthAlphabet_surjective (z : GaussianRational)
    (hz : IsGaussianFourthRoot z) : ∃ a : Fin 4,gaussianFourthAlphabet a=z := by sorry

theorem gaussianFourthRoot_star_self {z : GaussianRational}
    (hz : IsGaussianFourthRoot z) : star z*z=1 := by sorry

theorem gaussianFourthRoot_star_mul {z w : GaussianRational}
    (hz : IsGaussianFourthRoot z) (hw : IsGaussianFourthRoot w) :
    IsGaussianFourthRoot (star z*w) := by sorry

def exactGaussianFourthCandidates {m n : ℕ} {A : Matrix (Fin m) (Fin n) GaussianRational}
    (D : ExactGaussianKernelData A) (j : Fin D.freeCount) : Finset (Fin n → GaussianRational) :=
  (Finset.univ.image (fun b : {k : Fin D.freeCount // k≠j} → Fin 4 =>
    D.reconstruct (fun k => if h : k=j then 1 else gaussianFourthAlphabet (b ⟨k,h⟩)))).filter
    (fun v => ∀ i,IsGaussianFourthRoot (v i))

theorem exactGaussianFourthCandidates_sound {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) GaussianRational} (D : ExactGaussianKernelData A)
    (j : Fin D.freeCount) (v : Fin n → GaussianRational)
    (hv : v∈exactGaussianFourthCandidates D j) :
    (∀ i,IsGaussianFourthRoot (v i)) ∧ A.mulVec v=0 ∧ v (D.positions j)=1 := by sorry

theorem exactGaussianFourthCandidates_card {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) GaussianRational} (D : ExactGaussianKernelData A)
    (j : Fin D.freeCount) : (exactGaussianFourthCandidates D j).card≤4^(n-m-1) := by sorry

theorem exactGaussianFourthCandidates_complete {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) GaussianRational} (D : ExactGaussianKernelData A)
    (j : Fin D.freeCount) :
    (exactGaussianFourthCandidates D j).Nonempty ↔
      ∃ z : Fin n → GaussianRational,(∀ i,IsGaussianFourthRoot (z i)) ∧ A.mulVec z=0 := by sorry

def fourthAssignmentList {κ : Type*} [DecidableEq κ] : List κ → List (κ → Fin 4)
  | [] => [fun _ => 0]
  | k::ks => ([0,1,2,3] : List (Fin 4)).flatMap
      (fun a => (fourthAssignmentList ks).map (fun b => Function.update b k a))

theorem fourthAssignmentList_length {κ : Type*} [DecidableEq κ] (ks : List κ) :
    (fourthAssignmentList ks).length=4^ks.length := by sorry

theorem fourthAssignmentList_cover {κ : Type*} [DecidableEq κ]
    (ks : List κ) (b : κ → Fin 4) :
    ∃ c∈fourthAssignmentList ks,∀ k∈ks,c k=b k := by sorry

def countedFind {α : Type*} (p : α → Prop) [DecidablePred p] : List α → Option α × ℕ
  | [] => (none,0)
  | x::xs => if p x then (some x,1) else
      let r := countedFind p xs
      (r.1,r.2+1)

theorem countedFind_count_le {α : Type*} (p : α → Prop) [DecidablePred p]
    (xs : List α) : (countedFind p xs).2≤xs.length := by sorry

theorem countedFind_sound {α : Type*} (p : α → Prop) [DecidablePred p]
    (xs : List α) (v : α) (h : (countedFind p xs).1=some v) : p v ∧ v∈xs := by sorry

theorem countedFind_none_iff {α : Type*} (p : α → Prop) [DecidablePred p]
    (xs : List α) : (countedFind p xs).1=none ↔ ∀ x∈xs,¬p x := by sorry

theorem fourthAssignmentList_mem_of_cover {κ : Type*} [DecidableEq κ]
    (ks : List κ) (hks : ∀ k,k∈ks) (b : κ → Fin 4) : b∈fourthAssignmentList ks := by sorry

def gaussianAssignmentKeys {m n : ℕ} {A : Matrix (Fin m) (Fin n) GaussianRational}
    (D : ExactGaussianKernelData A) (j : Fin D.freeCount) :
    List {k : Fin D.freeCount // k≠j} := Finset.univ.sort (·≤·)

theorem gaussianAssignmentKeys_mem {m n : ℕ} {A : Matrix (Fin m) (Fin n) GaussianRational}
    (D : ExactGaussianKernelData A) (j : Fin D.freeCount)
    (k : {k : Fin D.freeCount // k≠j}) : k∈gaussianAssignmentKeys D j := by sorry

def gaussianCandidateList {m n : ℕ} {A : Matrix (Fin m) (Fin n) GaussianRational}
    (D : ExactGaussianKernelData A) (j : Fin D.freeCount) : List (Fin n → GaussianRational) :=
  (fourthAssignmentList (gaussianAssignmentKeys D j)).map
    (fun b => D.reconstruct (fun k => if h : k=j then 1 else gaussianFourthAlphabet (b ⟨k,h⟩)))

theorem gaussianCandidateList_length {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) GaussianRational} (D : ExactGaussianKernelData A)
    (j : Fin D.freeCount) : (gaussianCandidateList D j).length=4^(n-m-1) := by sorry

theorem gaussianCandidateList_mem_iff {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) GaussianRational} (D : ExactGaussianKernelData A)
    (j : Fin D.freeCount) (v : Fin n → GaussianRational) :
    v∈gaussianCandidateList D j ↔
      ∃ b : {k : Fin D.freeCount // k≠j} → Fin 4,
        D.reconstruct (fun k => if h : k=j then 1 else gaussianFourthAlphabet (b ⟨k,h⟩))=v := by sorry

theorem gaussianCandidateList_filter_iff {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) GaussianRational} (D : ExactGaussianKernelData A)
    (j : Fin D.freeCount) (v : Fin n → GaussianRational) :
    v∈exactGaussianFourthCandidates D j ↔
      v∈gaussianCandidateList D j ∧ ∀ i,IsGaussianFourthRoot (v i) := by sorry

def exactGaussianFourthSearch {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) GaussianRational} (D : ExactGaussianKernelData A)
    (j : Fin D.freeCount) : Option (Fin n → GaussianRational) × ℕ :=
  countedFind (fun v => ∀ i,IsGaussianFourthRoot (v i)) (gaussianCandidateList D j)

theorem exactGaussianFourthSearch_count {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) GaussianRational} (D : ExactGaussianKernelData A)
    (j : Fin D.freeCount) : (exactGaussianFourthSearch D j).2≤4^(n-m-1) := by sorry

theorem exactGaussianFourthSearch_sound {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) GaussianRational} (D : ExactGaussianKernelData A)
    (j : Fin D.freeCount) (v : Fin n → GaussianRational)
    (h : (exactGaussianFourthSearch D j).1=some v) :
    (∀ i,IsGaussianFourthRoot (v i)) ∧ A.mulVec v=0 ∧ v (D.positions j)=1 := by sorry

theorem exactGaussianFourthSearch_none_iff {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) GaussianRational} (D : ExactGaussianKernelData A)
    (j : Fin D.freeCount) : (exactGaussianFourthSearch D j).1=none ↔
      ¬∃ z : Fin n → GaussianRational,(∀ i,IsGaussianFourthRoot (z i)) ∧ A.mulVec z=0 := by sorry

theorem gaussianGram_transport {n m : ℕ} (V : Matrix (Fin n) (Fin m) GaussianRational)
    (hgram : V.conjTranspose*V=(n : GaussianRational) • (1 : Matrix (Fin m) (Fin m) GaussianRational)) :
    (V.map gaussianRationalEmbed).conjTranspose*(V.map gaussianRationalEmbed)=
      (n : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) := by sorry

theorem gaussianAdjoint_surjective {n m : ℕ} (hn : 0<n)
    (V : Matrix (Fin n) (Fin m) GaussianRational)
    (hgram : V.conjTranspose*V=(n : GaussianRational) • (1 : Matrix (Fin m) (Fin m) GaussianRational)) :
    Function.Surjective V.conjTranspose.mulVecLin := by sorry

theorem complexFourthRoot_has_gaussian (z : ℂ) (hz : IsFourthRoot z) :
    ∃ w : GaussianRational,IsGaussianFourthRoot w ∧ gaussianRationalEmbed w=z := by sorry

theorem small_defect_gaussian_extension_exists (hClassical : RealSmallDefectExtension)
    {n m : ℕ} (hn : Even n) (hm : m<n) (hr : n-m≤3)
    (V : Matrix (Fin n) (Fin m) GaussianRational)
    (hV : ∀ i j,IsGaussianFourthRoot (V i j))
    (hgram : V.conjTranspose*V=(n : GaussianRational) • (1 : Matrix (Fin m) (Fin m) GaussianRational)) :
    ∃ z : Fin n → GaussianRational,(∀ i,IsGaussianFourthRoot (z i)) ∧ V.conjTranspose.mulVec z=0 := by sorry

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
    (gaussianQuaternaryExtensionStep hm V hgram).2≤4^(n-m-1) := by sorry

theorem gaussianQuaternaryExtensionStep_sound {n m : ℕ} (hm : m<n)
    (V : Matrix (Fin n) (Fin m) GaussianRational)
    (hgram : V.conjTranspose*V=(n : GaussianRational) • (1 : Matrix (Fin m) (Fin m) GaussianRational))
    (z : Fin n → GaussianRational) (h : (gaussianQuaternaryExtensionStep hm V hgram).1=some z) :
    (∀ i,IsGaussianFourthRoot (z i)) ∧ V.conjTranspose.mulVec z=0 := by sorry

theorem gaussianQuaternaryExtensionStep_success (hClassical : RealSmallDefectExtension)
    {n m : ℕ} (hn : Even n) (hm : m<n) (hr : n-m≤3)
    (V : Matrix (Fin n) (Fin m) GaussianRational)
    (hV : ∀ i j,IsGaussianFourthRoot (V i j))
    (hgram : V.conjTranspose*V=(n : GaussianRational) • (1 : Matrix (Fin m) (Fin m) GaussianRational)) :
    ∃ z,(gaussianQuaternaryExtensionStep hm V hgram).1=some z ∧
      (∀ i,IsGaussianFourthRoot (z i)) ∧ V.conjTranspose.mulVec z=0 := by sorry

theorem gaussianGram_reflect {n m : ℕ} (V : Matrix (Fin n) (Fin m) GaussianRational)
    (hgram : (V.map gaussianRationalEmbed).conjTranspose*(V.map gaussianRationalEmbed)=
      (n : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) :
    V.conjTranspose*V=(n : GaussianRational) • (1 : Matrix (Fin m) (Fin m) GaussianRational) := by sorry

def gaussianAppendColumn {n m : ℕ} (V : Matrix (Fin n) (Fin m) GaussianRational)
    (z : Fin n → GaussianRational) : Matrix (Fin n) (Fin (m+1)) GaussianRational :=
  fun i => Fin.snoc (V i) (z i)

theorem gaussianAppendColumn_map {n m : ℕ} (V : Matrix (Fin n) (Fin m) GaussianRational)
    (z : Fin n → GaussianRational) :
    (gaussianAppendColumn V z).map gaussianRationalEmbed=
      appendFourthColumn (V.map gaussianRationalEmbed) (gaussianRationalEmbed ∘ z) := by sorry

theorem gaussianAppendColumn_roots {n m : ℕ} (V : Matrix (Fin n) (Fin m) GaussianRational)
    (z : Fin n → GaussianRational) (hV : ∀ i j,IsGaussianFourthRoot (V i j))
    (hz : ∀ i,IsGaussianFourthRoot (z i)) :
    ∀ i j,IsGaussianFourthRoot (gaussianAppendColumn V z i j) := by sorry

theorem gaussianAppendColumn_gram {n m : ℕ} (V : Matrix (Fin n) (Fin m) GaussianRational)
    (z : Fin n → GaussianRational) (hz : ∀ i,IsGaussianFourthRoot (z i))
    (hgram : V.conjTranspose*V=(n : GaussianRational) • (1 : Matrix (Fin m) (Fin m) GaussianRational))
    (horth : V.conjTranspose.mulVec z=0) :
    (gaussianAppendColumn V z).conjTranspose*(gaussianAppendColumn V z)=
      (n : GaussianRational) • (1 : Matrix (Fin (m+1)) (Fin (m+1)) GaussianRational) := by sorry

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

theorem gaussianCompletionTestBudget_zero : gaussianCompletionTestBudget 0=0 := by sorry

theorem gaussianCompletionTestBudget_succ (r : ℕ) :
    gaussianCompletionTestBudget (r+1)=gaussianCompletionTestBudget r+4^r := by sorry

theorem gaussianCompletionTestBudget_le_twentyone {r : ℕ} (hr : r≤3) :
    gaussianCompletionTestBudget r≤21 := by sorry

theorem gaussianQuaternaryComplete_count {n m : ℕ} (hm : m≤n)
    (V : Matrix (Fin n) (Fin m) GaussianRational)
    (hgram : V.conjTranspose*V=(n : GaussianRational) • (1 : Matrix (Fin m) (Fin m) GaussianRational)) :
    (gaussianQuaternaryComplete hm V hgram).2≤gaussianCompletionTestBudget (n-m) := by sorry

theorem gaussianQuaternaryComplete_correct (hClassical : RealSmallDefectExtension)
    {n m : ℕ} (hn : Even n) (hm : m≤n) (hr : n-m≤3)
    (V : Matrix (Fin n) (Fin m) GaussianRational)
    (hV : ∀ i j,IsGaussianFourthRoot (V i j))
    (hgram : V.conjTranspose*V=(n : GaussianRational) • (1 : Matrix (Fin m) (Fin m) GaussianRational)) :
    ∃ H : Matrix (Fin n) (Fin n) GaussianRational,
      (gaussianQuaternaryComplete hm V hgram).1=some H ∧
      (∀ i j,IsGaussianFourthRoot (H i j)) ∧
      H.conjTranspose*H=(n : GaussianRational) • (1 : Matrix (Fin n) (Fin n) GaussianRational) ∧
      ∀ i j,H i (Fin.castLE hm j)=V i j := by sorry

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
      (gaussianQuaternaryComplete hm V hgram).2≤21 := by sorry

theorem gaussianEncoding_of_fourth_roots {n m : ℕ} (V : Matrix (Fin n) (Fin m) ℂ)
    (hV : ∀ i j,IsFourthRoot (V i j)) :
    ∃ W : Matrix (Fin n) (Fin m) GaussianRational,
      (∀ i j,IsGaussianFourthRoot (W i j)) ∧ W.map gaussianRationalEmbed=V := by sorry

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
        (gaussianQuaternaryComplete hm W hWG).2≤21 := by sorry

end CompletionTheory
