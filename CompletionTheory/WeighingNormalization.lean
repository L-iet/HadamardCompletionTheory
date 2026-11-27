/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.RepetitionObstruction
public import CompletionTheory.SignedTwoBlocks
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.ZMod.Basic
@[expose] public section
set_option maxHeartbeats 2000000
namespace CompletionTheory
open Matrix

noncomputable def zeroRowSet {ι : Type*} [Fintype ι] (W : Matrix ι ι ℝ) (i : ι) : Finset ι := by
  classical
  exact Finset.univ.filter (fun j => W i j=0)

theorem weighing_two_row_zero_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix ι ι ℝ) (hW : IsWeighing W ((Fintype.card ι : ℝ)-2)) (i : ι) :
    (zeroRowSet W i).card=2 := by
  classical
  have hNorm := congrArg (fun M => M i i) hW.2
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,
    ite_true,mul_one] at hNorm
  have hZ : ((zeroRowSet W i).card : ℝ)=∑ j,(1-W i j*W i j) := by
    unfold zeroRowSet
    rw [Finset.card_eq_sum_ones,Nat.cast_sum]
    simp only [Nat.cast_one,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    rcases hW.1 i j with h0|hS
    · simp [h0]
    · rcases hS with h|h <;> simp [h]
  rw [Finset.sum_sub_distrib] at hZ
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hZ
  have hc : ((zeroRowSet W i).card : ℝ)=2 := by linarith
  exact_mod_cast hc

theorem square_column_gram_of_row_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix ι ι ℝ) (c : ℝ) (hc : c≠0) (hW : W*W.transpose=c • (1 : Matrix ι ι ℝ)) :
    W.transpose*W=c • (1 : Matrix ι ι ℝ) := by
  let B := c⁻¹ • W.transpose
  have hWB : W*B=1 := by
    dsimp only [B]
    rw [Matrix.mul_smul,hW,smul_smul,inv_mul_cancel₀ hc,one_smul]
  have hBW : B*W=1 := mul_eq_one_comm.mp hWB
  have hh := congrArg (fun M : Matrix ι ι ℝ => c • M) hBW
  simpa only [B,Matrix.smul_mul,smul_smul,mul_inv_cancel₀ hc,one_smul] using hh

theorem weighing_two_column_zero_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix ι ι ℝ) (hW : IsWeighing W ((Fintype.card ι : ℝ)-2)) (hn : 3≤Fintype.card ι) (i : ι) :
    (zeroRowSet W.transpose i).card=2 := by
  have hc : (Fintype.card ι : ℝ)-2≠0 := by
    have hh : (3 : ℝ)≤Fintype.card ι := by exact_mod_cast hn
    linarith
  apply weighing_two_row_zero_card W.transpose
  refine ⟨fun i j => hW.1 j i,?_⟩
  simpa only [Matrix.transpose_transpose] using square_column_gram_of_row_gram W _ hc hW.2

theorem weighing_common_support_even {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix ι ι ℝ) (hW : IsWeighing W ((Fintype.card ι : ℝ)-2)) (i j : ι) (hij : i≠j) :
    Even ((zeroRowSet W i ∪ zeroRowSet W j)ᶜ.card) := by
  classical
  let K := (zeroRowSet W i ∪ zeroRowSet W j)ᶜ
  have hNZ (k : K) : W i k.val≠0 ∧ W j k.val≠0 := by
    have hm := Finset.mem_compl.mp k.property
    simpa only [Finset.mem_union,zeroRowSet,Finset.mem_filter,Finset.mem_univ,true_and,not_or] using hm
  have hSign (k : K) : IsSign (W i k.val*W j k.val) := by
    obtain ⟨hi,hj⟩ := hNZ k
    rcases hW.1 i k.val with h0|hS
    · exact False.elim (hi h0)
    · rcases hW.1 j k.val with h0|hT
      · exact False.elim (hj h0)
      · rcases hS with hs|hs <;> rcases hT with ht|ht <;> simp [hs,ht,IsSign]
  have hOrth : (∑ k : ι,W i k*W j k)=0 := by
    have hh := congrArg (fun M => M i j) hW.2
    simpa [Matrix.mul_apply,Matrix.transpose_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,hij] using hh
  have hOutside (k : ι) (hk : k∈Finset.univ) (hkK : k∉K) : W i k*W j k=0 := by
    have hm : k∈zeroRowSet W i ∪ zeroRowSet W j := by
      simpa only [K,Finset.mem_compl,not_not] using hkK
    rcases Finset.mem_union.mp hm with hi|hj
    · have hz := (Finset.mem_filter.mp hi).2
      rw [hz,zero_mul]
    · have hz := (Finset.mem_filter.mp hj).2
      rw [hz,mul_zero]
  have hSum : (∑ k : K,W i k.val*W j k.val)=0 := by
    calc
      _=∑ k∈K,W i k*W j k := Finset.sum_coe_sort _ _
      _=∑ k : ι,W i k*W j k := Finset.sum_subset (Finset.subset_univ _) hOutside
      _=0 := hOrth
  have he := sign_sum_zero_even (fun k : K => W i k.val*W j k.val) hSign hSum
  simpa only [Fintype.card_coe] using he

theorem weighing_zero_neighborhoods_equal_or_disjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix ι ι ℝ) (hW : IsWeighing W ((Fintype.card ι : ℝ)-2)) (hn : Even (Fintype.card ι))
    (i j : ι) : zeroRowSet W i=zeroRowSet W j ∨ Disjoint (zeroRowSet W i) (zeroRowSet W j) := by
  classical
  by_cases hij : i=j
  · subst j;exact Or.inl rfl
  have hEven := weighing_common_support_even W hW i j hij
  have hCardK := Finset.card_compl_add_card (zeroRowSet W i ∪ zeroRowSet W j)
  have hUnion := Finset.card_union_add_card_inter (zeroRowSet W i) (zeroRowSet W j)
  have hi := weighing_two_row_zero_card W hW i
  have hj := weighing_two_row_zero_card W hW j
  have hBound : (zeroRowSet W i ∩ zeroRowSet W j).card≤2 := by
    have hh := Finset.card_le_card (Finset.inter_subset_left (s₁ := zeroRowSet W i) (s₂ := zeroRowSet W j))
    omega
  have hCases : (zeroRowSet W i ∩ zeroRowSet W j).card=0 ∨ (zeroRowSet W i ∩ zeroRowSet W j).card=2 := by
    obtain ⟨a,ha⟩ := hEven
    obtain ⟨b,hb⟩ := hn
    omega
  rcases hCases with h0|h2
  · right
    exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp h0)
  · left
    have heI : zeroRowSet W i ∩ zeroRowSet W j=zeroRowSet W i :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have heJ : zeroRowSet W i ∩ zeroRowSet W j=zeroRowSet W j :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    exact heI.symm.trans heJ

theorem mem_zeroRowSet {ι : Type*} [Fintype ι] (W : Matrix ι ι ℝ) (i j : ι) :
    j∈zeroRowSet W i ↔ W i j=0 := by
  classical
  simp [zeroRowSet]

noncomputable def zeroNeighborhoodRows {ι : Type*} [Fintype ι] (W : Matrix ι ι ℝ) (Z : Finset ι) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => zeroRowSet W i=Z)

theorem zero_neighborhood_eq_iff_column_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix ι ι ℝ) (hW : IsWeighing W ((Fintype.card ι : ℝ)-2)) (hn : Even (Fintype.card ι))
    (i k : ι) (hk : k∈zeroRowSet W i) (j : ι) :
    zeroRowSet W j=zeroRowSet W i ↔ W j k=0 := by
  constructor
  · intro heq
    apply (mem_zeroRowSet W j k).mp
    rw [heq]
    exact hk
  · intro hz
    have hkj := (mem_zeroRowSet W j k).mpr hz
    rcases weighing_zero_neighborhoods_equal_or_disjoint W hW hn j i with heq|hd
    · exact heq
    · exact False.elim (Finset.disjoint_left.mp hd hkj hk)

theorem zeroNeighborhoodRows_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix ι ι ℝ) (hW : IsWeighing W ((Fintype.card ι : ℝ)-2))
    (hn : Even (Fintype.card ι)) (hn3 : 3≤Fintype.card ι) (i : ι) :
    (zeroNeighborhoodRows W (zeroRowSet W i)).card=2 := by
  classical
  have hc := weighing_two_row_zero_card W hW i
  obtain ⟨k,hk⟩ := Finset.card_pos.mp (show 0<(zeroRowSet W i).card by omega)
  have heq : zeroNeighborhoodRows W (zeroRowSet W i)=zeroRowSet W.transpose k := by
    ext j
    simp only [zeroNeighborhoodRows,Finset.mem_filter,Finset.mem_univ,true_and,mem_zeroRowSet,Matrix.transpose_apply]
    exact zero_neighborhood_eq_iff_column_zero W hW hn i k hk j
  rw [heq]
  exact weighing_two_column_zero_card W hW hn3 k

noncomputable def zeroBlockSet {ι : Type*} [Fintype ι] [DecidableEq ι] (W : Matrix ι ι ℝ) : Finset (Finset ι) :=
  Finset.univ.image (zeroRowSet W)

def ZeroBlockIndex {ι : Type*} [Fintype ι] [DecidableEq ι] (W : Matrix ι ι ℝ) := ↥(zeroBlockSet W)

noncomputable instance zeroBlockIndexFintype {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix ι ι ℝ) : Fintype (ZeroBlockIndex W) :=
  inferInstanceAs (Fintype ↥(zeroBlockSet W))

noncomputable def zeroBlockLabel {ι : Type*} [Fintype ι] [DecidableEq ι] (W : Matrix ι ι ℝ) (i : ι) :
    ZeroBlockIndex W := ⟨zeroRowSet W i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩

theorem zeroBlockIndex_column_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix ι ι ℝ) (hW : IsWeighing W ((Fintype.card ι : ℝ)-2)) (L : ZeroBlockIndex W) :
    L.val.card=2 := by
  have hm := L.property
  change L.val∈Finset.univ.image (zeroRowSet W) at hm
  obtain ⟨i,hi,hEq⟩ := Finset.mem_image.mp hm
  rw [← hEq]
  exact weighing_two_row_zero_card W hW i

theorem zeroBlockIndex_covers_columns {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix ι ι ℝ) (hW : IsWeighing W ((Fintype.card ι : ℝ)-2)) (hn3 : 3≤Fintype.card ι) (k : ι) :
    ∃ L : ZeroBlockIndex W,k∈L.val := by
  have hc := weighing_two_column_zero_card W hW hn3 k
  obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0<(zeroRowSet W.transpose k).card by omega)
  refine ⟨zeroBlockLabel W i,?_⟩
  change k∈zeroRowSet W i
  exact (mem_zeroRowSet W i k).mpr ((mem_zeroRowSet W.transpose k i).mp hi)

theorem zeroBlockLabel_fiber_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix ι ι ℝ) (hW : IsWeighing W ((Fintype.card ι : ℝ)-2))
    (hn : Even (Fintype.card ι)) (hn3 : 3≤Fintype.card ι) (L : ZeroBlockIndex W) :
    Nat.card {i : ι // zeroBlockLabel W i=L}=2 := by
  classical
  have hm := L.property
  change L.val∈Finset.univ.image (zeroRowSet W) at hm
  obtain ⟨i,hi,hEq⟩ := Finset.mem_image.mp hm
  have hp (j : ι) : zeroBlockLabel W j=L ↔ zeroRowSet W j=L.val := by
    constructor
    · intro h;exact congrArg (fun M : ZeroBlockIndex W => M.val) h
    · intro h;exact Subtype.ext h
  rw [Nat.card_congr (Equiv.subtypeEquivRight hp)]
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype]
  have hFilter : Finset.univ.filter (fun j => zeroRowSet W j=L.val)=zeroNeighborhoodRows W L.val := by
    ext j
    simp only [zeroNeighborhoodRows,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [hFilter,← hEq]
  exact zeroNeighborhoodRows_card W hW hn hn3 i

theorem zeroBlockIndex_equal_or_disjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix ι ι ℝ) (hW : IsWeighing W ((Fintype.card ι : ℝ)-2)) (hn : Even (Fintype.card ι))
    (L M : ZeroBlockIndex W) : L=M ∨ Disjoint L.val M.val := by
  have hL := L.property
  have hM := M.property
  change L.val∈Finset.univ.image (zeroRowSet W) at hL
  change M.val∈Finset.univ.image (zeroRowSet W) at hM
  obtain ⟨i,hi,heI⟩ := Finset.mem_image.mp hL
  obtain ⟨j,hj,heJ⟩ := Finset.mem_image.mp hM
  rcases weighing_zero_neighborhoods_equal_or_disjoint W hW hn i j with heq|hd
  · left;exact Subtype.ext (heI.symm.trans (heq.trans heJ))
  · right;rw [← heI,← heJ];exact hd

theorem weighing_zero_support_paired_equivalences {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix ι ι ℝ) (hW : IsWeighing W ((Fintype.card ι : ℝ)-2))
    (hn : Even (Fintype.card ι)) (hn3 : 3≤Fintype.card ι) :
    ∃ r c : (Fin 2×ZeroBlockIndex W) ≃ ι,
      (∀ a b : Fin 2,∀ L M : ZeroBlockIndex W,W (r (a,L)) (c (b,M))=0 ↔ L=M) ∧
      2*Fintype.card (ZeroBlockIndex W)=Fintype.card ι := by
  classical
  let B := ZeroBlockIndex W
  have hRow (L : B) : Fintype.card {i : ι // zeroBlockLabel W i=L}=2 := by
    simpa only [Nat.card_eq_fintype_card] using zeroBlockLabel_fiber_card W hW hn hn3 L
  let eR (L : B) : Fin 2 ≃ {i : ι // zeroBlockLabel W i=L} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin,hRow L])
  let eC (L : B) : Fin 2 ≃ ↥L.val :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin,Fintype.card_coe,zeroBlockIndex_column_card W hW L])
  let r : (Fin 2×B) ≃ ι := (Equiv.prodComm (Fin 2) B).trans
    (((Equiv.sigmaEquivProd B (Fin 2)).symm.trans (Equiv.sigmaCongrRight eR)).trans
      (Equiv.sigmaFiberEquiv (zeroBlockLabel W)))
  have hr (a : Fin 2) (L : B) : r (a,L)=(eR L a).val := rfl
  have hRLabel (a : Fin 2) (L : B) : zeroBlockLabel W (r (a,L))=L := by
    rw [hr];exact (eR L a).property
  have hColInj : Function.Injective (fun x : (Σ L : B,↥L.val) => x.2.val) := by
    rintro ⟨L,a⟩ ⟨M,b⟩ hab
    change a.val=b.val at hab
    have hLM : L=M := by
      rcases zeroBlockIndex_equal_or_disjoint W hW hn L M with heq|hd
      · exact heq
      · apply False.elim
        apply Finset.disjoint_left.mp hd a.property
        rw [hab]
        exact b.property
    subst M
    exact congrArg (fun z : ↥L.val => (⟨L,z⟩ : Σ N : B,↥N.val)) (Subtype.ext hab)
  have hColSurj : Function.Surjective (fun x : (Σ L : B,↥L.val) => x.2.val) := by
    intro j
    obtain ⟨L,hj⟩ := zeroBlockIndex_covers_columns W hW hn3 j
    exact ⟨⟨L,⟨j,hj⟩⟩,rfl⟩
  let colEquiv : (Σ L : B,↥L.val) ≃ ι := Equiv.ofBijective _ ⟨hColInj,hColSurj⟩
  let c : (Fin 2×B) ≃ ι := (Equiv.prodComm (Fin 2) B).trans
    (((Equiv.sigmaEquivProd B (Fin 2)).symm.trans (Equiv.sigmaCongrRight eC)).trans colEquiv)
  have hc (a : Fin 2) (L : B) : c (a,L)=(eC L a).val := rfl
  have hCmem (a : Fin 2) (L : B) : c (a,L)∈L.val := by rw [hc];exact (eC L a).property
  refine ⟨r,c,?_,?_⟩
  · intro a b L M
    have hZ : zeroRowSet W (r (a,L))=L.val :=
      congrArg (fun N : B => N.val) (hRLabel a L)
    constructor
    · intro hz
      have hMem := (mem_zeroRowSet W (r (a,L)) (c (b,M))).mpr hz
      rw [hZ] at hMem
      rcases zeroBlockIndex_equal_or_disjoint W hW hn L M with heq|hd
      · exact heq
      · exact False.elim (Finset.disjoint_left.mp hd hMem (hCmem b M))
    · intro heq
      subst M
      apply (mem_zeroRowSet W (r (a,L)) (c (b,L))).mp
      rw [hZ]
      exact hCmem b L
  · have hcard := Fintype.card_congr r
    simpa only [Fintype.card_prod,Fintype.card_fin] using hcard


theorem weighing_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (W : Matrix ι ι ℝ) (w : ℝ)
    (hW : IsWeighing W w) (r c : κ ≃ ι) : IsWeighing (W.submatrix r c) w := by
  constructor
  · intro i j;exact hW.1 (r i) (c j)
  · change W.submatrix r c * W.transpose.submatrix c r = w • (1 : Matrix κ κ ℝ)
    rw [Matrix.submatrix_mul_equiv,hW.2]
    ext i j
    change w * (1 : Matrix ι ι ℝ) (r i) (r j) = w * (1 : Matrix κ κ ℝ) i j
    simp only [Matrix.one_apply,r.injective.eq_iff]

noncomputable instance zeroBlockIndexDecidableEq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix ι ι ℝ) : DecidableEq (ZeroBlockIndex W) := Classical.decEq _

theorem weighing_paired_block_form {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix ι ι ℝ) (hW : IsWeighing W ((Fintype.card ι : ℝ)-2))
    (hn : Even (Fintype.card ι)) (hn3 : 3≤Fintype.card ι) :
    ∃ r c : (Fin 2×ZeroBlockIndex W) ≃ ι,
      IsWeighing (W.submatrix r c) ((Fintype.card ι : ℝ)-2) ∧
      (∀ i,twoBlock (W.submatrix r c) i i=0) ∧
      (∀ i j,i≠j → IsSignMatrix (twoBlock (W.submatrix r c) i j)) ∧
      2*Fintype.card (ZeroBlockIndex W)=Fintype.card ι := by
  classical
  obtain ⟨r,c,hZero,hCard⟩ := weighing_zero_support_paired_equivalences W hW hn hn3
  refine ⟨r,c,weighing_reindex W _ hW r c,?_,?_,hCard⟩
  · intro i;ext a b
    exact (hZero a b i i).mpr rfl
  · intro i j hij a b
    have hNZ : W (r (a,i)) (c (b,j))≠0 := fun h => hij ((hZero a b i j).mp h)
    rcases hW.1 (r (a,i)) (c (b,j)) with h0|hS
    · exact False.elim (hNZ h0)
    · exact hS



def integerTwoBlock {ι : Type*} (W : Matrix (Fin 2×ι) (Fin 2×ι) ℤ) (i j : ι) : Matrix (Fin 2) (Fin 2) ℤ := fun a b => W (a,i) (b,j)

def rawTwoTransform (B : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  fun a b => (B*walshTwoInt) a b / 2

theorem rawTwoTransform_zero : rawTwoTransform 0=0 := by
  ext a b
  simp [rawTwoTransform]

theorem signTwo_transform_reconstruct : ∀ b : Fin 2 → Fin 2 → Bool,
    rawTwoTransform (signTwoInt b)*walshTwoInt=signTwoInt b := by decide +kernel

theorem signTwo_transform_row_parity : ∀ b : Fin 2 → Fin 2 → Bool,∀ a : Fin 2,
    (∑ c : Fin 2,(rawTwoTransform (signTwoInt b) a c : ZMod 2))=1 := by decide +kernel

theorem signTwo_transform_column_certificate : ∀ b : Fin 2 → Fin 2 → Bool,
    (∀ c : Fin 2,(∑ a : Fin 2,(rawTwoTransform (signTwoInt b) a c : ZMod 2))=1) →
    ∃ d : SignedTwoState,rawTwoTransform (signTwoInt b)=signedTwoInt d := by decide +kernel


def pairIndicatorTwo {ι : Type*} [DecidableEq ι] : Matrix (Fin 2×ι) ι (ZMod 2) :=
  fun p j => if p.2=j then 1 else 0

def blockFlipTwo {ι : Type*} [DecidableEq ι] : Matrix ι ι (ZMod 2) :=
  fun i j => if i=j then 0 else 1

theorem even_card_cast_two {ι : Type*} [Fintype ι] (hn : Even (Fintype.card ι)) :
    (Fintype.card ι : ZMod 2)=0 := by
  obtain ⟨k,hk⟩ := hn
  rw [hk,Nat.cast_add,← two_mul,show (2 : ZMod 2)=0 by decide,zero_mul]

theorem blockFlipTwo_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hn : Even (Fintype.card ι)) : (blockFlipTwo : Matrix ι ι (ZMod 2))*blockFlipTwo=1 := by
  let J : Matrix ι ι (ZMod 2) := fun _ _ => 1
  have hJ : J*J=0 := by
    ext i j
    change (∑ _ : ι,(1 : ZMod 2)*(1 : ZMod 2))=0
    simpa only [one_mul,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using even_card_cast_two hn
  have hBJ : (blockFlipTwo : Matrix ι ι (ZMod 2)) = J-1 := by
    ext i j
    change (if i=j then (0 : ZMod 2) else 1) = 1 - (1 : Matrix ι ι (ZMod 2)) i j
    by_cases hij : i=j <;> simp [Matrix.one_apply,hij]
  rw [hBJ]
  simp only [sub_mul,mul_sub,hJ,mul_one,one_mul]
  ext i j
  change ((0 : ZMod 2)-1-(1-(1 : Matrix ι ι (ZMod 2)) i j))=(1 : Matrix ι ι (ZMod 2)) i j
  by_cases hij : i=j <;> simp only [Matrix.one_apply,hij,ite_true,ite_false] <;> decide +kernel

theorem mul_pairIndicatorTwo_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix (Fin 2×ι) (Fin 2×ι) (ZMod 2)) (a : Fin 2) (i j : ι) :
    (A * (pairIndicatorTwo (ι := ι))) (a,i) j=∑ b : Fin 2,A (a,i) (b,j) := by
  simp [Matrix.mul_apply,Fintype.sum_prod_type,pairIndicatorTwo,mul_ite,eq_comm]

theorem pairIndicatorTwo_mul_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι (ZMod 2)) (a : Fin 2) (i j : ι) :
    ((pairIndicatorTwo (ι := ι)) * B) (a,i) j=B i j := by
  simp [Matrix.mul_apply,pairIndicatorTwo,ite_mul,eq_comm]

theorem block_row_parity_forces_column_parity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hn : Even (Fintype.card ι)) (A : Matrix (Fin 2×ι) (Fin 2×ι) (ZMod 2))
    (hA : A*A.transpose=1)
    (hRow : ∀ a : Fin 2,∀ i j : ι,(∑ b : Fin 2,A (a,i) (b,j))=if i=j then 0 else 1) :
    ∀ b : Fin 2,∀ i j : ι,(∑ a : Fin 2,A (a,i) (b,j))=if i=j then 0 else 1 := by
  have hAT : A.transpose*A=1 := mul_eq_one_comm.mp hA
  let E : Matrix (Fin 2×ι) ι (ZMod 2) := pairIndicatorTwo (ι := ι)
  let B : Matrix ι ι (ZMod 2) := blockFlipTwo (ι := ι)
  have hB : B*B=1 := blockFlipTwo_square hn
  have hAE : A*E=E*B := by
    ext ⟨a,i⟩ j
    change (A * pairIndicatorTwo (ι := ι)) (a,i) j = (pairIndicatorTwo (ι := ι) * B) (a,i) j
    rw [mul_pairIndicatorTwo_entry,pairIndicatorTwo_mul_entry,hRow]
    by_cases hij : i=j <;> simp [B,blockFlipTwo,Matrix.one_apply,hij]
  have hATE : A.transpose*E=E*B := by
    calc
      _=(A.transpose*E)*(B*B) := by rw [hB,Matrix.mul_one]
      _=(A.transpose*(E*B))*B := by simp only [Matrix.mul_assoc]
      _=(A.transpose*(A*E))*B := by rw [hAE]
      _=((A.transpose*A)*E)*B := by simp only [Matrix.mul_assoc]
      _=_ := by rw [hAT,Matrix.one_mul]
  intro b i j
  have hh := congrArg (fun M : Matrix (Fin 2×ι) ι (ZMod 2) => M (b,j) i) hATE
  change (A.transpose * pairIndicatorTwo (ι := ι)) (b,j) i = (pairIndicatorTwo (ι := ι) * B) (b,j) i at hh
  rw [mul_pairIndicatorTwo_entry,pairIndicatorTwo_mul_entry] at hh
  change (∑ a : Fin 2,A (a,i) (b,j))=B j i at hh
  by_cases hij : i=j <;> simpa [B,blockFlipTwo,Matrix.one_apply,hij,eq_comm] using hh



def rawPairedTransform {ι : Type*} (W : Matrix (Fin 2×ι) (Fin 2×ι) ℤ) :
    Matrix (Fin 2×ι) (Fin 2×ι) ℤ := fun p q => rawTwoTransform (integerTwoBlock W p.2 q.2) p.1 q.1

theorem integerTwoBlock_mul_blockDiagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix (Fin 2×ι) (Fin 2×ι) ℤ) (D : ι → Matrix (Fin 2) (Fin 2) ℤ) (i j : ι) :
    integerTwoBlock (M*Matrix.blockDiagonal D) i j=integerTwoBlock M i j*D j := by
  ext a b
  simp [integerTwoBlock,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.blockDiagonal_apply,mul_ite,eq_comm]

theorem rawPairedTransform_reconstruct {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix (Fin 2×ι) (Fin 2×ι) ℤ) (hDiag : ∀ i,integerTwoBlock W i i=0)
    (hOff : ∀ i j,i≠j → ∃ b : Fin 2 → Fin 2 → Bool,integerTwoBlock W i j=signTwoInt b) :
    rawPairedTransform W*Matrix.blockDiagonal (fun _ : ι => walshTwoInt)=W := by
  ext ⟨a,i⟩ ⟨b,j⟩
  have hh := integerTwoBlock_mul_blockDiagonal (rawPairedTransform W) (fun _ => walshTwoInt) i j
  have hBlock : integerTwoBlock (rawPairedTransform W) i j=rawTwoTransform (integerTwoBlock W i j) := rfl
  rw [hBlock] at hh
  by_cases hij : i=j
  · subst j
    rw [hDiag,rawTwoTransform_zero,Matrix.zero_mul] at hh
    have hZero := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M a b) (hDiag i)
    exact (congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M a b) hh).trans hZero.symm
  · obtain ⟨bits,hbits⟩ := hOff i j hij
    rw [hbits,signTwo_transform_reconstruct] at hh
    exact (congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M a b) hh).trans
      (congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M a b) hbits).symm

theorem walshTwoInt_gram : walshTwoInt*walshTwoInt.transpose=(2 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  decide +kernel

theorem rawPairedTransform_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix (Fin 2×ι) (Fin 2×ι) ℤ) (hDiag : ∀ i,integerTwoBlock W i i=0)
    (hOff : ∀ i j,i≠j → ∃ b : Fin 2 → Fin 2 → Bool,integerTwoBlock W i j=signTwoInt b)
    (hGram : W*W.transpose=(2*(Fintype.card ι : ℤ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℤ)) :
    rawPairedTransform W*(rawPairedTransform W).transpose=((Fintype.card ι : ℤ)-1) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℤ) := by
  let F : Matrix (Fin 2×ι) (Fin 2×ι) ℤ := Matrix.blockDiagonal (fun _ => walshTwoInt)
  have hF : F*F.transpose=(2 : ℤ) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℤ) := by
    dsimp only [F]
    rw [Matrix.blockDiagonal_transpose,← Matrix.blockDiagonal_mul]
    simp only [walshTwoInt_gram]
    change Matrix.blockDiagonal ((2 : ℤ) • (fun _ : ι => (1 : Matrix (Fin 2) (Fin 2) ℤ))) = _
    rw [Matrix.blockDiagonal_smul]
    change (2 : ℤ) • Matrix.blockDiagonal (1 : ι → Matrix (Fin 2) (Fin 2) ℤ) = _
    rw [Matrix.blockDiagonal_one]
  have hRec : rawPairedTransform W*F=W := rawPairedTransform_reconstruct W hDiag hOff
  rw [← hRec,Matrix.transpose_mul] at hGram
  have hEq : (rawPairedTransform W*F)*(F.transpose*(rawPairedTransform W).transpose)=
      (2 : ℤ) • (rawPairedTransform W*(rawPairedTransform W).transpose) := by
    calc
      _=(rawPairedTransform W*(F*F.transpose))*(rawPairedTransform W).transpose := by simp only [Matrix.mul_assoc]
      _=_ := by rw [hF,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul]
  rw [hEq] at hGram
  ext p q
  have hh := congrArg (fun M : Matrix (Fin 2×ι) (Fin 2×ι) ℤ => M p q) hGram
  simp only [Matrix.smul_apply,smul_eq_mul] at hh ⊢
  nlinarith


theorem rawPairedTransform_mod_two_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hn : Even (Fintype.card ι)) (N : Matrix (Fin 2×ι) (Fin 2×ι) ℤ)
    (hN : N*N.transpose=((Fintype.card ι : ℤ)-1) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℤ)) :
    N.map (Int.castRingHom (ZMod 2)) * (N.map (Int.castRingHom (ZMod 2))).transpose=1 := by
  have hm := congrArg (fun M : Matrix (Fin 2×ι) (Fin 2×ι) ℤ => M.map (Int.castRingHom (ZMod 2))) hN
  rw [Matrix.map_mul,Matrix.transpose_map] at hm
  rw [hm]
  ext p q
  have hEven := even_card_cast_two hn
  simp only [Matrix.map_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
  change (((((Fintype.card ι : ℤ)-1)*(if p=q then 1 else 0)) : ℤ) : ZMod 2) = _
  push_cast
  rw [hEven]
  by_cases hpq : p=q <;> simp [hpq] <;> decide +kernel

theorem rawPairedTransform_row_parity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix (Fin 2×ι) (Fin 2×ι) ℤ) (hDiag : ∀ i,integerTwoBlock W i i=0)
    (hOff : ∀ i j,i≠j → ∃ b : Fin 2 → Fin 2 → Bool,integerTwoBlock W i j=signTwoInt b) :
    ∀ a : Fin 2,∀ i j : ι,(∑ b : Fin 2,(rawPairedTransform W (a,i) (b,j) : ZMod 2))=if i=j then 0 else 1 := by
  intro a i j
  change (∑ b : Fin 2,(rawTwoTransform (integerTwoBlock W i j) a b : ZMod 2))=_
  by_cases hij : i=j
  · subst j;rw [hDiag,rawTwoTransform_zero];simp
  · obtain ⟨bits,hbits⟩ := hOff i j hij
    rw [hbits,if_neg hij]
    exact signTwo_transform_row_parity bits a

theorem paired_weighing_integer_block_factor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hn : Even (Fintype.card ι))
    (W : Matrix (Fin 2×ι) (Fin 2×ι) ℤ) (hDiag : ∀ i,integerTwoBlock W i i=0)
    (hOff : ∀ i j,i≠j → ∃ b : Fin 2 → Fin 2 → Bool,integerTwoBlock W i j=signTwoInt b)
    (hGram : W*W.transpose=(2*(Fintype.card ι : ℤ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℤ)) :
    ∀ i j,i≠j → ∃ d : SignedTwoState,integerTwoBlock W i j=signedTwoInt d*walshTwoInt := by
  let A := (rawPairedTransform W).map (Int.castRingHom (ZMod 2))
  have hA : A*A.transpose=1 := rawPairedTransform_mod_two_gram hn _ (rawPairedTransform_gram W hDiag hOff hGram)
  have hRow : ∀ a : Fin 2,∀ i j : ι,(∑ b : Fin 2,A (a,i) (b,j))=if i=j then 0 else 1 :=
    rawPairedTransform_row_parity W hDiag hOff
  have hCol := block_row_parity_forces_column_parity hn A hA hRow
  intro i j hij
  obtain ⟨bits,hbits⟩ := hOff i j hij
  have hLocal : ∀ c : Fin 2,(∑ a : Fin 2,(rawTwoTransform (signTwoInt bits) a c : ZMod 2))=1 := by
    intro c
    have hh := hCol c i j
    change (∑ a : Fin 2,(rawTwoTransform (integerTwoBlock W i j) a c : ZMod 2))=_ at hh
    simpa only [hbits,if_neg hij] using hh
  obtain ⟨d,hd⟩ := signTwo_transform_column_certificate bits hLocal
  refine ⟨d,?_⟩
  rw [hbits,← hd,signTwo_transform_reconstruct]



noncomputable def weighingIntegerModel {ι : Type*} (W : Matrix ι ι ℝ) : Matrix ι ι ℤ := by
  classical
  exact fun i j => if W i j=0 then 0 else if W i j=1 then 1 else -1

theorem weighingIntegerModel_cast {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix ι ι ℝ) (w : ℝ) (hW : IsWeighing W w) :
    (weighingIntegerModel W).map (Int.castRingHom ℝ)=W := by
  classical
  ext i j
  rcases hW.1 i j with h0|hS
  · simp [weighingIntegerModel,h0]
  · rcases hS with h|h <;> norm_num [weighingIntegerModel,h]

theorem integer_two_block_cast {ι : Type*} (W : Matrix (Fin 2×ι) (Fin 2×ι) ℤ) (i j : ι) :
    (integerTwoBlock W i j).map (Int.castRingHom ℝ)=twoBlock (W.map (Int.castRingHom ℝ)) i j := rfl

theorem paired_real_weighing_normalized {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hn : Even (Fintype.card ι))
    (W : Matrix (Fin 2×ι) (Fin 2×ι) ℝ)
    (hW : IsWeighing W ((Fintype.card (Fin 2×ι) : ℝ)-2))
    (hDiag : ∀ i,twoBlock W i i=0)
    (hOff : ∀ i j,i≠j → IsSignMatrix (twoBlock W i j)) : IsNormalizedTwoZeroWeighing W := by
  classical
  let WI := weighingIntegerModel W
  have hCast : WI.map (Int.castRingHom ℝ)=W := weighingIntegerModel_cast W _ hW
  have hIDiag (i : ι) : integerTwoBlock WI i i=0 := by
    ext a b
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M a b) (hDiag i)
    rw [← hCast] at hh
    change ((WI (a,i) (b,i) : ℤ) : ℝ)=0 at hh
    exact_mod_cast hh
  have hIOff (i j : ι) (hij : i≠j) : ∃ bits : Fin 2 → Fin 2 → Bool,integerTwoBlock WI i j=signTwoInt bits := by
    have hx (a b : Fin 2) : ∃ bit : Bool,W (a,i) (b,j)=if bit then -1 else 1 := by
      rcases hOff i j hij a b with h|h
      · exact ⟨false,h⟩
      · exact ⟨true,h⟩
    choose bits hbits using hx
    refine ⟨bits,?_⟩
    ext a b
    have hc := congrArg (fun M : Matrix (Fin 2×ι) (Fin 2×ι) ℝ => M (a,i) (b,j)) hCast
    change ((WI (a,i) (b,j) : ℤ) : ℝ)=W (a,i) (b,j) at hc
    rw [hbits] at hc
    cases hb : bits a b <;> simp only [hb,Bool.false_eq_true,ite_false,ite_true] at hc
    · change WI (a,i) (b,j)=(if bits a b then -1 else 1 : ℤ)
      rw [hb]
      exact_mod_cast hc
    · change WI (a,i) (b,j)=(if bits a b then -1 else 1 : ℤ)
      rw [hb]
      exact_mod_cast hc
  have hIGram : WI*WI.transpose=(2*(Fintype.card ι : ℤ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℤ) := by
    ext p q
    have hh := congrArg (fun M : Matrix (Fin 2×ι) (Fin 2×ι) ℝ => M p q) hW.2
    rw [← hCast] at hh
    simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.map_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] at hh ⊢
    change (∑ k,((WI p k : ℤ) : ℝ)*((WI q k : ℤ) : ℝ))=(2*(Fintype.card ι : ℝ)-2)*(if p=q then 1 else 0) at hh
    exact_mod_cast hh
  refine ⟨hDiag,?_,hW.2⟩
  intro i j hij
  obtain ⟨d,hd⟩ := paired_weighing_integer_block_factor hn WI hIDiag hIOff hIGram i j hij
  have hm := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (Int.castRingHom ℝ)) hd
  rw [integer_two_block_cast,hCast,Matrix.map_mul] at hm
  change twoBlock W i j=signedTwoReal d*walshTwoReal at hm
  exact ⟨hOff i j hij,hm ▸ signedTwo_walsh_real_gram d⟩


noncomputable def pairedWalshReal {ι : Type*} [DecidableEq ι] :
    Matrix (Fin 2×ι) (Fin 2×ι) ℝ := Matrix.blockDiagonal (fun _ : ι => walshTwoReal)

theorem pairedWalshReal_symmetric {ι : Type*} [DecidableEq ι] :
    (pairedWalshReal (ι := ι)).transpose=pairedWalshReal := by
  have hF : walshTwoReal.transpose=walshTwoReal := by
    change (walshTwoInt.map (Int.castRingHom ℝ)).transpose=walshTwoInt.map (Int.castRingHom ℝ)
    rw [← Matrix.transpose_map]
    congr 1
    decide +kernel
  simp only [pairedWalshReal,Matrix.blockDiagonal_transpose,hF]

theorem pairedWalshReal_gram {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (pairedWalshReal (ι := ι))*pairedWalshReal.transpose=(2 : ℝ) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) := by
  dsimp only [pairedWalshReal]
  rw [Matrix.blockDiagonal_transpose,← Matrix.blockDiagonal_mul]
  simp only [walshTwoReal_gram]
  change Matrix.blockDiagonal ((2 : ℝ) • (1 : ι → Matrix (Fin 2) (Fin 2) ℝ)) = _
  rw [Matrix.blockDiagonal_smul,Matrix.blockDiagonal_one]

theorem twoBlock_mul_pairedWalshReal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) (i j : ι) :
    twoBlock (W*pairedWalshReal) i j=twoBlock W i j*walshTwoReal := by
  ext a b
  simp [twoBlock,pairedWalshReal,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.blockDiagonal_apply,mul_ite,eq_comm]

theorem normalized_real_block_transform {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) (hW : IsNormalizedTwoZeroWeighing W) :
    let A := (1/2 : ℝ) • (W*pairedWalshReal)
    (∀ i,twoBlock A i i=0) ∧
    (∀ i j,i≠j → ∃ d : SignedTwoState,twoBlock A i j=signedTwoReal d) ∧
    A*A.transpose=((Fintype.card ι : ℝ)-1) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) := by
  dsimp only
  have hBlock (i j : ι) : twoBlock ((1/2 : ℝ) • (W*pairedWalshReal)) i j=(1/2 : ℝ) • (twoBlock W i j*walshTwoReal) := by
    have hh := twoBlock_mul_pairedWalshReal W i j
    exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => (1/2 : ℝ) • M) hh
  refine ⟨?_,?_,?_⟩
  · intro i;rw [hBlock,hW.1 i,Matrix.zero_mul,smul_zero]
  · intro i j hij
    obtain ⟨d,hd⟩ := sign_two_by_two_factor _ (hW.2.1 i j hij).1 (hW.2.1 i j hij).2
    refine ⟨d,?_⟩
    have hFF : walshTwoReal*walshTwoReal=(2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      have hSym : walshTwoReal.transpose=walshTwoReal := by
        change (walshTwoInt.map (Int.castRingHom ℝ)).transpose=walshTwoInt.map (Int.castRingHom ℝ)
        rw [← Matrix.transpose_map]
        congr 1
        decide +kernel
      simpa only [hSym] using walshTwoReal_gram
    rw [hBlock,hd,Matrix.mul_assoc,hFF,Matrix.mul_smul,Matrix.mul_one,smul_smul]
    norm_num
  · have hF : (pairedWalshReal (ι := ι))*pairedWalshReal=(2 : ℝ) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) := by
      simpa only [pairedWalshReal_symmetric] using (pairedWalshReal_gram (ι := ι))
    rw [Matrix.transpose_smul,Matrix.transpose_mul,pairedWalshReal_symmetric,
      Matrix.smul_mul,Matrix.mul_smul,smul_smul]
    have hMul : (W*pairedWalshReal)*(pairedWalshReal*W.transpose)=
        (2 : ℝ) • (W*W.transpose) := by
      calc
        _=(W*(pairedWalshReal*pairedWalshReal))*W.transpose := by simp only [Matrix.mul_assoc]
        _=_ := by rw [hF,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul]
    rw [hMul,hW.2.2]
    simp only [smul_smul]
    congr 1
    all_goals try simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
    all_goals ring


theorem forced_two_zero_block_structure {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix ι ι ℝ) (hW : IsWeighing W ((Fintype.card ι : ℝ)-2))
    (hn : 4∣Fintype.card ι) (hnpos : 0<Fintype.card ι) :
    ∃ r c : (Fin 2×ZeroBlockIndex W) ≃ ι,
      let V := W.submatrix r c
      let A := (1/2 : ℝ) • (V*pairedWalshReal)
      IsNormalizedTwoZeroWeighing V ∧
      (∀ a b : Fin 2,∀ i j : ZeroBlockIndex W,V (a,i) (b,j)=0 ↔ i=j) ∧
      2*Fintype.card (ZeroBlockIndex W)=Fintype.card ι ∧
      (∀ i,twoBlock A i i=0) ∧
      (∀ i j,i≠j → ∃ d : SignedTwoState,twoBlock A i j=signedTwoReal d) ∧
      A*A.transpose=((Fintype.card (ZeroBlockIndex W) : ℝ)-1) •
        (1 : Matrix (Fin 2×ZeroBlockIndex W) (Fin 2×ZeroBlockIndex W) ℝ) := by
  classical
  have hn4 : 4≤Fintype.card ι := by
    obtain ⟨k,hk⟩ := hn
    omega
  have hEven : Even (Fintype.card ι) := by
    obtain ⟨k,hk⟩ := hn
    exact ⟨2*k,by omega⟩
  obtain ⟨r,c,hPV,hDiag,hOff,hCard⟩ := weighing_paired_block_form W hW hEven (by omega)
  have hEvenBlocks : Even (Fintype.card (ZeroBlockIndex W)) := by
    obtain ⟨k,hk⟩ := hn
    exact ⟨k,by omega⟩
  have hPV' : IsWeighing (W.submatrix r c) ((Fintype.card (Fin 2×ZeroBlockIndex W) : ℝ)-2) := by
    have hc := Fintype.card_congr r
    simpa only [hc] using hPV
  have hNorm := paired_real_weighing_normalized hEvenBlocks _ hPV' hDiag hOff
  have hTransform := normalized_real_block_transform _ hNorm
  refine ⟨r,c,hNorm,?_,hCard,hTransform⟩
  intro a b i j
  by_cases hij : i=j
  · subst j
    have hz := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M a b) (hDiag i)
    exact ⟨fun _ => rfl,fun _ => hz⟩
  · constructor
    · intro hz
      have hs := hOff i j hij a b
      change IsSign ((W.submatrix r c) (a,i) (b,j)) at hs
      rw [hz] at hs
      rcases hs with hs|hs <;> norm_num at hs
    · exact fun h => False.elim (hij h)


end CompletionTheory
