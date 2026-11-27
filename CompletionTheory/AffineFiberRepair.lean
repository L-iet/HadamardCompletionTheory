/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.OddBlockBudget
public import CompletionTheory.TensorExchange
@[expose] public section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace CompletionTheory
open Matrix

def ternaryRepairCode (i : Fin 9) (j : Fin 4) : ℕ :=
  ![i.val%3,i.val/3,(i.val%3+i.val/3)%3,(i.val%3+3-i.val/3)%3] j

def affineRepairInt : Matrix (Fin 9) (Fin 4×Fin 3) ℤ :=
  fun i j => if j.2.val=ternaryRepairCode i j.1 then -1 else 1

def repeatedFourInt : Matrix (Fin 4) (Fin 4×Fin 3) ℤ :=
  fun i j => (!![1,1,1,1;1,-1,1,-1;1,1,-1,-1;1,-1,-1,1] : Matrix (Fin 4) (Fin 4) ℤ) i j.1

theorem affineRepairInt_gram : affineRepairInt*affineRepairInt.transpose=
    (12 : ℤ) • (1 : Matrix (Fin 9) (Fin 9) ℤ) := by decide +kernel

theorem affineRepairInt_cross : ∀ i : Fin 4,i≠0 → ∀ a : Fin 9,
    (∑ j : Fin 4×Fin 3,repeatedFourInt i j*affineRepairInt a j)=0 := by decide +kernel

noncomputable def affineRepair : Matrix (Fin 9) (Fin 4×Fin 3) ℝ :=
  fun i j => (affineRepairInt i j : ℝ)

theorem affineRepair_sign (i : Fin 9) (j : Fin 4×Fin 3) : IsSign (affineRepair i j) := by
  unfold affineRepair affineRepairInt
  split_ifs <;> simp [IsSign]

theorem repeatedFourInt_cast (i : Fin 4) (j : Fin 4×Fin 3) :
    (repeatedFourInt i j : ℝ)=seedFour i j.1 := by
  rcases j with ⟨j,k⟩
  fin_cases i <;> fin_cases j <;> norm_num [repeatedFourInt,seedFour]

theorem affineRepair_partialHadamard : IsPartialHadamard affineRepair := by
  constructor
  · exact affineRepair_sign
  · ext i j
    have hh := congrFun (congrFun affineRepairInt_gram i) j
    simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply] at hh ⊢
    change (∑ k : Fin 4×Fin 3,(affineRepairInt i k : ℝ)*(affineRepairInt j k : ℝ))=_
    norm_num only [Fintype.card_prod,Fintype.card_fin] at *
    exact_mod_cast hh

theorem affineRepair_cross : ∀ i : Fin 4,i≠0 → ∀ a : Fin 9,
    (∑ j : Fin 4×Fin 3,seedFour i j.1*affineRepair a j)=0 := by
  intro i hi a
  have hh := affineRepairInt_cross i hi a
  have hc := congrArg (fun z : ℤ => (z : ℝ)) hh
  simpa only [Int.cast_sum,Int.cast_mul,Int.cast_zero,repeatedFourInt_cast,affineRepair] using hc

theorem partialHadamard_row_dot {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {M : Matrix ι κ ℝ} (hM : IsPartialHadamard M) (i j : ι) :
    (∑ k,M i k*M j k)=if i=j then (Fintype.card κ : ℝ) else 0 := by
  have hh := congrArg (fun A => A i j) hM.2
  simpa [Matrix.mul_apply,Matrix.transpose_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply] using hh

theorem partialHadamard_of_row_dots {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (M : Matrix ι κ ℝ) (hSign : ∀ i j,IsSign (M i j))
    (hdot : ∀ i j,(∑ k,M i k*M j k)=if i=j then (Fintype.card κ : ℝ) else 0) :
    IsPartialHadamard M := by
  refine ⟨hSign,?_⟩
  ext i j
  simpa [Matrix.mul_apply,Matrix.transpose_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply] using hdot i j

theorem partialHadamard_restrict_rows {ι β κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β] [Fintype κ]
    {M : Matrix ι κ ℝ} (hM : IsPartialHadamard M) (f : β ↪ ι) :
    IsPartialHadamard (fun i j => M (f i) j) := by
  apply partialHadamard_of_row_dots
  · exact fun i j => hM.1 (f i) j
  · intro i j
    simpa only [f.injective.eq_iff] using partialHadamard_row_dot hM (f i) (f j)

theorem retainAndInsert_partialHadamard {ι κ γ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype γ] [DecidableEq γ]
    (P : Matrix ι κ ℝ) (Q : Matrix γ κ ℝ) (S : Finset ι)
    (hP : IsPartialHadamard P) (hQ : IsPartialHadamard Q)
    (hcross : ∀ i∈S,∀ a,(∑ j,P i j*Q a j)=0) :
    IsPartialHadamard (retainAndInsert P Q S) := by
  apply partialHadamard_of_row_dots
  · intro i j
    cases i with
    | inl i => exact hP.1 i.val j
    | inr a => exact hQ.1 a j
  · intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        by_cases heq : i=j
        · subst j
          simpa [retainAndInsert] using partialHadamard_row_dot hP i.val i.val
        · have hv : i.val≠j.val := fun h => heq (Subtype.ext h)
          simpa [retainAndInsert,heq,hv] using partialHadamard_row_dot hP i.val j.val
      | inr a => simpa [retainAndInsert] using hcross i.val i.property a
    | inr a =>
      cases j with
      | inl i => simpa [retainAndInsert,mul_comm] using hcross i.val i.property a
      | inr b => simpa [retainAndInsert] using partialHadamard_row_dot hQ a b

def fiberColumnEquiv (τ : Type*) : ((Fin 4×τ)×Fin 3) ≃ ((Fin 4×Fin 3)×τ) where
  toFun := fun j => ((j.1.1,j.2),j.1.2)
  invFun := fun j => ((j.1.1,j.2),j.1.2)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

theorem fiber_row_dot {τ : Type*} [Fintype τ]
    (u v : Fin 4×Fin 3 → ℝ) (h g : τ → ℝ) :
    (∑ j : ((Fin 4×τ)×Fin 3),(u (j.1.1,j.2)*h j.1.2)*(v (j.1.1,j.2)*g j.1.2))=
      (∑ j,u j*v j)*∑ a,h a*g a := by
  calc
    _=∑ j : ((Fin 4×Fin 3)×τ),(u j.1*h j.2)*(v j.1*g j.2) :=
      Fintype.sum_equiv (fiberColumnEquiv τ) _ _ (fun _ => rfl)
    _=_ := tensor_row_dot u v h g

noncomputable def repeatedTensorSeed {τ : Type*} (T : Matrix τ τ ℝ) :
    Matrix (Fin 4×τ) ((Fin 4×τ)×Fin 3) ℝ :=
  fun i j => seedFour i.1 j.1.1*T i.2 j.1.2

noncomputable def insertedFiberRows {τ : Type*} (T : Matrix τ τ ℝ) (F : Finset τ) :
    Matrix (Fin 9×F) ((Fin 4×τ)×Fin 3) ℝ :=
  fun a j => affineRepair a.1 (j.1.1,j.2)*T a.2.val j.1.2

def fiberDeletedRows {τ : Type*} (F : Finset τ) : Finset (Fin 4×τ) :=
  ({0} : Finset (Fin 4)).product F

theorem fiberDeletedRows_card {τ : Type*} (F : Finset τ) : (fiberDeletedRows F).card=F.card := by
  simp [fiberDeletedRows]

theorem repeatedTensorSeed_partialHadamard {τ : Type*} [Fintype τ] [DecidableEq τ]
    (T : Matrix τ τ ℝ) (hT : IsHadamard T) : IsPartialHadamard (repeatedTensorSeed T) :=
  repetition_partialHadamard (κ := Fin 3) (tensorFrame seedFour T)
    (tensorFrame_partialHadamard seedFour T seedFour_hadamard hT)

theorem insertedFiberRows_partialHadamard {τ : Type*} [Fintype τ] [DecidableEq τ]
    (T : Matrix τ τ ℝ) (hT : IsHadamard T) (F : Finset τ) :
    IsPartialHadamard (insertedFiberRows T F) := by
  apply partialHadamard_of_row_dots
  · intro a j
    rcases affineRepair_sign a.1 (j.1.1,j.2) with ha|ha <;>
      rcases hT.1 a.2.val j.1.2 with ht|ht <;> simp [insertedFiberRows,ha,ht,IsSign]
  · intro a b
    change (∑ j : ((Fin 4×τ)×Fin 3),
      (affineRepair a.1 (j.1.1,j.2)*T a.2.val j.1.2)*
      (affineRepair b.1 (j.1.1,j.2)*T b.2.val j.1.2))=_
    rw [fiber_row_dot,partialHadamard_row_dot affineRepair_partialHadamard,
      partialHadamard_row_dot hT]
    by_cases ha : a.1=b.1 <;> by_cases ht : a.2=b.2 <;>
      simp [Prod.ext_iff,ha,ht,Subtype.ext_iff,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul] <;> ring

theorem insertedFiberRows_cross {τ : Type*} [Fintype τ] [DecidableEq τ]
    (T : Matrix τ τ ℝ) (hT : IsHadamard T) (F : Finset τ)
    (i : Fin 4×τ) (hi : i∉fiberDeletedRows F) (a : Fin 9×F) :
    (∑ j,repeatedTensorSeed T i j*insertedFiberRows T F a j)=0 := by
  change (∑ j : ((Fin 4×τ)×Fin 3),
    (seedFour i.1 j.1.1*T i.2 j.1.2)*
    (affineRepair a.1 (j.1.1,j.2)*T a.2.val j.1.2))=0
  rw [fiber_row_dot (fun j => seedFour i.1 j.1) (affineRepair a.1) (T i.2) (T a.2.val)]
  by_cases hi0 : i.1=0
  · have hne : i.2≠a.2.val := by
      intro heq
      apply hi
      change i∈({0} : Finset (Fin 4)).product F
      exact Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr hi0,heq ▸ a.2.property⟩
    rw [partialHadamard_row_dot hT,if_neg hne,mul_zero]
  · rw [affineRepair_cross i.1 hi0 a.1,zero_mul]

theorem repaired_fiber_frame_partialHadamard {τ : Type*} [Fintype τ] [DecidableEq τ]
    (T : Matrix τ τ ℝ) (hT : IsHadamard T) (F : Finset τ) :
    IsPartialHadamard (retainAndInsert (repeatedTensorSeed T) (insertedFiberRows T F) (fiberDeletedRows F)ᶜ) := by
  apply retainAndInsert_partialHadamard _ _ _ (repeatedTensorSeed_partialHadamard T hT)
    (insertedFiberRows_partialHadamard T hT F)
  intro i hi a
  exact insertedFiberRows_cross T hT F i (Finset.mem_compl.mp hi) a

theorem sign_single_row_partialHadamard {κ : Type*} [Fintype κ] (x : κ → ℝ)
    (hx : ∀ j,IsSign (x j)) : IsPartialHadamard (fun (_ : Unit) j => x j) := by
  apply partialHadamard_of_row_dots
  · exact fun _ j => hx j
  · intro i j
    have hij : i=j := Subsingleton.elim _ _
    rw [if_pos hij]
    calc
      (∑ k,x k*x k)=∑ _ : κ,(1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        simpa only [pow_two] using isSign_sq (hx k)
      _=_ := by simp

theorem repaired_fiber_frame_terminal {τ : Type*} [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (T : Matrix τ τ ℝ) (hT : IsHadamard T) (F : Finset τ) :
    NoSignExtension (retainAndInsert (repeatedTensorSeed T) (insertedFiberRows T F) (fiberDeletedRows F)ᶜ) := by
  classical
  let P := repeatedTensorSeed T
  let Q := insertedFiberRows T F
  let S := (fiberDeletedRows F)ᶜ
  rintro ⟨x,hx,horth⟩
  let X : Matrix Unit ((Fin 4×τ)×Fin 3) ℝ := fun _ j => x j
  let Qplus := retainAndInsert Q X Finset.univ
  have hQ : IsPartialHadamard Q := insertedFiberRows_partialHadamard T hT F
  have hX : IsPartialHadamard X := sign_single_row_partialHadamard x hx
  have hQplus : IsPartialHadamard Qplus := by
    apply retainAndInsert_partialHadamard Q X Finset.univ hQ hX
    intro a ha b
    exact horth (Sum.inr a)
  have hP : IsPartialHadamard P := repeatedTensorSeed_partialHadamard T hT
  have hAll : IsPartialHadamard (retainAndInsert P Qplus S) := by
    apply retainAndInsert_partialHadamard P Qplus S hP hQplus
    intro i hi a
    cases a with
    | inl a => exact insertedFiberRows_cross T hT F i (Finset.mem_compl.mp hi) a.val
    | inr a => exact horth (Sum.inl ⟨i,hi⟩)
  have hK : IsHadamard (tensorFrame seedFour T) :=
    tensorFrame_partialHadamard seedFour T seedFour_hadamard hT
  have hb := (odd_block_exchange_budget (ι := Fin 4×τ) (κ := Fin 3) (by decide) (by decide)
    (tensorFrame seedFour T) hK Qplus S hAll).1
  have hComp : Sᶜ=fiberDeletedRows F := by
    ext i
    simp only [S,Finset.mem_compl,not_not]
  rw [hComp,fiberDeletedRows_card] at hb
  simp only [Fintype.card_sum,Fintype.card_coe,
    Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_unique,Nat.cast_add,Nat.cast_mul,Nat.cast_one] at hb
  norm_num at hb
  linarith

theorem repeatedTensorSeed_terminal {τ : Type*} [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (T : Matrix τ τ ℝ) (hT : IsHadamard T) : NoSignExtension (repeatedTensorSeed T) :=
  odd_repetition_unextendible (κ := Fin 3) (by decide) (tensorFrame seedFour T)
    (tensorFrame_partialHadamard seedFour T seedFour_hadamard hT)

theorem repeatedTensorSeed_one_row_augmentation {τ : Type*} [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (T : Matrix τ τ ℝ) (hT : IsHadamard T) : HasAugmentingExchange (repeatedTensorSeed T) 1 := by
  classical
  let t₀ : τ := Classical.choice inferInstance
  let F : Finset τ := {t₀}
  let f : Fin 2 ↪ Fin 9×F := {
    toFun := fun i => (⟨i.val,by omega⟩,⟨t₀,Finset.mem_singleton_self _⟩)
    inj' := fun i j h => Fin.ext (congrArg (fun a : Fin 9×F => a.1.val) h) }
  let V : Matrix (Fin 2) ((Fin 4×τ)×Fin 3) ℝ := fun i j => insertedFiberRows T F (f i) j
  refine ⟨fiberDeletedRows F,?_,V,?_,?_⟩
  · rw [fiberDeletedRows_card];simp [F]
  · exact partialHadamard_restrict_rows (insertedFiberRows_partialHadamard T hT F) f
  · intro i hi a
    exact insertedFiberRows_cross T hT F i hi (f a)

theorem no_zero_augmentation_of_terminal {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (P : Matrix ι κ ℝ) (hNo : NoSignExtension P) : ¬HasAugmentingExchange P 0 := by
  rintro ⟨D,hD,V,hV,hcross⟩
  have hDE : D=∅ := Finset.card_eq_zero.mp hD
  apply hNo
  refine ⟨V 0,hV.1 0,?_⟩
  intro i
  exact hcross i (by simp [hDE]) 0

theorem repeatedTensorSeed_exchangeCost {τ : Type*} [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (T : Matrix τ τ ℝ) (hT : IsHadamard T) : exchangeCost (repeatedTensorSeed T)=(1 : WithTop ℕ) := by
  classical
  let P := repeatedTensorSeed T
  have hOne : HasAugmentingExchange P 1 := repeatedTensorSeed_one_row_augmentation T hT
  have hZero : ¬HasAugmentingExchange P 0 := no_zero_augmentation_of_terminal P (repeatedTensorSeed_terminal T hT)
  have hex : ∃ k,HasAugmentingExchange P k := ⟨1,hOne⟩
  rw [exchangeCost_eq_minimum P hex]
  have hmin : Nat.find hex=1 := by
    have hle := Nat.find_min' hex hOne
    have hne : Nat.find hex≠0 := by intro h;exact hZero (h ▸ Nat.find_spec hex)
    omega
  rw [hmin]
  norm_num

def HasRetainedHadamardCompletion {ι κ : Type*} [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (P : Matrix ι κ ℝ) (S : Finset ι) : Prop :=
  ∃ H : Matrix κ κ ℝ,Matrix.IsHadamard H ∧ ∃ e : S ↪ κ,∀ i j,H (e i) j=P i.val j

theorem mathlib_hadamard_partial {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℝ} (hH : Matrix.IsHadamard H) : IsPartialHadamard H := by
  refine ⟨fun i j => Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hH.apply_mem i j),?_⟩
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hH.mul_conjTranspose

theorem repeatedTensorSeed_completion_lower_bound {τ : Type*} [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (T : Matrix τ τ ℝ) (hT : IsHadamard T) (S : Finset (Fin 4×τ))
    (hComp : HasRetainedHadamardCompletion (repeatedTensorSeed T) S) :
    Fintype.card τ≤Sᶜ.card := by
  classical
  obtain ⟨H,hH,e,hret⟩ := hComp
  let γ := {j : ((Fin 4×τ)×Fin 3) // j∉Set.range e}
  let Q : Matrix γ ((Fin 4×τ)×Fin 3) ℝ := fun i j => H i.val j
  let f : S⊕γ ↪ ((Fin 4×τ)×Fin 3) := {
    toFun := Sum.elim e (fun j => j.val)
    inj' := by
      intro i j hij
      cases i with
      | inl i =>
        cases j with
        | inl j => exact congrArg Sum.inl (e.injective hij)
        | inr j => exact False.elim (j.property ⟨i,hij⟩)
      | inr i =>
        cases j with
        | inl j => exact False.elim (i.property ⟨j,hij.symm⟩)
        | inr j => exact congrArg Sum.inr (Subtype.ext hij) }
  have hfSurj : Function.Surjective f := by
    intro j
    by_cases hj : j∈Set.range e
    · obtain ⟨i,rfl⟩ := hj
      exact ⟨Sum.inl i,rfl⟩
    · exact ⟨Sum.inr ⟨j,hj⟩,rfl⟩
  have hcard : S.card+Fintype.card γ=Fintype.card ((Fin 4×τ)×Fin 3) := by
    have hc := Fintype.card_congr (Equiv.ofBijective f ⟨f.injective,hfSurj⟩)
    simpa only [Fintype.card_sum,Fintype.card_coe] using hc
  have hR := partialHadamard_restrict_rows (mathlib_hadamard_partial hH) f
  have hEq : retainAndInsert (repeatedTensorSeed T) Q S=(fun i j => H (f i) j) := by
    funext i j
    cases i with
    | inl i => exact (hret i j).symm
    | inr i => rfl
  rw [← hEq] at hR
  have hK : IsHadamard (tensorFrame seedFour T) :=
    tensorFrame_partialHadamard seedFour T seedFour_hadamard hT
  have hb := (odd_block_exchange_budget (ι := Fin 4×τ) (κ := Fin 3) (by decide) (by decide)
    (tensorFrame seedFour T) hK Q S hR).2 (by simpa only [Fintype.card_prod] using hcard)
  have hRatio : ((Fintype.card (Fin 4×τ) : ℝ)/((Fintype.card (Fin 3) : ℝ)+1))=(Fintype.card τ : ℝ) := by
    norm_num [Fintype.card_prod] <;> ring
  simpa only [hRatio,Nat.ceil_natCast] using hb

theorem repeatedTensorSeed_full_completion_attained {τ : Type*} [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (T : Matrix τ τ ℝ) (hT : IsHadamard T) :
    ∃ S : Finset (Fin 4×τ),Sᶜ.card=Fintype.card τ ∧
      HasRetainedHadamardCompletion (repeatedTensorSeed T) S := by
  classical
  let F : Finset τ := Finset.univ
  let D := fiberDeletedRows F
  let S := Dᶜ
  let R := retainAndInsert (repeatedTensorSeed T) (insertedFiberRows T F) S
  have hR : IsPartialHadamard R := repaired_fiber_frame_partialHadamard T hT F
  have hD : D.card=Fintype.card τ := by simp only [D,F,fiberDeletedRows_card,Finset.card_univ]
  have hSplit : D.card+S.card=4*Fintype.card τ := by
    have hc := Finset.card_add_card_compl D
    simpa only [S,Fintype.card_prod,Fintype.card_fin] using hc
  have hF : F.card=Fintype.card τ := by simp [F]
  have hcR : Fintype.card (↥S ⊕ (Fin 9×F))=Fintype.card ((Fin 4×τ)×Fin 3) := by
    simp only [Fintype.card_sum,Fintype.card_coe,Fintype.card_prod,Fintype.card_fin]
    rw [hF]
    omega
  let e : (↥S ⊕ (Fin 9×F)) ≃ ((Fin 4×τ)×Fin 3) := Fintype.equivOfCardEq hcR
  let H : Matrix ((Fin 4×τ)×Fin 3) ((Fin 4×τ)×Fin 3) ℝ := fun i j => R (e.symm i) j
  have hH : IsHadamard H := partialHadamard_restrict_rows hR e.symm.toEmbedding
  let eOld : S ↪ ((Fin 4×τ)×Fin 3) := {
    toFun := fun i => e (Sum.inl i)
    inj' := fun _ _ h => Sum.inl_injective (e.injective h) }
  refine ⟨S,?_,H,isHadamard_mathlib hH,eOld,?_⟩
  · have hComp : Sᶜ=D := by ext i;simp only [S,Finset.mem_compl,not_not]
    rw [hComp,hD]
  · intro i j
    change R (e.symm (e (Sum.inl i))) j=repeatedTensorSeed T i.val j
    rw [e.symm_apply_apply]
    rfl

theorem cheap_augmentation_exact_completion_cost {τ : Type*} [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (T : Matrix τ τ ℝ) (hT : IsHadamard T) :
    IsPartialHadamard (repeatedTensorSeed T) ∧ NoSignExtension (repeatedTensorSeed T) ∧
    exchangeCost (repeatedTensorSeed T)=(1 : WithTop ℕ) ∧
    (∀ S : Finset (Fin 4×τ),HasRetainedHadamardCompletion (repeatedTensorSeed T) S → Fintype.card τ≤Sᶜ.card) ∧
    (∃ S : Finset (Fin 4×τ),Sᶜ.card=Fintype.card τ ∧ HasRetainedHadamardCompletion (repeatedTensorSeed T) S) ∧
    ∀ k : ℕ,k≤Fintype.card τ → ∃ F : Finset τ,F.card=k ∧
      (fiberDeletedRows F).card=k ∧ Fintype.card (Fin 9×F)=9*k ∧
      Fintype.card (↥((fiberDeletedRows F)ᶜ) ⊕ (Fin 9×F))=4*Fintype.card τ+8*k ∧
      IsPartialHadamard (retainAndInsert (repeatedTensorSeed T) (insertedFiberRows T F) (fiberDeletedRows F)ᶜ) ∧
      NoSignExtension (retainAndInsert (repeatedTensorSeed T) (insertedFiberRows T F) (fiberDeletedRows F)ᶜ) := by
  classical
  refine ⟨repeatedTensorSeed_partialHadamard T hT,repeatedTensorSeed_terminal T hT,
    repeatedTensorSeed_exchangeCost T hT,fun S h => repeatedTensorSeed_completion_lower_bound T hT S h,
    repeatedTensorSeed_full_completion_attained T hT,?_⟩
  intro k hk
  obtain ⟨F,hF,hcard⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset τ))
    (by simpa only [Finset.card_univ] using hk)
  refine ⟨F,hcard,?_,?_,?_,repaired_fiber_frame_partialHadamard T hT F,repaired_fiber_frame_terminal T hT F⟩
  · rw [fiberDeletedRows_card,hcard]
  · simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_coe,hcard]
  · have hs := Finset.card_add_card_compl (fiberDeletedRows F)
    rw [fiberDeletedRows_card,hcard] at hs
    simp only [Fintype.card_prod,Fintype.card_fin] at hs
    simp only [Fintype.card_sum,Fintype.card_coe,Fintype.card_prod,Fintype.card_fin,hcard]
    omega

end CompletionTheory
