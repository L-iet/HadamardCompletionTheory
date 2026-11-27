/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.RealificationGate
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic
@[expose] public section
namespace CompletionTheory
noncomputable section

def fourthAlphabet (a : Fin 4) : ℂ := ![1,-1,Complex.I,-Complex.I] a

theorem fourthAlphabet_root (a : Fin 4) : IsFourthRoot (fourthAlphabet a) := by
  fin_cases a <;> simp [fourthAlphabet,IsFourthRoot]

theorem fourthAlphabet_surjective (z : ℂ) (hz : IsFourthRoot z) :
    ∃ a : Fin 4, fourthAlphabet a=z := by
  rcases hz with h|h|h|h
  · exact ⟨0,by simpa [fourthAlphabet] using h.symm⟩
  · exact ⟨1,by simpa [fourthAlphabet] using h.symm⟩
  · exact ⟨2,by simpa [fourthAlphabet] using h.symm⟩
  · exact ⟨3,by simpa [fourthAlphabet] using h.symm⟩

noncomputable def normalizedFourthCandidates {ι : Type*} [Fintype ι]
    {V : Submodule ℂ (ι → ℂ)} {I : Finset ι}
    (e : V ≃ₗ[ℂ] (I → ℂ)) (j : I) : Finset V := by
  classical
  exact (Finset.univ.image (fun b : {k : I // k≠j} → Fin 4 =>
    e.symm (fun k => if h : k=j then 1 else fourthAlphabet (b ⟨k,h⟩)))).filter
    (fun v => ∀ i, IsFourthRoot (v.val i))

theorem normalizedFourthCandidates_exact {ι : Type*} [Fintype ι]
    {V : Submodule ℂ (ι → ℂ)} {I : Finset ι}
    (e : V ≃ₗ[ℂ] (I → ℂ)) (he : ∀ v j,e v j=v.val j.val)
    (j : I) (v : V) :
    v ∈ normalizedFourthCandidates e j ↔
      (∀ i,IsFourthRoot (v.val i)) ∧ v.val j.val=1 := by
  classical
  constructor
  · intro hv
    obtain ⟨hm,hr⟩ := Finset.mem_filter.mp hv
    obtain ⟨b,_,hb⟩ := Finset.mem_image.mp hm
    refine ⟨hr,?_⟩
    have hh := congrArg (fun u : V => e u j) hb
    rw [e.apply_symm_apply] at hh
    simpa only [dite_true,he] using hh.symm
  · rintro ⟨hr,hj⟩
    have hchoose : ∀ k : {k : I // k≠j},∃ a : Fin 4,fourthAlphabet a=v.val k.val.val :=
      fun k => fourthAlphabet_surjective _ (hr _)
    choose b hb using hchoose
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨b,Finset.mem_univ _,?_⟩,hr⟩
    apply e.injective
    rw [e.apply_symm_apply]
    funext k
    rw [he]
    split_ifs with hk
    · subst k; exact hj.symm
    · exact hb ⟨k,hk⟩

theorem normalizedFourthCandidates_card_bound {ι : Type*} [Fintype ι]
    {V : Submodule ℂ (ι → ℂ)} {I : Finset ι}
    (e : V ≃ₗ[ℂ] (I → ℂ)) (j : I) :
    (normalizedFourthCandidates e j).card ≤ 4 ^ (I.card-1) := by
  classical
  have hc : Fintype.card {k : I // k≠j}=I.card-1 := by
    simp [Fintype.card_subtype_compl]
  exact (Finset.card_filter_le _ _).trans
    (Finset.card_image_le.trans (by simp [hc]))

theorem fourthRoot_star_self {z : ℂ} (hz : IsFourthRoot z) : star z*z=1 := by
  rcases hz with rfl|rfl|rfl|rfl <;> norm_num

theorem fourthRoot_star_mul {z w : ℂ} (hz : IsFourthRoot z) (hw : IsFourthRoot w) :
    IsFourthRoot (star z*w) := by
  rcases hz with rfl|rfl|rfl|rfl <;>
    rcases hw with rfl|rfl|rfl|rfl <;> norm_num [IsFourthRoot]

theorem normalizedFourthCandidates_nonempty_iff {ι : Type*} [Fintype ι]
    {V : Submodule ℂ (ι → ℂ)} {I : Finset ι}
    (e : V ≃ₗ[ℂ] (I → ℂ)) (he : ∀ v j,e v j=v.val j.val) (j : I) :
    (normalizedFourthCandidates e j).Nonempty ↔
      ∃ v : V,∀ i,IsFourthRoot (v.val i) := by
  classical
  constructor
  · rintro ⟨v,hv⟩
    exact ⟨v,((normalizedFourthCandidates_exact e he j v).mp hv).1⟩
  · rintro ⟨v,hv⟩
    let u : V := star (v.val j.val) • v
    refine ⟨u,(normalizedFourthCandidates_exact e he j u).mpr ⟨?_,?_⟩⟩
    · intro i
      exact fourthRoot_star_mul (hv j.val) (hv i)
    · exact fourthRoot_star_self (hv j.val)


theorem complex_partial_kernel_dimension {n m : ℕ} (hn : 0<n)
    (V : Matrix (Fin n) (Fin m) ℂ)
    (hgram : V.conjTranspose*V=(n : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) :
    Module.finrank ℂ (LinearMap.ker V.conjTranspose.mulVecLin)=n-m := by
  have hnz : (n : ℂ)≠0 := by exact_mod_cast hn.ne'
  let M : Matrix (Fin n) (Fin m) ℂ := (n : ℂ)⁻¹ • V
  have hPM : V.conjTranspose*M=1 := by
    simp only [M,Matrix.mul_smul,hgram,smul_smul,inv_mul_cancel₀ hnz,one_smul]
  have hsurj : Function.Surjective V.conjTranspose.mulVecLin := by
    intro y
    refine ⟨M.mulVec y,?_⟩
    change V.conjTranspose.mulVec (M.mulVec y)=y
    rw [Matrix.mulVec_mulVec,hPM,Matrix.one_mulVec]
  have hd := V.conjTranspose.mulVecLin.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj] at hd
  simp at hd
  omega

theorem bounded_quaternary_extension_test {n m : ℕ} (hm : m<n)
    (V : Matrix (Fin n) (Fin m) ℂ)
    (hgram : V.conjTranspose*V=(n : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) :
    ∃ C : Finset (LinearMap.ker V.conjTranspose.mulVecLin),
      C.card ≤ 4^(n-m-1) ∧
      (∀ v∈C,∀ i,IsFourthRoot (v.val i)) ∧
      (C.Nonempty ↔ ∃ z : Fin n → ℂ,
        (∀ i,IsFourthRoot (z i)) ∧ V.conjTranspose.mulVec z=0) := by
  classical
  let W := LinearMap.ker V.conjTranspose.mulVecLin
  obtain ⟨I,hI,e,he⟩ := exists_information_equivalence W
  have hd : Module.finrank ℂ W=n-m :=
    complex_partial_kernel_dimension (by omega) V hgram
  have hpos : 0<I.card := by omega
  obtain ⟨j,hj⟩ := Finset.card_pos.mp hpos
  let j' : I := ⟨j,hj⟩
  refine ⟨normalizedFourthCandidates e j',?_,?_,?_⟩
  · simpa [hI,hd] using normalizedFourthCandidates_card_bound e j'
  · intro v hv
    exact ((normalizedFourthCandidates_exact e he j' v).mp hv).1
  · rw [normalizedFourthCandidates_nonempty_iff e he j']
    constructor
    · rintro ⟨v,hv⟩
      exact ⟨v.val,hv,v.property⟩
    · rintro ⟨z,hz,hker⟩
      exact ⟨⟨z,hker⟩,hz⟩


def appendFourthColumn {n m : ℕ} (V : Matrix (Fin n) (Fin m) ℂ)
    (z : Fin n → ℂ) : Matrix (Fin n) (Fin (m+1)) ℂ :=
  fun i => Fin.snoc (V i) (z i)

theorem appendFourthColumn_roots {n m : ℕ} (V : Matrix (Fin n) (Fin m) ℂ)
    (z : Fin n → ℂ) (hV : ∀ i j,IsFourthRoot (V i j))
    (hz : ∀ i,IsFourthRoot (z i)) : ∀ i j,IsFourthRoot (appendFourthColumn V z i j) := by
  intro i j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simpa [appendFourthColumn] using hz i
  · simpa [appendFourthColumn] using hV i k

theorem appendFourthColumn_gram {n m : ℕ} (V : Matrix (Fin n) (Fin m) ℂ)
    (z : Fin n → ℂ) (hz : ∀ i,IsFourthRoot (z i))
    (hgram : V.conjTranspose*V=(n : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ))
    (horth : V.conjTranspose.mulVec z=0) :
    (appendFourthColumn V z).conjTranspose*(appendFourthColumn V z)=
      (n : ℂ) • (1 : Matrix (Fin (m+1)) (Fin (m+1)) ℂ) := by
  have hnew : (∑ i,star (z i)*z i)=(n : ℂ) := by
    simp_rw [fourthRoot_star_self (hz _)]
    simp
  have hcross (j : Fin m) : (∑ i,star (V i j)*z i)=0 := by
    simpa [Matrix.mulVec,dotProduct,Matrix.conjTranspose_apply] using congrFun horth j
  have hreverse (j : Fin m) : (∑ i,star (z i)*V i j)=0 := by
    have hh := congrArg star (hcross j)
    simpa [star_sum,star_mul,mul_comm] using hh
  ext a b
  refine Fin.lastCases ?_ (fun j => ?_) a
  · refine Fin.lastCases ?_ (fun k => ?_) b
    · simpa [Matrix.mul_apply,Matrix.conjTranspose_apply,appendFourthColumn,Matrix.one_apply] using hnew
    · simpa [Matrix.mul_apply,Matrix.conjTranspose_apply,appendFourthColumn,Matrix.one_apply,Ne.symm (Fin.castSucc_ne_last k)] using hreverse k
  · refine Fin.lastCases ?_ (fun k => ?_) b
    · simpa [Matrix.mul_apply,Matrix.conjTranspose_apply,appendFourthColumn,Matrix.one_apply] using hcross j
    · simpa [Matrix.mul_apply,Matrix.conjTranspose_apply,appendFourthColumn,Matrix.one_apply] using
        congrFun (congrFun hgram j) k


/-- The explicitly assumed classical real small-codimension extension input.
This is a proposition parameter, not an axiom or an asserted formalization of
Hall--Verheiden's real completion theorem. -/
def RealSmallDefectExtension : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℝ),
    4 ∣ Fintype.card ι → Fintype.card κ < Fintype.card ι →
    Fintype.card ι-Fintype.card κ ≤ 7 →
    (∀ i j,A i j=1 ∨ A i j= -1) →
    A.transpose*A=(Fintype.card ι : ℝ) • (1 : Matrix κ κ ℝ) →
    ∃ w : ι → ℝ,IsCubeVector w ∧ A.transpose.mulVec w=0

theorem small_defect_quaternary_extension (hClassical : RealSmallDefectExtension)
    {n m : ℕ} (hn : Even n) (hm : m<n) (hr : n-m≤3)
    (V : Matrix (Fin n) (Fin m) ℂ)
    (hV : ∀ i j,IsFourthRoot (V i j))
    (hgram : V.conjTranspose*V=(n : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) :
    ∃ z : Fin n → ℂ,(∀ i,IsFourthRoot (z i)) ∧ V.conjTranspose.mulVec z=0 := by
  classical
  obtain ⟨hA,hAG,hgate⟩ := quaternary_realification_gate V hV hgram
  apply hgate.mpr
  apply hClassical (Fin n⊕Fin n) (Fin m⊕Fin m)
    (realifiedMatrix (((1+Complex.I) : ℂ) • V))
  · obtain ⟨k,hk⟩ := hn
    simp only [Fintype.card_sum,Fintype.card_fin]
    exact ⟨k,by omega⟩
  · simp only [Fintype.card_sum,Fintype.card_fin]
    omega
  · simp only [Fintype.card_sum,Fintype.card_fin]
    omega
  · exact hA
  · simpa only [Fintype.card_sum,Fintype.card_fin,Nat.cast_add,two_mul] using hAG


theorem small_defect_quaternary_completion (hClassical : RealSmallDefectExtension)
    {n m : ℕ} (hn : Even n) (hm : m≤n) (hr : n-m≤3)
    (V : Matrix (Fin n) (Fin m) ℂ)
    (hV : ∀ i j,IsFourthRoot (V i j))
    (hgram : V.conjTranspose*V=(n : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) :
    ∃ H : Matrix (Fin n) (Fin n) ℂ,
      (∀ i j,IsFourthRoot (H i j)) ∧
      H.conjTranspose*H=(n : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) ∧
      ∀ i j,H i (Fin.castLE hm j)=V i j := by
  classical
  generalize hd : n-m=d
  induction d using Nat.strong_induction_on generalizing m with
  | h d ih =>
    by_cases hmn : m=n
    · subst m
      refine ⟨V,hV,hgram,?_⟩
      intro i j
      rfl
    · have hlt : m<n := by omega
      obtain ⟨z,hz,horth⟩ := small_defect_quaternary_extension hClassical hn hlt hr V hV hgram
      let W := appendFourthColumn V z
      have hW := appendFourthColumn_roots V z hV hz
      have hWG := appendFourthColumn_gram V z hz hgram horth
      have hnext : m+1≤n := by omega
      have hrnext : n-(m+1)≤3 := by omega
      obtain ⟨H,hH,hHG,hret⟩ := ih (n-(m+1)) (by omega)
        hnext hrnext W hW hWG rfl
      refine ⟨H,hH,hHG,?_⟩
      intro i j
      have h := hret i j.castSucc
      have heq : Fin.castLE (by omega : m+1≤n) j.castSucc=Fin.castLE hm j := by
        ext
        rfl
      simpa only [W,appendFourthColumn,Fin.snoc_castSucc,heq] using h


def HasQuaternaryCompletion {n m : ℕ} (V : Matrix (Fin n) (Fin m) ℂ) : Prop :=
  ∃ (hm : m≤n) (H : Matrix (Fin n) (Fin n) ℂ),
    (∀ i j,IsFourthRoot (H i j)) ∧
    H.conjTranspose*H=(n : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) ∧
    ∀ i j,H i (Fin.castLE hm j)=V i j

theorem quaternary_completion_supplies_column {n m : ℕ} (hm : m<n)
    (V : Matrix (Fin n) (Fin m) ℂ) (hc : HasQuaternaryCompletion V) :
    ∃ z : Fin n → ℂ,(∀ i,IsFourthRoot (z i)) ∧ V.conjTranspose.mulVec z=0 := by
  classical
  obtain ⟨hle,H,hH,hHG,hret⟩ := hc
  let k : Fin n := ⟨m,hm⟩
  refine ⟨fun i => H i k,fun i => hH i k,?_⟩
  ext j
  have hne : Fin.castLE hle j≠k := by
    intro heq
    have hh := congrArg Fin.val heq
    have hj := j.isLt
    change j.val=m at hh
    omega
  have hh := congrFun (congrFun hHG (Fin.castLE hle j)) k
  simpa [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.mulVec,dotProduct,
    Matrix.one_apply,hret,hne] using hh

theorem quaternary_defect_four_completion_gate (hClassical : RealSmallDefectExtension)
    {n m : ℕ} (hn : Even n) (hr : n-m=4)
    (V : Matrix (Fin n) (Fin m) ℂ)
    (hV : ∀ i j,IsFourthRoot (V i j))
    (hgram : V.conjTranspose*V=(n : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) :
    (HasQuaternaryCompletion V ↔
      ∃ z : Fin n → ℂ,(∀ i,IsFourthRoot (z i)) ∧ V.conjTranspose.mulVec z=0) ∧
    ∃ C : Finset (LinearMap.ker V.conjTranspose.mulVecLin),
      C.card≤64 ∧ (∀ v∈C,∀ i,IsFourthRoot (v.val i)) ∧
      (C.Nonempty ↔ HasQuaternaryCompletion V) := by
  classical
  have hm : m<n := by omega
  have hiff : HasQuaternaryCompletion V ↔
      ∃ z : Fin n → ℂ,(∀ i,IsFourthRoot (z i)) ∧ V.conjTranspose.mulVec z=0 := by
    constructor
    · exact quaternary_completion_supplies_column hm V
    · rintro ⟨z,hz,horth⟩
      have hnext : m+1≤n := by omega
      obtain ⟨H,hH,hHG,hret⟩ := small_defect_quaternary_completion hClassical hn
        hnext (by omega) (appendFourthColumn V z)
        (appendFourthColumn_roots V z hV hz)
        (appendFourthColumn_gram V z hz hgram horth)
      refine ⟨Nat.le_of_lt hm,H,hH,hHG,?_⟩
      intro i j
      have hh := hret i j.castSucc
      have heq : Fin.castLE hnext j.castSucc=Fin.castLE (Nat.le_of_lt hm) j := by
        ext
        rfl
      simpa only [appendFourthColumn,Fin.snoc_castSucc,heq] using hh
  refine ⟨hiff,?_⟩
  obtain ⟨C,hC,hroot,hsearch⟩ := bounded_quaternary_extension_test hm V hgram
  refine ⟨C,?_,hroot,hsearch.trans hiff.symm⟩
  have he : n-m-1=3 := by omega
  norm_num [he] at hC
  exact hC

end
end CompletionTheory
