/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module

public import CompletionTheory.ResidualBlocks
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Exact smaller-Hadamard equivalence for duplication residual spaces -/

@[expose] public section
namespace CompletionTheory
open Matrix

theorem block_hadamard_gives_sign_factor {δ ι J : Type*}
    [Fintype δ] [Fintype ι] [Fintype J] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq J] [Nonempty δ]
    (P : Matrix ι (δ ⊕ ι) ℝ) (hP : IsPartialHadamard P)
    (a : (δ ⊕ ι) → J) (s : (δ ⊕ ι) → ℝ)
    (ha : Function.Surjective a) (hs : IsCubeVector s)
    (hspace : LinearMap.ker P.mulVecLin = LinearMap.range (duplicationMap a s))
    (H : Matrix J J ℝ) (hH : Matrix.IsHadamard H) :
    ∃ B : Matrix δ (δ ⊕ ι) ℝ, IsSignMatrix B ∧ B.transpose * B = residualGram P := by
  classical
  have hcount := residual_block_count P hP a s ha hs hspace
  let e : δ ≃ J := Fintype.equivOfCardEq hcount.symm
  let B : Matrix δ (δ ⊕ ι) ℝ := fun i k => s k * H (e i) (a k)
  have hHsign (j k : J) : IsSign (H j k) :=
    Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hH.apply_mem j k)
  have hcol : H.transpose * H = (Fintype.card J : ℝ) • 1 := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hH.conjTranspose_mul
  have hsum (j k : J) : (∑ i : δ, H (e i) j * H (e i) k) =
      (Fintype.card J : ℝ) * (if j = k then 1 else 0) := by
    calc
      _ = ∑ i : J, H i j * H i k := e.sum_comp _
      _ = _ := by
        have h := congrArg (fun M => M j k) hcol
        simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] using h
  refine ⟨B, ?_, ?_⟩
  · intro i k
    rcases hs k with hs | hs <;> rcases hHsign (e i) (a k) with hh | hh <;>
      simp [B, hs, hh, IsSign]
  · ext k l
    change (∑ i : δ, (s k * H (e i) (a k)) * (s l * H (e i) (a l))) = residualGram P k l
    calc
      _ = (s k * s l) * ∑ i : δ, H (e i) (a k) * H (e i) (a l) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        rw [hsum, residualGram_duplication_formula P hP a s ha hs hspace]
        by_cases hkl : a k = a l
        · simp only [hkl, ite_true, mul_one, hcount]
          ring
        · simp [hkl]

theorem sign_factor_gives_block_hadamard {δ ι J : Type*}
    [Fintype δ] [Fintype ι] [Fintype J] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq J] [Nonempty δ]
    (P : Matrix ι (δ ⊕ ι) ℝ) (hP : IsPartialHadamard P)
    (a : (δ ⊕ ι) → J) (s : (δ ⊕ ι) → ℝ)
    (ha : Function.Surjective a) (hs : IsCubeVector s)
    (hspace : LinearMap.ker P.mulVecLin = LinearMap.range (duplicationMap a s))
    (B : Matrix δ (δ ⊕ ι) ℝ) (hB : IsSignMatrix B)
    (hfactor : B.transpose * B = residualGram P) :
    ∃ H : Matrix J J ℝ, Matrix.IsHadamard H := by
  classical
  have hcount := residual_block_count P hP a s ha hs hspace
  let e : δ ≃ J := Fintype.equivOfCardEq hcount.symm
  let : Nonempty J := ⟨e (Classical.arbitrary δ)⟩
  have ha' := ha
  choose r hr using ha'
  let H : Matrix J J ℝ := fun i j => B (e.symm i) (r j) * s (r j)
  have hsign : IsSignMatrix H := by
    intro i j
    rcases hB (e.symm i) (r j) with hb | hb <;> rcases hs (r j) with hs | hs <;>
      simp [H, hb, hs, IsSign]
  have hsum (j k : J) : (∑ i : J, B (e.symm i) (r j) * B (e.symm i) (r k)) =
      residualGram P (r j) (r k) := by
    calc
      _ = ∑ i : δ, B i (r j) * B i (r k) := e.symm.sum_comp _
      _ = _ := by
        have h := congrArg (fun M => M (r j) (r k)) hfactor
        simpa [Matrix.mul_apply] using h
  have hcol : H.transpose * H = (Fintype.card J : ℝ) • 1 := by
    ext j k
    change (∑ i : J, (B (e.symm i) (r j) * s (r j)) *
      (B (e.symm i) (r k) * s (r k))) = (Fintype.card J : ℝ) * (if j = k then 1 else 0)
    calc
      _ = (s (r j) * s (r k)) *
          ∑ i : J, B (e.symm i) (r j) * B (e.symm i) (r k) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        rw [hsum, residualGram_duplication_formula P hP a s ha hs hspace, hr, hr]
        by_cases hjk : j = k
        · subst k
          rcases hs (r j) with hs | hs <;> simp [hs, hcount]
        · simp [hjk]
  have ht : IsHadamard H.transpose :=
    ⟨fun i j => hsign j i, by simpa only [Matrix.transpose_transpose] using hcol⟩
  exact ⟨H, Matrix.isHadamard_transpose_iff.mp (isHadamard_mathlib ht)⟩

theorem duplication_residual_completion_iff {δ ι J : Type*}
    [Fintype δ] [Fintype ι] [Fintype J] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq J] [Nonempty δ]
    (P : Matrix ι (δ ⊕ ι) ℝ) (hP : IsPartialHadamard P)
    (a : (δ ⊕ ι) → J) (s : (δ ⊕ ι) → ℝ)
    (ha : Function.Surjective a) (hs : IsCubeVector s)
    (hspace : LinearMap.ker P.mulVecLin = LinearMap.range (duplicationMap a s)) :
    (∃ H : Matrix (δ ⊕ ι) (δ ⊕ ι) ℝ, Matrix.IsHadamard H ∧
      ∀ i j, H (Sum.inr i) j = P i j) ↔ ∃ Q : Matrix J J ℝ, Matrix.IsHadamard Q := by
  rw [← residual_factor_completion_iff P hP.1]
  constructor
  · rintro ⟨B, hB, hf⟩
    exact sign_factor_gives_block_hadamard P hP a s ha hs hspace B hB hf
  · rintro ⟨H, hH⟩
    exact block_hadamard_gives_sign_factor P hP a s ha hs hspace H hH

theorem partial_kernel_dimension_sum {δ ι : Type*}
    [Fintype δ] [Fintype ι] [DecidableEq δ] [DecidableEq ι] [Nonempty (δ ⊕ ι)]
    (P : Matrix ι (δ ⊕ ι) ℝ) (hP : IsPartialHadamard P) :
    Module.finrank ℝ (LinearMap.ker P.mulVecLin) = Fintype.card δ := by
  have hn : (Fintype.card (δ ⊕ ι) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  let M : Matrix (δ ⊕ ι) ι ℝ := (Fintype.card (δ ⊕ ι) : ℝ)⁻¹ • P.transpose
  have hPM : P * M = 1 := by
    simp only [M, Matrix.mul_smul, hP.2, smul_smul, inv_mul_cancel₀ hn, one_smul]
  have hsurj : Function.Surjective P.mulVecLin := by
    intro y
    refine ⟨M.mulVec y, ?_⟩
    change P.mulVec (M.mulVec y) = y
    rw [Matrix.mulVec_mulVec, hPM, Matrix.one_mulVec]
  have hdim := P.mulVecLin.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj] at hdim
  simp [Fintype.card_sum] at hdim
  omega

theorem maximum_residual_cube_completion {δ ι : Type*}
    [Fintype δ] [Fintype ι] [DecidableEq δ] [DecidableEq ι] [Nonempty (δ ⊕ ι)]
    (P : Matrix ι (δ ⊕ ι) ℝ) (hP : IsPartialHadamard P)
    (hmax : ∃ T : Finset (δ ⊕ ι), T.card = Module.finrank ℝ (LinearMap.ker P.mulVecLin) ∧
      ∃ e : (LinearMap.ker P.mulVecLin) ≃ₗ[ℝ] (T → ℝ),
        (∀ v j, e v j = v.val j.val) ∧ (cubeCandidates e).card = 2 ^ T.card) :
    ∃ I : Finset (δ ⊕ ι), I.card = Module.finrank ℝ (LinearMap.ker P.mulVecLin) ∧
      I.card = Fintype.card δ ∧ ∃ a : (δ ⊕ ι) → I, Function.Surjective a ∧
      ∃ s : (δ ⊕ ι) → ℝ, IsCubeVector s ∧
        LinearMap.ker P.mulVecLin = LinearMap.range (duplicationMap a s) ∧
        (∀ j : I, (blockSize a j : ℝ) = (Fintype.card (δ ⊕ ι) : ℝ) / (I.card : ℝ)) ∧
        ((∃ H : Matrix (δ ⊕ ι) (δ ⊕ ι) ℝ, Matrix.IsHadamard H ∧
          ∀ i j, H (Sum.inr i) j = P i j) ↔ ∃ Q : Matrix I I ℝ, Matrix.IsHadamard Q) := by
  classical
  obtain ⟨I, hI, a, ha, s, hs, hspace⟩ :=
    maximum_cube_duplication_space (LinearMap.ker P.mulVecLin) hmax
  have hdim := partial_kernel_dimension_sum P hP
  have hcount : I.card = Fintype.card δ := hI.trans hdim
  have hIpos : 0 < I.card := Finset.card_pos.mpr
    ⟨(a (Classical.arbitrary (δ ⊕ ι))).val, (a (Classical.arbitrary (δ ⊕ ι))).property⟩
  have hdpos : 0 < Fintype.card δ := by omega
  let : Nonempty δ := Fintype.card_pos_iff.mp hdpos
  refine ⟨I, hI, hcount, a, ha, s, hs, hspace, ?_, ?_⟩
  · intro j
    simpa only [hcount] using residual_block_size_quotient P hP a s ha hs hspace j
  · exact duplication_residual_completion_iff P hP a s ha hs hspace

end CompletionTheory
