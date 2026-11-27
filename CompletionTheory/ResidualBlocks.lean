/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module

public import CompletionTheory.CubeRigidity
public import CompletionTheory.ResidualFactor

/-! # Duplication blocks in an actual partial-Hadamard residual space -/

@[expose] public section
namespace CompletionTheory
open Matrix

noncomputable def blockIndicator {κ J : Type*} (a : κ → J) (s : κ → ℝ) (j : J) : κ → ℝ := by
  classical
  exact fun i => if a i = j then s i else 0

noncomputable def blockSize {κ J : Type*} [Fintype κ] (a : κ → J) (j : J) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => a i = j)).card

theorem duplicationMap_single {κ J : Type*} [DecidableEq J]
    (a : κ → J) (s : κ → ℝ) (j : J) :
    duplicationMap a s (Pi.single j 1) = blockIndicator a s j := by
  classical
  funext i
  by_cases h : a i = j
  · simp [duplicationMap, blockIndicator, h]
  · simp [duplicationMap, blockIndicator, h]

theorem residualGram_transpose {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (P : Matrix ι κ ℝ) : (residualGram P).transpose = residualGram P := by
  simp [residualGram, Matrix.transpose_sub, Matrix.transpose_mul]

theorem partial_mul_residualGram_zero {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) : P * residualGram P = 0 := by
  simp [residualGram, Matrix.mul_sub, ← Matrix.mul_assoc, hP.2]

theorem residualGram_column_mem_kernel {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (k : κ) :
    (fun i => residualGram P i k) ∈ LinearMap.ker P.mulVecLin := by
  change P.mulVec (fun i => residualGram P i k) = 0
  ext j
  have h := congrArg (fun M => M j k) (partial_mul_residualGram_zero P hP)
  simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.zero_apply, Pi.zero_apply] using h

theorem residualGram_mulVec_kernel {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ] (P : Matrix ι κ ℝ)
    (x : κ → ℝ) (hx : P.mulVec x = 0) :
    (residualGram P).mulVec x = (Fintype.card κ : ℝ) • x := by
  unfold residualGram
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, sub_zero]

theorem blockIndicator_in_kernel {ι κ J : Type*}
    [Fintype κ] [DecidableEq J] (P : Matrix ι κ ℝ)
    (a : κ → J) (s : κ → ℝ)
    (hspace : LinearMap.ker P.mulVecLin = LinearMap.range (duplicationMap a s)) (j : J) :
    P.mulVec (blockIndicator a s j) = 0 := by
  change blockIndicator a s j ∈ LinearMap.ker P.mulVecLin
  rw [hspace]
  exact ⟨Pi.single j 1, duplicationMap_single a s j⟩

theorem indicator_dot_duplication {κ J : Type*} [Fintype κ]
    (a : κ → J) (s : κ → ℝ) (hs : IsCubeVector s) (j : J) (x : J → ℝ) :
    (∑ i, blockIndicator a s j i * duplicationMap a s x i) = (blockSize a j : ℝ) * x j := by
  classical
  have hterm (i : κ) : blockIndicator a s j i * duplicationMap a s x i =
      if a i = j then x j else 0 := by
    by_cases hij : a i = j
    · simp only [blockIndicator, hij, ite_true, duplicationMap, LinearMap.coe_mk,
        AddHom.coe_mk]
      have hh := isSign_sq (hs i)
      calc
        s i * (s i * x j) = s i ^ 2 * x j := by ring
        _ = x j := by rw [hh, one_mul]
    · simp [blockIndicator, duplicationMap, hij]
  simp_rw [hterm]
  simp [blockSize, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul]

theorem blockSize_mul_residual_diagonal {ι κ J : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [DecidableEq J]
    (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (a : κ → J) (s : κ → ℝ)
    (hs : IsCubeVector s)
    (hspace : LinearMap.ker P.mulVecLin = LinearMap.range (duplicationMap a s)) (k : κ) :
    (blockSize a (a k) : ℝ) * residualGram P k k = Fintype.card κ := by
  classical
  have hcol := residualGram_column_mem_kernel P hP k
  rw [hspace] at hcol
  obtain ⟨x, hx⟩ := hcol
  have hdot : (∑ i, blockIndicator a s (a k) i * residualGram P i k) =
      (Fintype.card κ : ℝ) * s k := by
    have hmul := congrFun (residualGram_mulVec_kernel P (blockIndicator a s (a k))
      (blockIndicator_in_kernel P a s hspace (a k))) k
    have hsym (i : κ) : residualGram P k i = residualGram P i k := by
      exact congrArg (fun M => M i k) (residualGram_transpose P)
    simpa [Matrix.mulVec, dotProduct, hsym, mul_comm, blockIndicator] using hmul
  have hpair : (∑ i, blockIndicator a s (a k) i * residualGram P i k) =
      (blockSize a (a k) : ℝ) * x (a k) := by
    have hx' (i : κ) := congrFun hx i
    simp_rw [← hx']
    exact indicator_dot_duplication a s hs (a k) x
  have hdiag := congrFun hx k
  change s k * x (a k) = residualGram P k k at hdiag
  have hsquare := isSign_sq (hs k)
  have hsize := hpair.symm.trans hdot
  calc
    _ = ((blockSize a (a k) : ℝ) * x (a k)) * s k := by rw [← hdiag]; ring
    _ = ((Fintype.card κ : ℝ) * s k) * s k := by rw [hsize]
    _ = (Fintype.card κ : ℝ) * s k ^ 2 := by ring
    _ = _ := by rw [hsquare, mul_one]

theorem blockSize_pos {κ J : Type*} [Fintype κ] (a : κ → J)
    (ha : Function.Surjective a) (j : J) : 0 < blockSize a j := by
  classical
  obtain ⟨k, hk⟩ := ha j
  exact Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩⟩

theorem sum_blockSize {κ J : Type*} [Fintype κ] [Fintype J] (a : κ → J) :
    (∑ j, blockSize a j) = Fintype.card κ := by
  classical
  simp only [blockSize, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem residual_block_size_equation {δ ι J : Type*}
    [Fintype δ] [Fintype ι] [DecidableEq δ] [DecidableEq ι] [DecidableEq J]
    (P : Matrix ι (δ ⊕ ι) ℝ) (hP : IsPartialHadamard P)
    (a : (δ ⊕ ι) → J) (s : (δ ⊕ ι) → ℝ)
    (ha : Function.Surjective a) (hs : IsCubeVector s)
    (hspace : LinearMap.ker P.mulVecLin = LinearMap.range (duplicationMap a s)) (j : J) :
    (blockSize a j : ℝ) * (Fintype.card δ : ℝ) = Fintype.card (δ ⊕ ι) := by
  obtain ⟨k, rfl⟩ := ha j
  have h := blockSize_mul_residual_diagonal P hP a s hs hspace k
  rw [residualGram_diagonal P hP.1 k] at h
  exact h

theorem residual_blocks_equal_size {δ ι J : Type*}
    [Fintype δ] [Fintype ι] [DecidableEq δ] [DecidableEq ι] [Nonempty δ] [DecidableEq J]
    (P : Matrix ι (δ ⊕ ι) ℝ) (hP : IsPartialHadamard P)
    (a : (δ ⊕ ι) → J) (s : (δ ⊕ ι) → ℝ)
    (ha : Function.Surjective a) (hs : IsCubeVector s)
    (hspace : LinearMap.ker P.mulVecLin = LinearMap.range (duplicationMap a s)) (j k : J) :
    blockSize a j = blockSize a k := by
  have hq : (Fintype.card δ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h := (residual_block_size_equation P hP a s ha hs hspace j).trans
    (residual_block_size_equation P hP a s ha hs hspace k).symm
  exact_mod_cast (mul_right_cancel₀ hq h)

theorem residual_block_size_quotient {δ ι J : Type*}
    [Fintype δ] [Fintype ι] [DecidableEq δ] [DecidableEq ι] [Nonempty δ] [DecidableEq J]
    (P : Matrix ι (δ ⊕ ι) ℝ) (hP : IsPartialHadamard P)
    (a : (δ ⊕ ι) → J) (s : (δ ⊕ ι) → ℝ)
    (ha : Function.Surjective a) (hs : IsCubeVector s)
    (hspace : LinearMap.ker P.mulVecLin = LinearMap.range (duplicationMap a s)) (j : J) :
    (blockSize a j : ℝ) = (Fintype.card (δ ⊕ ι) : ℝ) / (Fintype.card δ : ℝ) := by
  have hq : (Fintype.card δ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact (eq_div_iff hq).mpr (residual_block_size_equation P hP a s ha hs hspace j)

theorem residual_block_count {δ ι J : Type*}
    [Fintype δ] [Fintype ι] [Fintype J] [DecidableEq δ] [DecidableEq ι]
    [Nonempty δ] [DecidableEq J]
    (P : Matrix ι (δ ⊕ ι) ℝ) (hP : IsPartialHadamard P)
    (a : (δ ⊕ ι) → J) (s : (δ ⊕ ι) → ℝ)
    (ha : Function.Surjective a) (hs : IsCubeVector s)
    (hspace : LinearMap.ker P.mulVecLin = LinearMap.range (duplicationMap a s)) :
    Fintype.card J = Fintype.card δ := by
  classical
  let j0 := a (Sum.inl (Classical.arbitrary δ))
  have huniform (j : J) : blockSize a j = blockSize a j0 :=
    residual_blocks_equal_size P hP a s ha hs hspace j j0
  have hsum := sum_blockSize a
  simp_rw [huniform] at hsum
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  have hsumR : (Fintype.card J : ℝ) * (blockSize a j0 : ℝ) = Fintype.card (δ ⊕ ι) := by
    exact_mod_cast hsum
  have hsize := residual_block_size_equation P hP a s ha hs hspace j0
  have hc : (blockSize a j0 : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (blockSize_pos a ha j0)
  have heq : (Fintype.card J : ℝ) = Fintype.card δ :=
    mul_right_cancel₀ hc (hsumR.trans (by simpa only [mul_comm] using hsize.symm))
  exact_mod_cast heq

theorem indicator_dot_residual_column {ι κ J : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ] [DecidableEq J]
    (P : Matrix ι κ ℝ) (a : κ → J) (s : κ → ℝ)
    (hspace : LinearMap.ker P.mulVecLin = LinearMap.range (duplicationMap a s)) (j : J) (k : κ) :
    (∑ i, blockIndicator a s j i * residualGram P i k) =
      (Fintype.card κ : ℝ) * blockIndicator a s j k := by
  have hmul := congrFun (residualGram_mulVec_kernel P (blockIndicator a s j)
    (blockIndicator_in_kernel P a s hspace j)) k
  have hsym (i : κ) : residualGram P k i = residualGram P i k :=
    congrArg (fun M => M i k) (residualGram_transpose P)
  simpa [Matrix.mulVec, dotProduct, hsym, mul_comm] using hmul

theorem residualGram_duplication_formula {δ ι J : Type*}
    [Fintype δ] [Fintype ι] [DecidableEq δ] [DecidableEq ι] [DecidableEq J]
    (P : Matrix ι (δ ⊕ ι) ℝ) (hP : IsPartialHadamard P)
    (a : (δ ⊕ ι) → J) (s : (δ ⊕ ι) → ℝ)
    (ha : Function.Surjective a) (hs : IsCubeVector s)
    (hspace : LinearMap.ker P.mulVecLin = LinearMap.range (duplicationMap a s)) (i k : δ ⊕ ι) :
    residualGram P i k = if a i = a k then (Fintype.card δ : ℝ) * s i * s k else 0 := by
  classical
  have hcol := residualGram_column_mem_kernel P hP k
  rw [hspace] at hcol
  obtain ⟨x, hx⟩ := hcol
  have hcoeff (j : J) : x j = (Fintype.card δ : ℝ) * blockIndicator a s j k := by
    have hdot := indicator_dot_residual_column P a s hspace j k
    have hx' (b : δ ⊕ ι) := congrFun hx b
    simp_rw [← hx'] at hdot
    rw [indicator_dot_duplication a s hs] at hdot
    have hsize := residual_block_size_equation P hP a s ha hs hspace j
    have hc : (blockSize a j : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (blockSize_pos a ha j)
    apply mul_left_cancel₀ hc
    rw [hdot]
    rw [← hsize]
    ring
  have hval := congrFun hx i
  change s i * x (a i) = residualGram P i k at hval
  rw [hcoeff] at hval
  rw [← hval]
  by_cases hik : a i = a k
  · simp [blockIndicator, hik]
    ring
  · simp [blockIndicator, hik, Ne.symm hik]

end CompletionTheory
