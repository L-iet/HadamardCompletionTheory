/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.RealConferenceConversion
public import Mathlib.Tactic
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace CompletionTheory

noncomputable def weighingRowMix {ν : Type*} [Fintype ν]
    (W V : Matrix ν ν ℝ) (w : ℝ) : Matrix ν ν ℝ := w⁻¹ • (V*W.transpose)

theorem weighing_scaled_inverse {ν : Type*} [Fintype ν] [DecidableEq ν]
    (W : Matrix ν ν ℝ) (w : ℝ) (hw : w≠0)
    (hW : W*W.transpose=w • (1 : Matrix ν ν ℝ)) :
    W*(w⁻¹ • W.transpose)=1 ∧ (w⁻¹ • W.transpose)*W=1 := by
  have h : W*(w⁻¹ • W.transpose)=1 := by
    rw [Matrix.mul_smul,hW,smul_smul,inv_mul_cancel₀ hw,one_smul]
  exact ⟨h,mul_eq_one_comm.mp h⟩

theorem weighing_transpose_gram {ν : Type*} [Fintype ν] [DecidableEq ν]
    (W : Matrix ν ν ℝ) (w : ℝ) (hw : w≠0)
    (hW : W*W.transpose=w • (1 : Matrix ν ν ℝ)) :
    W.transpose*W=w • (1 : Matrix ν ν ℝ) := by
  have h := congrArg (fun M : Matrix ν ν ℝ => w • M) (weighing_scaled_inverse W w hw hW).2
  simpa only [Matrix.smul_mul,smul_smul,mul_inv_cancel₀ hw,one_smul] using h

theorem weighing_row_mix_reconstruct {ν : Type*} [Fintype ν] [DecidableEq ν]
    (W V : Matrix ν ν ℝ) (w : ℝ) (hw : w≠0)
    (hW : W*W.transpose=w • (1 : Matrix ν ν ℝ)) :
    weighingRowMix W V w*W=V := by
  rw [weighingRowMix,Matrix.smul_mul,Matrix.mul_assoc,weighing_transpose_gram W w hw hW,
    Matrix.mul_smul,Matrix.mul_one,smul_smul,inv_mul_cancel₀ hw,one_smul]

theorem weighing_row_mix_orthogonal {ν : Type*} [Fintype ν] [DecidableEq ν]
    (W V : Matrix ν ν ℝ) (w : ℝ) (hw : w≠0)
    (hW : W*W.transpose=w • (1 : Matrix ν ν ℝ))
    (hV : V*V.transpose=w • (1 : Matrix ν ν ℝ)) :
    weighingRowMix W V w*(weighingRowMix W V w).transpose=1 := by
  rw [weighingRowMix,Matrix.transpose_smul,Matrix.transpose_mul,Matrix.transpose_transpose,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  calc
    _=(w⁻¹*w⁻¹) • (V*(W.transpose*W)*V.transpose) := by congr 1; noncomm_ring
    _=1 := by
      rw [weighing_transpose_gram W w hw hW,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul,hV,smul_smul,smul_smul]
      have hh : w⁻¹*w⁻¹*w*w=1 := by field_simp
      rw [hh,one_smul]


theorem weighing_row_mix_unchanged_row {ν : Type*} [Fintype ν] [DecidableEq ν]
    (W V : Matrix ν ν ℝ) (w : ℝ) (hw : w≠0)
    (hW : W*W.transpose=w • (1 : Matrix ν ν ℝ)) (p : ν)
    (hRow : ∀ k, V p k=W p k) :
    ∀ q, weighingRowMix W V w p q=(1 : Matrix ν ν ℝ) p q := by
  intro q
  have hMul : (V*W.transpose) p q=(W*W.transpose) p q := by simp [Matrix.mul_apply,hRow]
  simp only [weighingRowMix,Matrix.smul_apply,smul_eq_mul,hMul,hW]
  change w⁻¹*(w*(1 : Matrix ν ν ℝ) p q)=(1 : Matrix ν ν ℝ) p q
  rw [← mul_assoc,inv_mul_cancel₀ hw,one_mul]

theorem orthogonal_unchanged_row_forces_column {ν : Type*} [Fintype ν] [DecidableEq ν]
    (U : Matrix ν ν ℝ) (hU : U*U.transpose=1) (r : ν)
    (hRow : ∀ k, U r k=(1 : Matrix ν ν ℝ) r k) :
    ∀ p, U p r=(1 : Matrix ν ν ℝ) p r := by
  intro p
  have h := congrArg (fun M : Matrix ν ν ℝ => M p r) hU
  simpa [Matrix.mul_apply,Matrix.transpose_apply,hRow,Matrix.one_apply,mul_ite] using h


theorem two_pair_zero_support_cross_block {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U W V : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) (r s : ι)
    (hRecon : U*W=V) (hWZero : ∀ i, twoBlock W i i=0) (hVZero : ∀ i, twoBlock V i i=0)
    (hCols : ∀ k, k≠r → k≠s → ∀ a b : Fin 2, ∀ i,
      U (a,i) (b,k)=(1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) (a,i) (b,k)) :
    twoBlock U r s*twoBlock W s r=0 := by
  ext a b
  have hSum (c : Fin 2) : (∑ k : ι, U (a,r) (c,k)*W (c,k) (b,r))=
      U (a,r) (c,s)*W (c,s) (b,r) := by
    apply Finset.sum_eq_single s
    · intro k _ hks
      by_cases hkr : k=r
      · subst k
        have hz := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M c b) (hWZero r)
        change W (c,r) (b,r)=0 at hz
        rw [hz,mul_zero]
      · rw [hCols k hkr hks a c r]
        have hneq : (a,r)≠(c,k) := by intro h; exact hkr (congrArg Prod.snd h).symm
        simp [Matrix.one_apply,hneq]
    · intro h; exact False.elim (h (Finset.mem_univ s))
  have he := congrArg (fun M : Matrix (Fin 2×ι) (Fin 2×ι) ℝ => M (a,r) (b,r)) hRecon
  have hz := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M a b) (hVZero r)
  change V (a,r) (b,r)=0 at hz
  rw [hz] at he
  simp only [Matrix.mul_apply,Fintype.sum_prod_type] at he
  simp only [hSum] at he
  simpa only [Matrix.mul_apply,twoBlock,Matrix.zero_apply] using he

theorem two_square_hadamard_right_cancel_zero (M B : Matrix (Fin 2) (Fin 2) ℝ)
    (hB : B*B.transpose=(2:ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (h : M*B=0) : M=0 := by
  have hh := congrArg (fun N : Matrix (Fin 2) (Fin 2) ℝ => N*B.transpose) h
  rw [Matrix.mul_assoc,hB,Matrix.mul_smul,Matrix.mul_one,Matrix.zero_mul] at hh
  ext a b
  have he := congrArg (fun N : Matrix (Fin 2) (Fin 2) ℝ => N a b) hh
  change (2:ℝ)*M a b=0 at he
  change M a b=0
  linarith


theorem two_pair_mixing_is_block_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U W V : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) (r s : ι)
    (hU : U*U.transpose=1) (hRecon : U*W=V)
    (hWZero : ∀ i, twoBlock W i i=0) (hVZero : ∀ i, twoBlock V i i=0)
    (hOff : ∀ i j, i≠j → twoBlock W i j*(twoBlock W i j).transpose=
      (2:ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hRows : ∀ i, i≠r → i≠s → ∀ a : Fin 2, ∀ q,
      U (a,i) q=(1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) (a,i) q) :
    U=Matrix.blockDiagonal (fun i => twoBlock U i i) := by
  have hCols (k : ι) (hkr : k≠r) (hks : k≠s) (b : Fin 2) (p : Fin 2×ι) :
      U p (b,k)=(1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) p (b,k) :=
    orthogonal_unchanged_row_forces_column U hU (b,k) (hRows k hkr hks b) p
  have hRS (hrs : r≠s) : twoBlock U r s=0 :=
    two_square_hadamard_right_cancel_zero _ _ (hOff s r (Ne.symm hrs))
      (two_pair_zero_support_cross_block U W V r s hRecon hWZero hVZero
        (fun k hkr hks a b i => hCols k hkr hks b (a,i)))
  have hSR (hsr : s≠r) : twoBlock U s r=0 :=
    two_square_hadamard_right_cancel_zero _ _ (hOff r s (Ne.symm hsr))
      (two_pair_zero_support_cross_block U W V s r hRecon hWZero hVZero
        (fun k hks hkr a b i => hCols k hkr hks b (a,i)))
  have hAllOff (i j : ι) (hij : i≠j) : twoBlock U i j=0 := by
    by_cases hi : i=r ∨ i=s
    · by_cases hj : j=r ∨ j=s
      · rcases hi with hi|hi <;> rcases hj with hj|hj
        · subst i; subst j; exact False.elim (hij rfl)
        · subst i; subst j; exact hRS hij
        · subst i; subst j; exact hSR hij
        · subst i; subst j; exact False.elim (hij rfl)
      · push_neg at hj
        ext a b
        change U (a,i) (b,j)=0
        rw [hCols j hj.1 hj.2 b (a,i)]
        have hneq : (a,i)≠(b,j) := by intro h; exact hij (congrArg Prod.snd h)
        simp [Matrix.one_apply,hneq]
    · push_neg at hi
      ext a b
      change U (a,i) (b,j)=0
      rw [hRows i hi.1 hi.2 a (b,j)]
      have hneq : (a,i)≠(b,j) := by intro h; exact hij (congrArg Prod.snd h)
      simp [Matrix.one_apply,hneq]
  ext ⟨a,i⟩ ⟨b,j⟩
  by_cases hij : i=j
  · subst j; simp [Matrix.blockDiagonal_apply,twoBlock]
  · have hz := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M a b) (hAllOff i j hij)
    change U (a,i) (b,j)=0 at hz
    simp [Matrix.blockDiagonal_apply,hij,hz]


theorem walsh_two_right_cancel (M N : Matrix (Fin 2) (Fin 2) ℝ)
    (h : M*walshTwoReal=N*walshTwoReal) : M=N := by
  have hz : (M-N)*walshTwoReal=0 := by rw [Matrix.sub_mul,h,sub_self]
  exact sub_eq_zero.mp (two_square_hadamard_right_cancel_zero _ _ walshTwoReal_gram hz)

theorem block_diagonal_mul_twoBlock {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Matrix (Fin 2) (Fin 2) ℝ) (W : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) (i j : ι) :
    twoBlock (Matrix.blockDiagonal S*W) i j=S i*twoBlock W i j := by
  ext a b
  have h := blockDiagonal_mul_transpose_entry W.transpose S i j a b
  have ht : (twoBlock W.transpose j i).transpose=twoBlock W i j := by ext c d; rfl
  rw [Matrix.transpose_transpose,ht] at h
  exact h

theorem signed_two_identity_real : signedTwoReal (false,false,false)=1 := by
  ext a b; fin_cases a <;> fin_cases b <;> norm_num [signedTwoReal,signedTwoInt]

theorem normalized_block_diagonal_mix_is_signed {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (A B : ι → ι → SignedTwoState) (U : Matrix (Fin 2×ι) (Fin 2×ι) ℝ)
    (hDiag : U=Matrix.blockDiagonal (fun i => twoBlock U i i))
    (hRecon : U*normalizedTwoReal A=normalizedTwoReal B) :
    ∃ T : ι → SignedTwoState, U=signedTwoBlockDiagonal T := by
  classical
  have hExists (i : ι) : ∃ d : SignedTwoState, twoBlock U i i=signedTwoReal d := by
    obtain ⟨j,hji⟩ := exists_ne i
    have hij : i≠j := Ne.symm hji
    have hb := congrArg (fun W : Matrix (Fin 2×ι) (Fin 2×ι) ℝ => twoBlock W i j) hRecon
    rw [hDiag,block_diagonal_mul_twoBlock,normalizedTwoReal_offdiagonal A i j hij,
      normalizedTwoReal_offdiagonal B i j hij] at hb
    have hc : twoBlock U i i*signedTwoReal (A i j)=signedTwoReal (B i j) :=
      walsh_two_right_cancel _ _ (by simpa only [Matrix.mul_assoc] using hb)
    have hm := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M*(signedTwoReal (A i j)).transpose) hc
    rw [Matrix.mul_assoc,(signed_two_real_orthogonal (A i j)).1,Matrix.mul_one] at hm
    obtain ⟨d,hd⟩ := signed_two_real_triple_transpose_closed (B i j) (A i j) (false,false,false)
    rw [signed_two_identity_real,Matrix.mul_one] at hd
    exact ⟨d,hm.trans hd.symm⟩
  choose T hT using hExists
  refine ⟨T,?_⟩
  rw [hDiag]
  unfold signedTwoBlockDiagonal
  congr 1
  funext i
  exact hT i


theorem two_fixed_support_pairs_are_signed_row_permutation {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (A B : ι → ι → SignedTwoState) (r s : ι)
    (hA : normalizedTwoReal A*(normalizedTwoReal A).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (hB : normalizedTwoReal B*(normalizedTwoReal B).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (hRet : ∀ i, i≠r → i≠s → ∀ a : Fin 2, ∀ q,
      normalizedTwoReal B (a,i) q=normalizedTwoReal A (a,i) q) :
    ∃ T : ι → SignedTwoState,
      normalizedTwoReal B=signedTwoBlockDiagonal T*normalizedTwoReal A ∧
      ∀ i, i≠r → i≠s → signedTwoReal (T i)=1 := by
  let w : ℝ := (Fintype.card (Fin 2×ι) : ℝ)-2
  have hCard : (2:ℝ)≤Fintype.card ι := by exact_mod_cast (Nat.succ_le_of_lt (Fintype.one_lt_card (α:=ι)))
  have hw : w≠0 := by
    dsimp [w]
    simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
    linarith
  let U := weighingRowMix (normalizedTwoReal A) (normalizedTwoReal B) w
  have hU : U*U.transpose=1 := weighing_row_mix_orthogonal _ _ w hw hA hB
  have hRecon : U*normalizedTwoReal A=normalizedTwoReal B := weighing_row_mix_reconstruct _ _ w hw hA
  have hRows (i : ι) (hir : i≠r) (his : i≠s) (a : Fin 2) :
      ∀ q, U (a,i) q=(1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) (a,i) q :=
    weighing_row_mix_unchanged_row _ _ w hw hA (a,i) (hRet i hir his a)
  have hOff (i j : ι) (hij : i≠j) :
      twoBlock (normalizedTwoReal A) i j*(twoBlock (normalizedTwoReal A) i j).transpose=
        (2:ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [normalizedTwoReal_offdiagonal A i j hij]
    exact signedTwo_walsh_real_gram (A i j)
  have hDiag := two_pair_mixing_is_block_diagonal U (normalizedTwoReal A) (normalizedTwoReal B) r s hU hRecon
    (normalizedTwoReal_diagonal A) (normalizedTwoReal_diagonal B) hOff hRows
  obtain ⟨T,hT⟩ := normalized_block_diagonal_mix_is_signed A B U hDiag hRecon
  refine ⟨T,?_,?_⟩
  · rw [hT] at hRecon
    exact hRecon.symm
  · intro i hir his
    have hId : twoBlock U i i=1 := by
      ext a b
      have h := hRows i hir his a (b,i)
      simpa [twoBlock,Matrix.one_apply,Prod.mk.injEq] using h
    rw [hT] at hId
    ext a b
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M a b) hId
    change (if i=i then signedTwoReal (T i) a b else 0)=(1 : Matrix (Fin 2) (Fin 2) ℝ) a b at he
    simpa only [if_pos rfl,ite_true] using he


theorem signed_two_row_mul_entry {κ : Type*} (d : SignedTwoState)
    (M : Matrix (Fin 2) κ ℝ) (a : Fin 2) (b : κ) :
    (signedTwoReal d*M) a b=
      (if (if a=0 then d.2.1 else d.2.2) then (-1:ℝ) else 1)*M (if d.1 then Fin.rev a else a) b := by
  rcases d with ⟨p,e,f⟩
  cases p <;> cases e <;> cases f <;> fin_cases a <;>
    norm_num [signedTwoReal,signedTwoInt,Matrix.map_apply,Matrix.mul_apply,Fin.sum_univ_two,Fin.rev]

theorem signed_block_left_hadamard {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → SignedTwoState) (H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ)
    (hH : Matrix.IsHadamard H) : Matrix.IsHadamard (signedTwoBlockDiagonal T*H) := by
  have hD := signed_two_block_diagonal_orthogonal T
  have hGram : H*H.transpose=(Fintype.card (Fin 2×ι) : ℝ) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hH.mul_conjTranspose
  have hColGram : H.transpose*H=(Fintype.card (Fin 2×ι) : ℝ) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hH.conjTranspose_mul
  refine ⟨?_,?_,?_⟩
  · rintro ⟨a,i⟩ ⟨b,j⟩
    apply Unitary.mem_iff_eq_one_or_eq_neg_one.mpr
    change IsSign ((twoBlock (signedTwoBlockDiagonal T*H) i j) a b)
    rw [signedTwoBlockDiagonal,block_diagonal_mul_twoBlock,signed_two_row_mul_entry]
    have hSign := Unitary.mem_iff_eq_one_or_eq_neg_one.mp
      (hH.apply_mem ((if (T i).1 then Fin.rev a else a),i) (b,j))
    change IsSign ((twoBlock H i j) (if (T i).1 then Fin.rev a else a) b) at hSign
    split_ifs at * <;> rcases hSign with h|h <;> rw [h] <;> norm_num [IsSign]
  · simp only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_mul]
    calc
      _=signedTwoBlockDiagonal T*(H*H.transpose)*(signedTwoBlockDiagonal T).transpose := by noncomm_ring
      _=_ := by rw [hGram,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul,hD.1]
  · simp only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_mul]
    calc
      _=H.transpose*((signedTwoBlockDiagonal T).transpose*signedTwoBlockDiagonal T)*H := by noncomm_ring
      _=_ := by rw [hD.2,Matrix.mul_one,hColGram]

theorem signed_block_transpose_closed {ι : Type*} [DecidableEq ι] (T : ι → SignedTwoState) :
    ∃ S : ι → SignedTwoState, signedTwoBlockDiagonal S=(signedTwoBlockDiagonal T).transpose := by
  classical
  have h (i : ι) : ∃ s : SignedTwoState, signedTwoReal s=(signedTwoReal (T i)).transpose := by
    obtain ⟨s,hs⟩ := signedTwoInt_transpose_closed (T i)
    refine ⟨s,?_⟩
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (Int.castRingHom ℝ)) hs
    simpa only [signedTwoReal,← Matrix.transpose_map] using he
  choose S hS using h
  refine ⟨S,?_⟩
  rw [signedTwoBlockDiagonal,signedTwoBlockDiagonal,Matrix.blockDiagonal_transpose]
  congr 1
  funext i
  exact hS i


theorem signed_block_transfers_filling {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → SignedTwoState) (W H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ)
    (hH : IsZeroBlockHadamardFilling W H) :
    IsZeroBlockHadamardFilling (signedTwoBlockDiagonal T*W) (signedTwoBlockDiagonal T*H) := by
  refine ⟨signed_block_left_hadamard T H hH.1,?_⟩
  rintro ⟨a,i⟩ ⟨b,j⟩ hij
  have hBlock : twoBlock H i j=twoBlock W i j := by
    ext c d
    exact hH.2 (c,i) (d,j) hij
  change (twoBlock (signedTwoBlockDiagonal T*H) i j) a b=
    (twoBlock (signedTwoBlockDiagonal T*W) i j) a b
  rw [signedTwoBlockDiagonal,block_diagonal_mul_twoBlock,block_diagonal_mul_twoBlock,hBlock]

theorem signed_block_fill_feasibility_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → SignedTwoState) (W : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) :
    (∃ H, IsZeroBlockHadamardFilling W H) ↔
      ∃ K, IsZeroBlockHadamardFilling (signedTwoBlockDiagonal T*W) K := by
  constructor
  · rintro ⟨H,hH⟩
    exact ⟨signedTwoBlockDiagonal T*H,signed_block_transfers_filling T W H hH⟩
  · rintro ⟨K,hK⟩
    obtain ⟨S,hS⟩ := signed_block_transpose_closed T
    have hBack := signed_block_transfers_filling S (signedTwoBlockDiagonal T*W) K hK
    have hWBack : signedTwoBlockDiagonal S*(signedTwoBlockDiagonal T*W)=W := by
      rw [hS,← Matrix.mul_assoc,(signed_two_block_diagonal_orthogonal T).2,Matrix.one_mul]
    rw [hWBack] at hBack
    exact ⟨signedTwoBlockDiagonal S*K,hBack⟩

theorem two_fixed_support_pairs_preserve_feasibility {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (A B : ι → ι → SignedTwoState) (r s : ι)
    (hA : normalizedTwoReal A*(normalizedTwoReal A).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (hB : normalizedTwoReal B*(normalizedTwoReal B).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (hRet : ∀ i, i≠r → i≠s → ∀ a : Fin 2, ∀ q,
      normalizedTwoReal B (a,i) q=normalizedTwoReal A (a,i) q) :
    ∃ T : ι → SignedTwoState,
      normalizedTwoReal B=signedTwoBlockDiagonal T*normalizedTwoReal A ∧
      (∀ i, i≠r → i≠s → signedTwoReal (T i)=1) ∧
      ((∃ H, IsZeroBlockHadamardFilling (normalizedTwoReal A) H) ↔
        ∃ K, IsZeroBlockHadamardFilling (normalizedTwoReal B) K) := by
  obtain ⟨T,hEq,hId⟩ := two_fixed_support_pairs_are_signed_row_permutation A B r s hA hB hRet
  refine ⟨T,hEq,hId,?_⟩
  rw [hEq]
  exact signed_block_fill_feasibility_iff T (normalizedTwoReal A)

end CompletionTheory
