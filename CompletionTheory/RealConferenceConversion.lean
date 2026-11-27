/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0.
Original formal proof of the conference normalization input stated in
Geramita--Verner (1976), Theorem 2, doi:10.4153/CJM-1976-028-3. -/
module
public import CompletionTheory.SignedTwoBlocks
public import CompletionTheory.WeighingNormalization
public import CompletionTheory.RealComponentSections
public import Mathlib.Tactic
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace CompletionTheory

def IsDiagonalConferenceInt {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Matrix ι ι ℤ) : Prop :=
  (∀ i, C i i=0) ∧ (∀ i j, i≠j → C i j=1 ∨ C i j= -1) ∧
    C*C.transpose=((Fintype.card ι : ℤ)-1) • (1 : Matrix ι ι ℤ)

theorem conference_offdiagonal_dot {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℤ) (hC : IsDiagonalConferenceInt C) (i j : ι) (hij : i≠j) :
    (∑ k, C i k*C j k)=0 := by
  have h := congrArg (fun M : Matrix ι ι ℤ => M i j) hC.2.2
  simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.one_apply,if_neg hij,mul_zero] using h

theorem normalized_conference_row_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℤ) (hC : IsDiagonalConferenceInt C) (root : ι)
    (hRow : ∀ k, k≠root → C root k=1) (hCol : ∀ k, k≠root → C k root= -1)
    (i : ι) (hi : i≠root) : (∑ k, C i k)= -1 := by
  have hDot := conference_offdiagonal_dot C hC i root hi
  have hTerm (k : ι) : C i k*C root k=C i k-(if k=root then C i root else 0) := by
    by_cases hk : k=root
    · subst k; rw [hC.1 root]; simp
    · rw [hRow k hk,if_neg hk]; ring
  simp only [hTerm,Finset.sum_sub_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hDot
  rw [hCol i hi] at hDot
  linarith

theorem sign_pair_four_divides (x y : ℤ) (hx : x=1 ∨ x= -1) (hy : y=1 ∨ y= -1) :
    (4:ℤ) ∣ x+y+x*y+1 := by
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;> norm_num

theorem normalized_conference_skew {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℤ) (hC : IsDiagonalConferenceInt C) (hn : 4∣Fintype.card ι) (root : ι)
    (hRow : ∀ k, k≠root → C root k=1) (hCol : ∀ k, k≠root → C k root= -1) :
    C.transpose= -C := by
  have hN : (4:ℤ) ∣ (Fintype.card ι : ℤ) := by exact_mod_cast hn
  have hEntry (i j : ι) : C i j= -C j i := by
    by_cases hij : i=j
    · subst j; rw [hC.1 i]; ring
    by_cases hi : i=root
    · subst i; rw [hRow j (Ne.symm hij),hCol j (Ne.symm hij)]; norm_num
    by_cases hj : j=root
    · subst j; rw [hCol i hi,hRow i hi]
    have hSi := normalized_conference_row_sum C hC root hRow hCol i hi
    have hSj := normalized_conference_row_sum C hC root hRow hCol j hj
    have hDot := conference_offdiagonal_dot C hC i j hij
    let G : ι → ℤ := fun k => (C i k+C j k+C i k*C j k+1)-
      (if k=i then C j i+1 else 0)-(if k=j then C i j+1 else 0)
    have hG (k : ι) : (4:ℤ) ∣ G k := by
      by_cases hki : k=i
      · subst k; simp [G,hC.1 i,hij,Ne.symm hij]
      by_cases hkj : k=j
      · subst k; simp [G,hC.1 j,hij,Ne.symm hij]
      simp only [G,if_neg hki,if_neg hkj,sub_zero]
      exact sign_pair_four_divides _ _ (hC.2.1 i k (Ne.symm hki)) (hC.2.1 j k (Ne.symm hkj))
    have hSum : (∑ k, G k)=(Fintype.card ι : ℤ)-4-C i j-C j i := by
      simp only [G,Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_ite_eq',
        Finset.mem_univ,ite_true,hSi,hSj,hDot,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
      ring
    have hDiv := Finset.dvd_sum (fun k (_ : k∈Finset.univ) => hG k)
    rw [hSum] at hDiv
    rcases hC.2.1 i j hij with ha|ha <;> rcases hC.2.1 j i (Ne.symm hij) with hb|hb <;>
      rw [ha,hb] at hDiv ⊢ <;> omega
  ext i j
  exact hEntry j i

def switchedConference {ι : Type*} (C : Matrix ι ι ℤ) (r c : ι → ℤ) : Matrix ι ι ℤ :=
  fun i j => r i*C i j*c j

theorem int_sign_square (x : ℤ) (hx : x=1 ∨ x= -1) : x*x=1 := by
  rcases hx with rfl|rfl <;> norm_num

theorem switched_conference_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℤ) (r c : ι → ℤ) (hr : ∀ i, r i=1 ∨ r i= -1)
    (hc : ∀ i, c i=1 ∨ c i= -1) (w : ℤ)
    (hGram : C*C.transpose=w • (1 : Matrix ι ι ℤ)) :
    switchedConference C r c*(switchedConference C r c).transpose=w • (1 : Matrix ι ι ℤ) := by
  ext i j
  have hOld := congrArg (fun M : Matrix ι ι ℤ => M i j) hGram
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply] at hOld
  change (∑ k, (r i*C i k*c k)*(r j*C j k*c k))=w*(if i=j then 1 else 0)
  have hTerm (k : ι) : (r i*C i k*c k)*(r j*C j k*c k)=r i*r j*(C i k*C j k) := by
    rcases hc k with h|h <;> rw [h] <;> ring
  simp only [hTerm,← Finset.mul_sum,hOld]
  by_cases hij : i=j
  · subst j
    rcases hr i with h|h <;> simp [h]
  · simp [hij]

theorem switched_conference_valid {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℤ) (hC : IsDiagonalConferenceInt C) (r c : ι → ℤ)
    (hr : ∀ i, r i=1 ∨ r i= -1) (hc : ∀ i, c i=1 ∨ c i= -1) :
    IsDiagonalConferenceInt (switchedConference C r c) := by
  refine ⟨?_,?_,switched_conference_gram C r c hr hc _ hC.2.2⟩
  · intro i; simp [switchedConference,hC.1 i]
  · intro i j hij
    rcases hr i with h|h <;> rcases hc j with h'|h' <;>
      rcases hC.2.1 i j hij with h''|h'' <;> simp [switchedConference,h,h',h'']

def conferenceRowSigns {ι : Type*} [DecidableEq ι] (C : Matrix ι ι ℤ) (root : ι) (i : ι) : ℤ :=
  if i=root then 1 else -C i root

def conferenceColSigns {ι : Type*} [DecidableEq ι] (C : Matrix ι ι ℤ) (root : ι) (i : ι) : ℤ :=
  if i=root then 1 else C root i

theorem conference_normalizing_signs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℤ) (hC : IsDiagonalConferenceInt C) (root : ι) :
    (∀ i, conferenceRowSigns C root i=1 ∨ conferenceRowSigns C root i= -1) ∧
    (∀ i, conferenceColSigns C root i=1 ∨ conferenceColSigns C root i= -1) ∧
    (∀ j, j≠root → switchedConference C (conferenceRowSigns C root) (conferenceColSigns C root) root j=1) ∧
    (∀ i, i≠root → switchedConference C (conferenceRowSigns C root) (conferenceColSigns C root) i root= -1) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    by_cases hi : i=root
    · simp [conferenceRowSigns,hi]
    · rcases hC.2.1 i root hi with h|h <;> simp [conferenceRowSigns,hi,h]
  · intro i
    by_cases hi : i=root
    · simp [conferenceColSigns,hi]
    · rcases hC.2.1 root i (Ne.symm hi) with h|h <;> simp [conferenceColSigns,hi,h]
  · intro j hj
    rcases hC.2.1 root j (Ne.symm hj) with h|h <;>
      simp [switchedConference,conferenceRowSigns,conferenceColSigns,hj,h]
  · intro i hi
    rcases hC.2.1 i root hi with h|h <;>
      simp [switchedConference,conferenceRowSigns,conferenceColSigns,hi,h]

theorem conference_row_sign_skew {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℤ) (hC : IsDiagonalConferenceInt C) (hn : 4∣Fintype.card ι) (root : ι) :
    ∃ d : ι → ℤ, (∀ i, d i=1 ∨ d i= -1) ∧
      (switchedConference C d (fun _ => 1)).transpose= -switchedConference C d (fun _ => 1) := by
  have h := conference_normalizing_signs C hC root
  let r := conferenceRowSigns C root
  let c := conferenceColSigns C root
  let B := switchedConference C r c
  have hB : IsDiagonalConferenceInt B := switched_conference_valid C hC r c h.1 h.2.1
  have hSkew := normalized_conference_skew B hB hn root h.2.2.1 h.2.2.2
  refine ⟨fun i => r i*c i,?_,?_⟩
  · intro i
    rcases h.1 i with hi|hi <;> rcases h.2.1 i with hi'|hi' <;>
      change r i*c i=1 ∨ r i*c i= -1 <;> simp_all [r,c]
  · ext i j
    have hEntry := congrArg (fun M : Matrix ι ι ℤ => M i j) hSkew
    change r j*C j i*c i= -(r i*C i j*c j) at hEntry
    change (r j*c j)*C j i*1= -((r i*c i)*C i j*1)
    have hci : c i=1 ∨ c i= -1 := h.2.1 i
    have hcj : c j=1 ∨ c j= -1 := h.2.1 j
    rcases hci with hci|hci <;> rcases hcj with hcj|hcj <;> rw [hci,hcj] at hEntry ⊢ <;> nlinarith only [hEntry]

theorem skew_conference_plus_minus_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Matrix ι ι ℤ) (hGram : V*V.transpose=((Fintype.card ι : ℤ)-1) • (1 : Matrix ι ι ℤ))
    (hSkew : V.transpose= -V) :
    (V+1)*(V+1).transpose=(Fintype.card ι : ℤ) • (1 : Matrix ι ι ℤ) ∧
    (V-1)*(V-1).transpose=(Fintype.card ι : ℤ) • (1 : Matrix ι ι ℤ) := by
  have hSum : ((Fintype.card ι : ℤ)-1) • (1 : Matrix ι ι ℤ)+1=(Fintype.card ι : ℤ) • (1 : Matrix ι ι ℤ) := by
    ext i j
    simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
    split_ifs <;> ring
  constructor
  · calc
      _=V*V.transpose+V+V.transpose+1 := by rw [Matrix.transpose_add,Matrix.transpose_one]; noncomm_ring
      _=((Fintype.card ι : ℤ)-1) • (1 : Matrix ι ι ℤ)+1 := by rw [hGram,hSkew]; abel
      _=_ := hSum
  · calc
      _=V*V.transpose-V-V.transpose+1 := by rw [Matrix.transpose_sub,Matrix.transpose_one]; noncomm_ring
      _=((Fintype.card ι : ℤ)-1) • (1 : Matrix ι ι ℤ)+1 := by rw [hGram,hSkew]; abel
      _=_ := hSum

theorem conference_sign_switch_undo {ι : Type*} [DecidableEq ι]
    (C : Matrix ι ι ℤ) (d : ι → ℤ) (hd : ∀ i, d i=1 ∨ d i= -1) (ε : ℤ) :
    switchedConference (switchedConference C d (fun _ => 1)+ε • (1 : Matrix ι ι ℤ)) d (fun _ => 1)=
      C+ε • Matrix.diagonal d := by
  ext i j
  simp only [switchedConference,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.one_apply,Matrix.diagonal_apply,mul_one]
  by_cases hij : i=j
  · subst j
    simp only [ite_true]
    rcases hd i with h|h <;> rw [h] <;> ring
  · simp only [if_neg hij]
    rcases hd i with h|h <;> rw [h] <;> ring

theorem integer_sign_gram_hadamard {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (H : Matrix ι ι ℤ) (hSign : ∀ i j, H i j=1 ∨ H i j= -1)
    (hGram : H*H.transpose=(Fintype.card ι : ℤ) • (1 : Matrix ι ι ℤ)) : Matrix.IsHadamard H := by
  apply Matrix.IsHadamard.of_mul_conjTranspose
  · intro i j
    exact Unitary.mem_iff_eq_one_or_eq_neg_one.mpr (hSign i j)
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hGram
  · apply isRegular_iff_ne_zero.mpr
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι≠0)

theorem conference_signed_diagonal_fill_int {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℤ) (hC : IsDiagonalConferenceInt C) (hn : 4∣Fintype.card ι) (root : ι) :
    ∃ d : ι → ℤ, (∀ i, d i=1 ∨ d i= -1) ∧
      Matrix.IsHadamard (C+Matrix.diagonal d) ∧ Matrix.IsHadamard (C-Matrix.diagonal d) := by
  letI : Nonempty ι := ⟨root⟩
  obtain ⟨d,hd,hSkew⟩ := conference_row_sign_skew C hC hn root
  let V := switchedConference C d (fun _ => 1)
  have hVGram : V*V.transpose=((Fintype.card ι : ℤ)-1) • (1 : Matrix ι ι ℤ) :=
    switched_conference_gram C d (fun _ => 1) hd (fun _ => Or.inl rfl) _ hC.2.2
  have hBoth := skew_conference_plus_minus_gram V hVGram hSkew
  have hSigns (ε : ℤ) (hε : ε=1 ∨ ε= -1) :
      ∀ i j, (C+ε • Matrix.diagonal d) i j=1 ∨ (C+ε • Matrix.diagonal d) i j= -1 := by
    intro i j
    by_cases hij : i=j
    · subst j
      rcases hd i with hi|hi <;> rcases hε with hε|hε <;>
        simp [hC.1 i,Matrix.diagonal_apply,hi,hε]
    · simpa only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.diagonal_apply,
        if_neg hij,mul_zero,add_zero] using hC.2.1 i j hij
  have hPlus : (C+Matrix.diagonal d)*(C+Matrix.diagonal d).transpose=
      (Fintype.card ι : ℤ) • (1 : Matrix ι ι ℤ) := by
    have h := switched_conference_gram (V+1) d (fun _ => 1) hd (fun _ => Or.inl rfl) _ hBoth.1
    have hUndo : switchedConference (V+1) d (fun _ => 1)=C+Matrix.diagonal d := by
      simpa only [one_smul] using conference_sign_switch_undo C d hd 1
    rwa [hUndo] at h
  have hMinus : (C-Matrix.diagonal d)*(C-Matrix.diagonal d).transpose=
      (Fintype.card ι : ℤ) • (1 : Matrix ι ι ℤ) := by
    have h := switched_conference_gram (V-1) d (fun _ => 1) hd (fun _ => Or.inl rfl) _ hBoth.2
    have hUndo : switchedConference (V-1) d (fun _ => 1)=C-Matrix.diagonal d := by
      simpa only [neg_one_smul,sub_eq_add_neg] using conference_sign_switch_undo C d hd (-1)
    rwa [hUndo] at h
  refine ⟨d,hd,integer_sign_gram_hadamard _ ?_ hPlus,integer_sign_gram_hadamard _ ?_ hMinus⟩
  · simpa only [one_smul] using hSigns 1 (Or.inl rfl)
  · simpa only [neg_one_smul,sub_eq_add_neg] using hSigns (-1) (Or.inr rfl)

theorem integer_smul_one_real_cast {ι : Type*} [DecidableEq ι] (w : ℤ) :
    (w • (1 : Matrix ι ι ℤ)).map (Int.castRingHom ℝ)=(w:ℝ) • (1 : Matrix ι ι ℝ) := by
  ext i j
  change (((w • (1 : Matrix ι ι ℤ)) i j : ℤ):ℝ)=((w:ℝ) • (1 : Matrix ι ι ℝ)) i j
  simp only [Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
  split_ifs <;> norm_num

theorem integer_gram_real_cast {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℤ) (w : ℤ) (h : H*H.transpose=w • (1 : Matrix ι ι ℤ)) :
    H.map (Int.castRingHom ℝ)*(H.map (Int.castRingHom ℝ)).transpose=(w:ℝ) • (1 : Matrix ι ι ℝ) := by
  have h' := congrArg (fun M : Matrix ι ι ℤ => M.map (Int.castRingHom ℝ)) h
  simpa only [Matrix.map_mul,← Matrix.transpose_map,integer_smul_one_real_cast] using h'

theorem integer_gram_of_real_cast {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℤ) (w : ℤ)
    (h : H.map (Int.castRingHom ℝ)*(H.map (Int.castRingHom ℝ)).transpose=(w:ℝ) • (1 : Matrix ι ι ℝ)) :
    H*H.transpose=w • (1 : Matrix ι ι ℤ) := by
  have hInjective : Function.Injective (fun M : Matrix ι ι ℤ => M.map (Int.castRingHom ℝ)) := by
    intro A B hAB
    ext i j
    have hEntry := congrArg (fun M : Matrix ι ι ℝ => M i j) hAB
    change (A i j : ℝ)=(B i j : ℝ) at hEntry
    exact_mod_cast hEntry
  apply hInjective
  simpa only [Matrix.map_mul,← Matrix.transpose_map,integer_smul_one_real_cast] using h

theorem integer_hadamard_real_cast {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℤ) (h : Matrix.IsHadamard H) : Matrix.IsHadamard (H.map (Int.castRingHom ℝ)) := by
  refine ⟨?_,?_,?_⟩
  · intro i j
    apply Unitary.mem_iff_eq_one_or_eq_neg_one.mpr
    have hSign := Unitary.mem_iff_eq_one_or_eq_neg_one.mp (h.apply_mem i j)
    rcases hSign with h1|h1
    · left; simpa only [Matrix.map_apply,h1,map_one]
    · right; simpa only [Matrix.map_apply,h1,map_neg,map_one]
  · have hGram : H*H.transpose=(Fintype.card ι : ℤ) • (1 : Matrix ι ι ℤ) := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using h.mul_conjTranspose
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Int.cast_natCast] using integer_gram_real_cast H _ hGram
  · have hGram : H.transpose*H.transpose.transpose=(Fintype.card ι : ℤ) • (1 : Matrix ι ι ℤ) := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_transpose] using h.conjTranspose_mul
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,← Matrix.transpose_map,Matrix.transpose_transpose,
      Int.cast_natCast] using integer_gram_real_cast H.transpose _ hGram

def IsDiagonalConferenceReal {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Matrix ι ι ℝ) : Prop :=
  (∀ i, C i i=0) ∧ (∀ i j, i≠j → C i j=1 ∨ C i j= -1) ∧
    C*C.transpose=((Fintype.card ι : ℝ)-1) • (1 : Matrix ι ι ℝ)

theorem conference_signed_diagonal_fill_real {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : IsDiagonalConferenceReal C) (hn : 4∣Fintype.card ι) (root : ι) :
    ∃ d : ι → ℝ, (∀ i, d i=1 ∨ d i= -1) ∧
      Matrix.IsHadamard (C+Matrix.diagonal d) ∧ Matrix.IsHadamard (C-Matrix.diagonal d) := by
  have hWeigh : IsWeighing C ((Fintype.card ι : ℝ)-1) := by
    refine ⟨?_,hC.2.2⟩
    intro i j
    by_cases hij : i=j
    · subst j; exact Or.inl (hC.1 i)
    · exact Or.inr (hC.2.1 i j hij)
  let CI := weighingIntegerModel C
  have hCast : CI.map (Int.castRingHom ℝ)=C := weighingIntegerModel_cast C _ hWeigh
  have hPoint (i j : ι) : (CI i j : ℝ)=C i j := congrArg (fun M : Matrix ι ι ℝ => M i j) hCast
  have hCI : IsDiagonalConferenceInt CI := by
    refine ⟨?_,?_,?_⟩
    · intro i; simp [CI,weighingIntegerModel,hC.1 i]
    · intro i j hij
      rcases hC.2.1 i j hij with h|h <;> norm_num [CI,weighingIntegerModel,h]
    · apply integer_gram_of_real_cast CI ((Fintype.card ι : ℤ)-1)
      simpa only [hCast,Int.cast_sub,Int.cast_natCast,Int.cast_one] using hC.2.2
  obtain ⟨d,hd,hPlus,hMinus⟩ := conference_signed_diagonal_fill_int CI hCI hn root
  have hPCast : (CI+Matrix.diagonal d).map (Int.castRingHom ℝ)=C+Matrix.diagonal (fun i => (d i : ℝ)) := by
    ext i j
    by_cases hij : i=j <;> simp [Matrix.map_apply,Matrix.add_apply,Matrix.diagonal_apply,hPoint,hij]
  have hMCast : (CI-Matrix.diagonal d).map (Int.castRingHom ℝ)=C-Matrix.diagonal (fun i => (d i : ℝ)) := by
    ext i j
    by_cases hij : i=j <;> simp [Matrix.map_apply,Matrix.sub_apply,Matrix.diagonal_apply,hPoint,hij]
  refine ⟨fun i => (d i : ℝ),?_,?_,?_⟩
  · intro i
    change (d i : ℝ)=1 ∨ (d i : ℝ)= -1
    rcases hd i with h|h <;> rw [h] <;> norm_num
  · rw [← hPCast]; exact integer_hadamard_real_cast _ hPlus
  · rw [← hMCast]; exact integer_hadamard_real_cast _ hMinus

def pairedFlip {ι : Type*} : (Fin 2×ι) ≃ (Fin 2×ι) where
  toFun p := (Fin.rev p.1,p.2)
  invFun p := (Fin.rev p.1,p.2)
  left_inv := by rintro ⟨a,i⟩; simp
  right_inv := by rintro ⟨a,i⟩; simp

theorem paired_flip_involution {ι : Type*} (p : Fin 2×ι) : pairedFlip (pairedFlip p)=p := by
  rcases p with ⟨a,i⟩; simp [pairedFlip]

theorem paired_flip_equality {ι : Type*} (p q : Fin 2×ι) : p=pairedFlip q ↔ q=pairedFlip p := by
  constructor
  · intro h; have hh := congrArg pairedFlip h; simpa only [paired_flip_involution] using hh.symm
  · intro h; have hh := congrArg pairedFlip h; simpa only [paired_flip_involution] using hh.symm

noncomputable def pairedMatchingFill {ι : Type*} [DecidableEq ι] (d : (Fin 2×ι) → ℝ) :
    Matrix (Fin 2×ι) (Fin 2×ι) ℝ := fun p q => if q=pairedFlip p then d p else 0

theorem diagonal_paired_pullback {ι : Type*} [DecidableEq ι] (d : (Fin 2×ι) → ℝ) :
    (Matrix.diagonal d).submatrix id pairedFlip=pairedMatchingFill d := by
  ext p q
  simp only [Matrix.submatrix_apply,Matrix.diagonal_apply,id_eq,pairedMatchingFill,paired_flip_equality]

theorem paired_pullback_twice {ι : Type*} (U : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) :
    (U.submatrix id pairedFlip).submatrix id pairedFlip=U := by
  ext p q; simp only [Matrix.submatrix_apply,id_eq,paired_flip_involution]

theorem paired_fill_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : (Fin 2×ι) → ℝ) (hd : ∀ p, d p=1 ∨ d p= -1) :
    pairedMatchingFill d*(pairedMatchingFill d).transpose=1 := by
  ext p q
  simp only [Matrix.mul_apply,Matrix.transpose_apply,pairedMatchingFill]
  simp only [ite_mul,mul_ite,zero_mul,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have hEq : (pairedFlip p=pairedFlip q) ↔ p=q := pairedFlip.injective.eq_iff
  simp only [hEq,Matrix.one_apply]
  by_cases hpq : p=q
  · subst q; rcases hd p with h|h <;> simp [h]
  · simp [hpq,Ne.symm hpq]

theorem mul_paired_fill_transpose_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) (d : (Fin 2×ι) → ℝ) (p q : Fin 2×ι) :
    (U*(pairedMatchingFill d).transpose) p q=U p (pairedFlip q)*d q := by
  simp [Matrix.mul_apply,Matrix.transpose_apply,pairedMatchingFill,mul_ite]

theorem paired_fill_mul_transpose_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) (d : (Fin 2×ι) → ℝ) (p q : Fin 2×ι) :
    (pairedMatchingFill d*U.transpose) p q=d p*U q (pairedFlip p) := by
  simp [Matrix.mul_apply,Matrix.transpose_apply,pairedMatchingFill,ite_mul]

theorem paired_conference_permuted {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) (hBlock : ∀ i, twoBlock U i i=1)
    (hOff : ∀ i j, i≠j → ∀ a b : Fin 2, U (a,i) (b,j)=1 ∨ U (a,i) (b,j)= -1)
    (hGram : U*U.transpose=((Fintype.card (Fin 2×ι) : ℝ)-1) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ)) :
    IsDiagonalConferenceReal (U.submatrix id pairedFlip) := by
  refine ⟨?_,?_,?_⟩
  · rintro ⟨a,i⟩
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M a (Fin.rev a)) (hBlock i)
    fin_cases a <;> simpa [twoBlock,pairedFlip,Fin.rev] using h
  · rintro ⟨a,i⟩ ⟨b,j⟩ hpq
    by_cases hij : i=j
    · subst j
      have hEntry (a b : Fin 2) : U (a,i) (Fin.rev b,i)=(1 : Matrix (Fin 2) (Fin 2) ℝ) a (Fin.rev b) :=
        congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M a (Fin.rev b)) (hBlock i)
      fin_cases a
      · fin_cases b
        · exact False.elim (hpq rfl)
        · left; simpa [pairedFlip,Fin.rev, Matrix.one_apply] using hEntry 0 1
      · fin_cases b
        · left; simpa [pairedFlip,Fin.rev, Matrix.one_apply] using hEntry 1 0
        · exact False.elim (hpq rfl)
    · change U (a,i) (Fin.rev b,j)=1 ∨ U (a,i) (Fin.rev b,j)= -1
      exact hOff i j hij a (Fin.rev b)
  · change (U.submatrix id pairedFlip)*(U.transpose.submatrix pairedFlip id)=_
    rw [Matrix.submatrix_mul_equiv]
    exact hGram

theorem paired_conference_fills {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) (hBlock : ∀ i, twoBlock U i i=1)
    (hOff : ∀ i j, i≠j → ∀ a b : Fin 2, U (a,i) (b,j)=1 ∨ U (a,i) (b,j)= -1)
    (hGram : U*U.transpose=((Fintype.card (Fin 2×ι) : ℝ)-1) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (hn : 4∣Fintype.card (Fin 2×ι)) (root : ι) :
    ∃ d : (Fin 2×ι) → ℝ, (∀ p, d p=1 ∨ d p= -1) ∧
      Matrix.IsHadamard (U+pairedMatchingFill d) ∧ Matrix.IsHadamard (U-pairedMatchingFill d) := by
  let U' := U.submatrix id pairedFlip
  have hU' := paired_conference_permuted U hBlock hOff hGram
  obtain ⟨d,hd,hPlus,hMinus⟩ := conference_signed_diagonal_fill_real U' hU' hn (0,root)
  have hPU : U'.submatrix id pairedFlip=U := paired_pullback_twice U
  have hPD := diagonal_paired_pullback d
  have hPlusPull : (U'+Matrix.diagonal d).submatrix id pairedFlip=U+pairedMatchingFill d := by
    ext p q
    exact congrArg₂ (fun x y : ℝ => x+y)
      (congrArg (fun M : Matrix (Fin 2×ι) (Fin 2×ι) ℝ => M p q) hPU)
      (congrArg (fun M : Matrix (Fin 2×ι) (Fin 2×ι) ℝ => M p q) hPD)
  have hMinusPull : (U'-Matrix.diagonal d).submatrix id pairedFlip=U-pairedMatchingFill d := by
    ext p q
    exact congrArg₂ (fun x y : ℝ => x-y)
      (congrArg (fun M : Matrix (Fin 2×ι) (Fin 2×ι) ℝ => M p q) hPU)
      (congrArg (fun M : Matrix (Fin 2×ι) (Fin 2×ι) ℝ => M p q) hPD)
  have hP := (Matrix.isHadamard_submatrix_equiv_iff (Equiv.refl (Fin 2×ι)) pairedFlip).mpr hPlus
  have hM := (Matrix.isHadamard_submatrix_equiv_iff (Equiv.refl (Fin 2×ι)) pairedFlip).mpr hMinus
  change Matrix.IsHadamard ((U'+Matrix.diagonal d).submatrix id pairedFlip) at hP
  change Matrix.IsHadamard ((U'-Matrix.diagonal d).submatrix id pairedFlip) at hM
  rw [hPlusPull] at hP
  rw [hMinusPull] at hM
  exact ⟨d,hd,hP,hM⟩


theorem paired_hadamard_cross_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U Y : Matrix (Fin 2×ι) (Fin 2×ι) ℝ)
    (hP : Matrix.IsHadamard (U+Y)) (hM : Matrix.IsHadamard (U-Y)) :
    U*Y.transpose+Y*U.transpose=0 := by
  have hp : (U+Y)*(U+Y).transpose=(Fintype.card (Fin 2×ι) : ℝ) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hP.mul_conjTranspose
  have hm : (U-Y)*(U-Y).transpose=(Fintype.card (Fin 2×ι) : ℝ) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hM.mul_conjTranspose
  have he : (U*Y.transpose+Y*U.transpose)+(U*Y.transpose+Y*U.transpose)=0 := by
    calc
      _=(U+Y)*(U+Y).transpose-(U-Y)*(U-Y).transpose := by
        rw [Matrix.transpose_add,Matrix.transpose_sub]; noncomm_ring
      _=0 := by rw [hp,hm,sub_self]
  ext p q
  have h := congrArg (fun M : Matrix (Fin 2×ι) (Fin 2×ι) ℝ => M p q) he
  simp only [Matrix.add_apply,Matrix.zero_apply] at h ⊢
  linarith

theorem paired_hadamard_fill_skew {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) (d : (Fin 2×ι) → ℝ)
    (hBlock : ∀ i, twoBlock U i i=1)
    (hP : Matrix.IsHadamard (U+pairedMatchingFill d))
    (hM : Matrix.IsHadamard (U-pairedMatchingFill d)) :
    (∀ p, d (pairedFlip p)= -d p) ∧ (pairedMatchingFill d).transpose= -pairedMatchingFill d := by
  have hCross := paired_hadamard_cross_zero U (pairedMatchingFill d) hP hM
  have hDiag (p : Fin 2×ι) : U p p=1 := by
    rcases p with ⟨a,i⟩
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M a a) (hBlock i)
    simpa [twoBlock,Matrix.one_apply] using h
  have hNeg (p : Fin 2×ι) : d (pairedFlip p)= -d p := by
    have h := congrArg (fun M : Matrix (Fin 2×ι) (Fin 2×ι) ℝ => M p (pairedFlip p)) hCross
    simp only [Matrix.add_apply,Matrix.zero_apply,mul_paired_fill_transpose_entry,
      paired_fill_mul_transpose_entry,paired_flip_involution,hDiag,one_mul,mul_one] at h
    linarith
  refine ⟨hNeg,?_⟩
  ext p q
  by_cases hq : q=pairedFlip p
  · subst q
    simp [Matrix.transpose_apply,pairedMatchingFill,paired_flip_involution,hNeg]
  · have hp : p≠pairedFlip q := by
      intro hp
      apply hq
      rw [hp,paired_flip_involution]
    simp [Matrix.transpose_apply,pairedMatchingFill,hq,hp]


def diagonalRootInt (p e : Bool) : Matrix (Fin 2) (Fin 2) ℤ :=
  twoPlaneMatrix p 1 (if e then -1 else 1)
noncomputable def diagonalRootReal (p e : Bool) : Matrix (Fin 2) (Fin 2) ℝ :=
  twoPlaneMatrix p 1 (if e then -1 else 1)

theorem diagonal_root_walsh_state_int : ∀ p e : Bool, ∃ d : SignedTwoState,
    diagonalRootInt p e*walshTwoInt=(2:ℤ) • signedTwoInt d := by decide +kernel

theorem propagated_diagonal_walsh_state_int : ∀ (p e : Bool) (a b : SignedTwoState), ∃ d : SignedTwoState,
    (-signedTwoInt a*(diagonalRootInt p e).transpose*signedTwoInt b)*walshTwoInt=
      (2:ℤ) • signedTwoInt d := by decide +kernel

theorem diagonal_root_real_cast (p e : Bool) :
    (diagonalRootInt p e).map (Int.castRingHom ℝ)=diagonalRootReal p e := by
  cases p <;> cases e <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [diagonalRootInt,diagonalRootReal,twoPlaneMatrix]

theorem two_signed_state_real_cast (d : SignedTwoState) :
    ((2:ℤ) • signedTwoInt d).map (Int.castRingHom ℝ)=(2:ℝ) • signedTwoReal d := by
  ext i j
  change (((2:ℤ) • signedTwoInt d) i j : ℝ)=((2:ℝ) • signedTwoReal d) i j
  simp only [Matrix.smul_apply,smul_eq_mul,signedTwoReal,Matrix.map_apply]
  push_cast
  rfl

theorem neg_signed_state_real_cast (d : SignedTwoState) :
    (-signedTwoInt d).map (Int.castRingHom ℝ)= -signedTwoReal d := by
  ext i j
  simp [signedTwoReal]

theorem diagonal_root_transpose_real_cast (p e : Bool) :
    (diagonalRootInt p e).transpose.map (Int.castRingHom ℝ)=(diagonalRootReal p e).transpose := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M.transpose) (diagonal_root_real_cast p e)
  simpa only [Matrix.transpose_map] using h

theorem diagonal_root_walsh_state_real (p e : Bool) : ∃ d : SignedTwoState,
    diagonalRootReal p e*walshTwoReal=(2:ℝ) • signedTwoReal d := by
  obtain ⟨d,hd⟩ := diagonal_root_walsh_state_int p e
  refine ⟨d,?_⟩
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (Int.castRingHom ℝ)) hd
  simpa only [Matrix.map_mul,diagonal_root_real_cast,two_signed_state_real_cast,walshTwoReal,signedTwoReal] using h

theorem propagated_diagonal_walsh_state_real (p e : Bool) (a b : SignedTwoState) : ∃ d : SignedTwoState,
    (-signedTwoReal a*(diagonalRootReal p e).transpose*signedTwoReal b)*walshTwoReal=
      (2:ℝ) • signedTwoReal d := by
  obtain ⟨d,hd⟩ := propagated_diagonal_walsh_state_int p e a b
  refine ⟨d,?_⟩
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (Int.castRingHom ℝ)) hd
  simpa only [Matrix.map_mul,diagonal_root_transpose_real_cast,two_signed_state_real_cast,
    neg_signed_state_real_cast,walshTwoReal,signedTwoReal] using h

theorem forced_diagonal_family_states {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (p e : Bool) :
    ∃ T : ι → SignedTwoState, ∀ i,
      forcedRealTwo A root (diagonalRootReal p e) i*walshTwoReal=(2:ℝ) • signedTwoReal (T i) := by
  classical
  have h (i : ι) : ∃ d : SignedTwoState,
      forcedRealTwo A root (diagonalRootReal p e) i*walshTwoReal=(2:ℝ) • signedTwoReal d := by
    by_cases hi : i=root
    · simpa only [forcedRealTwo,if_pos hi] using diagonal_root_walsh_state_real p e
    · simpa only [forcedRealTwo,if_neg hi] using propagated_diagonal_walsh_state_real p e (A i root) (A root i)
  choose T hT using h
  exact ⟨T,hT⟩

theorem walsh_two_real_symmetric : walshTwoReal.transpose=walshTwoReal := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [walshTwoReal,walshTwoInt]

theorem right_walsh_signed_state_coherent (M : Matrix (Fin 2) (Fin 2) ℝ) (d : SignedTwoState)
    (h : M*walshTwoReal=(2:ℝ) • signedTwoReal d) : M=signedTwoReal d*walshTwoReal := by
  have hSquare : walshTwoReal*walshTwoReal=(2:ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    simpa only [walsh_two_real_symmetric] using walshTwoReal_gram
  have hLeft : (M*walshTwoReal)*walshTwoReal=(2:ℝ) • M := by
    rw [Matrix.mul_assoc,hSquare,Matrix.mul_smul,Matrix.mul_one]
  have hh := congrArg (fun N : Matrix (Fin 2) (Fin 2) ℝ => N*walshTwoReal) h
  rw [hLeft,Matrix.smul_mul] at hh
  ext a b
  have he := congrArg (fun N : Matrix (Fin 2) (Fin 2) ℝ => N a b) hh
  change (2:ℝ)*M a b=2*(signedTwoReal d*walshTwoReal) a b at he
  linarith

theorem forced_diagonal_family_coherent {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (p e : Bool) :
    ∃ T : ι → SignedTwoState, ∀ i,
      forcedRealTwo A root (diagonalRootReal p e) i=signedTwoReal (T i)*walshTwoReal := by
  obtain ⟨T,hT⟩ := forced_diagonal_family_states A root p e
  exact ⟨T,fun i => right_walsh_signed_state_coherent _ _ (hT i)⟩

noncomputable def signedTwoBlockDiagonal {ι : Type*} [DecidableEq ι] (T : ι → SignedTwoState) :
    Matrix (Fin 2×ι) (Fin 2×ι) ℝ := Matrix.blockDiagonal (fun i => signedTwoReal (T i))

theorem signed_two_block_diagonal_orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → SignedTwoState) :
    signedTwoBlockDiagonal T*(signedTwoBlockDiagonal T).transpose=1 ∧
      (signedTwoBlockDiagonal T).transpose*signedTwoBlockDiagonal T=1 := by
  constructor
  · calc
      _=Matrix.blockDiagonal (fun i => signedTwoReal (T i)*(signedTwoReal (T i)).transpose) := by
        rw [signedTwoBlockDiagonal,Matrix.blockDiagonal_transpose,← Matrix.blockDiagonal_mul]
      _=Matrix.blockDiagonal (1 : ι → Matrix (Fin 2) (Fin 2) ℝ) := by
        congr 1; funext i; exact (signed_two_real_orthogonal (T i)).1
      _=1 := Matrix.blockDiagonal_one
  · calc
      _=Matrix.blockDiagonal (fun i => (signedTwoReal (T i)).transpose*signedTwoReal (T i)) := by
        rw [signedTwoBlockDiagonal,Matrix.blockDiagonal_transpose,← Matrix.blockDiagonal_mul]
      _=Matrix.blockDiagonal (1 : ι → Matrix (Fin 2) (Fin 2) ℝ) := by
        congr 1; funext i; exact (signed_two_real_orthogonal (T i)).2
      _=1 := Matrix.blockDiagonal_one

theorem root_family_block_anticommutator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (hR : realRootConsistency A root R) (T : ι → SignedTwoState)
    (hT : ∀ i, forcedRealTwo A root R i=signedTwoReal (T i)*walshTwoReal) :
    normalizedTwoReal A*(signedTwoBlockDiagonal T).transpose+
      signedTwoBlockDiagonal T*(normalizedTwoReal A).transpose=0 := by
  ext ⟨a,i⟩ ⟨b,j⟩
  simp only [signedTwoBlockDiagonal,Matrix.add_apply]
  rw [mul_blockDiagonal_transpose_entry,blockDiagonal_mul_transpose_entry]
  by_cases hij : i=j
  · subst j; rw [normalizedTwoReal_diagonal]; simp
  · rw [normalizedTwoReal_offdiagonal A i j hij,normalizedTwoReal_offdiagonal A j i (Ne.symm hij)]
    have hc := hR i j hij
    rw [hT i,hT j] at hc
    have hCross : (signedTwoReal (A i j)*walshTwoReal)*(signedTwoReal (T j)).transpose+
        signedTwoReal (T i)*(signedTwoReal (A j i)*walshTwoReal).transpose=0 := by
      simpa only [Matrix.transpose_mul,walsh_two_real_symmetric,Matrix.mul_assoc] using hc
    exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M a b) hCross

theorem orthogonal_switch_skew_gram {ν : Type*} [Fintype ν] [DecidableEq ν]
    (W T : Matrix ν ν ℝ) (w : ℝ) (hT : T.transpose*T=1)
    (hGram : W*W.transpose=w • (1 : Matrix ν ν ℝ))
    (hAnti : W*T.transpose+T*W.transpose=0) :
    (W*T.transpose).transpose= -(W*T.transpose) ∧
      (W*T.transpose)*(W*T.transpose).transpose=w • (1 : Matrix ν ν ℝ) := by
  constructor
  · apply eq_neg_of_add_eq_zero_left
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,add_comm] using hAnti
  · rw [Matrix.transpose_mul,Matrix.transpose_transpose]
    calc
      _=W*(T.transpose*T)*W.transpose := by noncomm_ring
      _=w • (1 : Matrix ν ν ℝ) := by rw [hT]; simpa only [Matrix.mul_one] using hGram


theorem signed_walsh_product_sign_int : ∀ (a b : SignedTwoState) (i j : Fin 2),
    (signedTwoInt a*walshTwoInt*(signedTwoInt b).transpose) i j=1 ∨
      (signedTwoInt a*walshTwoInt*(signedTwoInt b).transpose) i j= -1 := by decide +kernel

theorem signed_walsh_product_sign_real (a b : SignedTwoState) (i j : Fin 2) :
    (signedTwoReal a*walshTwoReal*(signedTwoReal b).transpose) i j=1 ∨
      (signedTwoReal a*walshTwoReal*(signedTwoReal b).transpose) i j= -1 := by
  have hCast : (signedTwoInt a*walshTwoInt*(signedTwoInt b).transpose).map (Int.castRingHom ℝ)=
      signedTwoReal a*walshTwoReal*(signedTwoReal b).transpose := by
    simp only [Matrix.map_mul,← Matrix.transpose_map,signedTwoReal,walshTwoReal]
  have hp := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M i j) hCast
  rcases signed_walsh_product_sign_int a b i j with h|h
  · left; rw [← hp]; change ((signedTwoInt a*walshTwoInt*(signedTwoInt b).transpose) i j : ℝ)=1
    rw [h]; norm_num
  · right; rw [← hp]; change ((signedTwoInt a*walshTwoInt*(signedTwoInt b).transpose) i j : ℝ)= -1
    rw [h]; norm_num

theorem switched_normalized_two_blocks {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (T : ι → SignedTwoState) :
    (∀ i, twoBlock (normalizedTwoReal A*(signedTwoBlockDiagonal T).transpose) i i=0) ∧
    (∀ i j, i≠j → ∀ a b : Fin 2,
      (normalizedTwoReal A*(signedTwoBlockDiagonal T).transpose) (a,i) (b,j)=1 ∨
      (normalizedTwoReal A*(signedTwoBlockDiagonal T).transpose) (a,i) (b,j)= -1) := by
  constructor
  · intro i
    ext a b
    change (normalizedTwoReal A*(Matrix.blockDiagonal (fun j => signedTwoReal (T j))).transpose) (a,i) (b,i)=0
    rw [mul_blockDiagonal_transpose_entry,normalizedTwoReal_diagonal]
    simp
  · intro i j hij a b
    change (normalizedTwoReal A*(Matrix.blockDiagonal (fun j => signedTwoReal (T j))).transpose) (a,i) (b,j)=1 ∨
      (normalizedTwoReal A*(Matrix.blockDiagonal (fun j => signedTwoReal (T j))).transpose) (a,i) (b,j)= -1
    rw [mul_blockDiagonal_transpose_entry,normalizedTwoReal_offdiagonal A i j hij]
    exact signed_walsh_product_sign_real (A i j) (T j) a b

theorem skew_add_identity_gram {ν : Type*} [Fintype ν] [DecidableEq ν]
    (C : Matrix ν ν ℝ) (w : ℝ) (hSkew : C.transpose= -C)
    (hGram : C*C.transpose=w • (1 : Matrix ν ν ℝ)) :
    (C+1)*(C+1).transpose=(w+1) • (1 : Matrix ν ν ℝ) := by
  calc
    _=C*C.transpose+(1 : Matrix ν ν ℝ) := by
      rw [Matrix.transpose_add,Matrix.transpose_one]
      have hc : C+C.transpose=0 := by rw [hSkew]; exact add_neg_cancel C
      calc
        _=C*C.transpose+(C+C.transpose)+1 := by noncomm_ring
        _=_ := by rw [hc,add_zero]
    _=(w+1) • (1 : Matrix ν ν ℝ) := by rw [hGram,add_smul,one_smul]


theorem diagonal_root_paired_skew_fills {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (p e : Bool)
    (hR : realRootConsistency A root (diagonalRootReal p e))
    (hW : normalizedTwoReal A*(normalizedTwoReal A).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (hn : 4∣Fintype.card (Fin 2×ι)) :
    ∃ T : ι → SignedTwoState, ∃ d : (Fin 2×ι) → ℝ,
      (∀ i, forcedRealTwo A root (diagonalRootReal p e) i=signedTwoReal (T i)*walshTwoReal) ∧
      (∀ q, d q=1 ∨ d q= -1) ∧ (∀ q, d (pairedFlip q)= -d q) ∧
      (pairedMatchingFill d).transpose= -pairedMatchingFill d ∧
      Matrix.IsHadamard (normalizedTwoReal A*(signedTwoBlockDiagonal T).transpose+1+pairedMatchingFill d) ∧
      Matrix.IsHadamard (normalizedTwoReal A*(signedTwoBlockDiagonal T).transpose+1-pairedMatchingFill d) := by
  obtain ⟨T,hT⟩ := forced_diagonal_family_coherent A root p e
  let C := normalizedTwoReal A*(signedTwoBlockDiagonal T).transpose
  have hAnti := root_family_block_anticommutator A root (diagonalRootReal p e) hR T hT
  obtain ⟨hSkew,hGram⟩ := orthogonal_switch_skew_gram (normalizedTwoReal A) (signedTwoBlockDiagonal T)
    ((Fintype.card (Fin 2×ι) : ℝ)-2) (signed_two_block_diagonal_orthogonal T).2 hW hAnti
  have hBlocks := switched_normalized_two_blocks A T
  have hUBlock (i : ι) : twoBlock (C+1) i i=1 := by
    ext a b
    have hz := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M a b) (hBlocks.1 i)
    change C (a,i) (b,i)=0 at hz
    change C (a,i) (b,i)+(1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) (a,i) (b,i)=_
    simp [hz,Matrix.one_apply,Prod.mk.injEq]
  have hUOff (i j : ι) (hij : i≠j) (a b : Fin 2) :
      (C+1) (a,i) (b,j)=1 ∨ (C+1) (a,i) (b,j)= -1 := by
    have hneq : (a,i)≠(b,j) := by intro h; exact hij (congrArg Prod.snd h)
    simpa only [Matrix.add_apply,Matrix.one_apply,if_neg hneq,add_zero] using hBlocks.2 i j hij a b
  have hUGram : (C+1)*(C+1).transpose=((Fintype.card (Fin 2×ι) : ℝ)-1) •
      (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) := by
    have h := skew_add_identity_gram C _ hSkew hGram
    convert h using 1 <;> congr 1 <;> ring
  obtain ⟨d,hd,hP,hM⟩ := paired_conference_fills (C+1) hUBlock hUOff hUGram hn root
  obtain ⟨hNeg,hYSkew⟩ := paired_hadamard_fill_skew (C+1) d hUBlock hP hM
  exact ⟨T,d,hT,hd,hNeg,hYSkew,hP,hM⟩


noncomputable def pairedSmallFill {ι : Type*} (d : (Fin 2×ι) → ℝ) (i : ι) :
    Matrix (Fin 2) (Fin 2) ℝ := !![0,d (0,i);d (1,i),0]

theorem paired_fill_block_diagonal {ι : Type*} [DecidableEq ι] (d : (Fin 2×ι) → ℝ) :
    pairedMatchingFill d=Matrix.blockDiagonal (pairedSmallFill d) := by
  ext ⟨a,i⟩ ⟨b,j⟩
  by_cases hij : i=j
  · subst j
    fin_cases a <;> fin_cases b <;>
      simp [pairedMatchingFill,pairedFlip,pairedSmallFill,Matrix.blockDiagonal,Fin.rev]
  · simp [pairedMatchingFill,pairedFlip,Matrix.blockDiagonal,Prod.mk.injEq,hij,Ne.symm hij]

theorem switched_fill_anticommutator {ν : Type*} [Fintype ν] [DecidableEq ν]
    (W T Y : Matrix ν ν ℝ) (hTT : T.transpose*T=1)
    (hY : Y.transpose= -Y)
    (hCross : (W*T.transpose+1)*Y.transpose+Y*(W*T.transpose+1).transpose=0) :
    W*(Y*T).transpose+(Y*T)*W.transpose=0 := by
  have hh : W*(Y*T).transpose+(Y*T)*W.transpose=
      ((W*T.transpose+1)*Y.transpose+Y*(W*T.transpose+1).transpose)-(Y.transpose+Y) := by
    rw [Matrix.transpose_mul,Matrix.transpose_add,Matrix.transpose_one,Matrix.transpose_mul,Matrix.transpose_transpose]
    noncomm_ring
  rw [hh,hCross,hY,neg_add_cancel,sub_self]

theorem block_anticommutator_real_family {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (V : ι → Matrix (Fin 2) (Fin 2) ℝ)
    (h : normalizedTwoReal A*(Matrix.blockDiagonal V).transpose+
      Matrix.blockDiagonal V*(normalizedTwoReal A).transpose=0) :
    ∀ i j, i≠j → signedTwoReal (A i j)*(V j*walshTwoReal).transpose+
      (V i*walshTwoReal)*(signedTwoReal (A j i)).transpose=0 := by
  intro i j hij
  ext a b
  have he := congrArg (fun M : Matrix (Fin 2×ι) (Fin 2×ι) ℝ => M (a,i) (b,j)) h
  simp only [Matrix.add_apply,Matrix.zero_apply] at he
  rw [mul_blockDiagonal_transpose_entry,blockDiagonal_mul_transpose_entry,
    normalizedTwoReal_offdiagonal A i j hij,normalizedTwoReal_offdiagonal A j i (Ne.symm hij)] at he
  simpa only [Matrix.add_apply,Matrix.zero_apply,Matrix.transpose_mul,walsh_two_real_symmetric,
    Matrix.mul_assoc] using he

theorem real_consistent_family_forced {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (R : ι → Matrix (Fin 2) (Fin 2) ℝ)
    (h : ∀ i j, i≠j → signedTwoReal (A i j)*(R j).transpose+
      R i*(signedTwoReal (A j i)).transpose=0) :
    realRootConsistency A root (R root) := by
  have heq (i : ι) : R i=forcedRealTwo A root (R root) i := by
    by_cases hi : i=root
    · subst i; simp [forcedRealTwo]
    · rw [forcedRealTwo,if_neg hi]
      have ht := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M.transpose) (h root i (Ne.symm hi))
      simp only [Matrix.transpose_add,Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_zero] at ht
      have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M*signedTwoReal (A root i)) ht
      simp only [Matrix.add_mul,Matrix.zero_mul,Matrix.mul_assoc,(signed_two_real_orthogonal (A root i)).2,Matrix.mul_one] at hh
      have he := eq_neg_of_add_eq_zero_left hh
      simpa only [Matrix.neg_mul,Matrix.mul_assoc] using he
  intro i j hij
  rw [← heq i,← heq j]
  exact h i j hij


theorem paired_fill_rotates_root {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (T : ι → SignedTwoState) (d : (Fin 2×ι) → ℝ)
    (hT : ∀ i, forcedRealTwo A root R i=signedTwoReal (T i)*walshTwoReal)
    (hY : (pairedMatchingFill d).transpose= -pairedMatchingFill d)
    (hP : Matrix.IsHadamard (normalizedTwoReal A*(signedTwoBlockDiagonal T).transpose+1+pairedMatchingFill d))
    (hM : Matrix.IsHadamard (normalizedTwoReal A*(signedTwoBlockDiagonal T).transpose+1-pairedMatchingFill d)) :
    realRootConsistency A root (pairedSmallFill d root*R) := by
  have hCross := paired_hadamard_cross_zero
    (normalizedTwoReal A*(signedTwoBlockDiagonal T).transpose+1) (pairedMatchingFill d) hP hM
  have hSwitch := switched_fill_anticommutator (normalizedTwoReal A) (signedTwoBlockDiagonal T)
    (pairedMatchingFill d) (signed_two_block_diagonal_orthogonal T).2 hY hCross
  have hProd : pairedMatchingFill d*signedTwoBlockDiagonal T=
      Matrix.blockDiagonal (fun i => pairedSmallFill d i*signedTwoReal (T i)) := by
    rw [paired_fill_block_diagonal,signedTwoBlockDiagonal,← Matrix.blockDiagonal_mul]
  rw [hProd] at hSwitch
  have hFamily := block_anticommutator_real_family A (fun i => pairedSmallFill d i*signedTwoReal (T i)) hSwitch
  have hRoot := real_consistent_family_forced A root
    (fun i => (pairedSmallFill d i*signedTwoReal (T i))*walshTwoReal) hFamily
  have hAtRoot : R=signedTwoReal (T root)*walshTwoReal := by
    simpa only [forcedRealTwo,if_pos rfl,ite_true] using hT root
  rw [hAtRoot,← Matrix.mul_assoc]
  exact hRoot


theorem paired_diagonal_root_coordinates {ι : Type*} (d : (Fin 2×ι) → ℝ)
    (root : ι) (p e : Bool) (hd : d (1,root)= -d (0,root)) :
    pairedSmallFill d root*diagonalRootReal p e=twoPlaneMatrix p
      (if p then d (0,root)*(if e then -1 else 1) else -d (0,root)*(if e then -1 else 1))
      (if p then -d (0,root) else d (0,root)) := by
  cases p <;> cases e <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [pairedSmallFill,diagonalRootReal,twoPlaneMatrix,Matrix.mul_apply,Fin.sum_univ_two,hd]

theorem diagonal_rotation_section_full (k : TwoPlaneSectionKind) (p e : Bool) (u : ℝ)
    (hu : u=1 ∨ u= -1)
    (hA : twoPlaneSectionCondition k 1 (if e then -1 else 1))
    (hB : twoPlaneSectionCondition k
      (if p then u*(if e then -1 else 1) else -u*(if e then -1 else 1))
      (if p then -u else u)) : k=.full := by
  cases p <;> cases e <;> rcases hu with hu|hu <;> subst u <;> cases k <;>
    norm_num [twoPlaneSectionCondition] at *

theorem real_diagonal_root_forces_full_plane {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (p e : Bool)
    (hR : realRootConsistency A root (twoPlaneMatrix p 1 (if e then -1 else 1)))
    (hW : normalizedTwoReal A*(normalizedTwoReal A).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (hn : 4∣Fintype.card (Fin 2×ι)) :
    ∀ x y : ℝ, realRootConsistency A root (twoPlaneMatrix p x y) := by
  obtain ⟨T,d,hT,hd,hNeg,hY,hP,hM⟩ := diagonal_root_paired_skew_fills A root p e hR hW hn
  have hRot := paired_fill_rotates_root A root (diagonalRootReal p e) T d hT hY hP hM
  have hPair : d (1,root)= -d (0,root) := by
    simpa [pairedFlip,Fin.rev] using hNeg (0,root)
  rw [paired_diagonal_root_coordinates d root p e hPair] at hRot
  obtain ⟨k,hk⟩ := real_root_original_component_sections A root p
  have hFull := diagonal_rotation_section_full k p e (d (0,root)) (hd (0,root))
    ((hk 1 (if e then -1 else 1)).mp hR) ((hk _ _).mp hRot)
  intro x y
  apply (hk x y).mpr
  rw [hFull]
  exact ⟨rfl,rfl⟩

end CompletionTheory
