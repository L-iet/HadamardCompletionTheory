/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import PhaseGeometry.FourierCharacters
public import Mathlib.GroupTheory.Index
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PhaseGeometry
open scoped ComplexConjugate Matrix


def zmodMulAddHom {n : ℕ} (a : ZMod n) : ZMod n →+ ZMod n where
  toFun x := a*x
  map_zero' := mul_zero a
  map_add' := mul_add a

theorem zmod_mul_range_card {n : ℕ} [NeZero n] (b : ℕ) :
    Nat.card (zmodMulAddHom (b : ZMod n)).range=n/Nat.gcd n b := by
  classical
  let R : Finset (ZMod n) := Finset.univ.image (fun i : ZMod n => (b : ZMod n)*i)
  have hs : ((zmodMulAddHom (b : ZMod n)).range : Set (ZMod n))=(R : Set (ZMod n)) := by
    ext x
    simp [zmodMulAddHom,R,AddMonoidHom.mem_range]
  calc
    _ = Nat.card R := Nat.card_congr (Equiv.cast (congrArg (fun S : Set (ZMod n) => ↥S) hs))
    _ = R.card := by rw [Nat.card_eq_fintype_card,Fintype.card_coe]
    _ = _ := by rw [zmod_mul_image_card,ZMod.addOrderOf_coe b (NeZero.ne n)]

theorem zmod_mul_kernel_card {n : ℕ} [NeZero n] (b : ℕ) :
    Nat.card (zmodMulAddHom (b : ZMod n)).ker=Nat.gcd n b := by
  have hp := AddSubgroup.card_ker_mul_card_range (zmodMulAddHom (b : ZMod n))
  have hn : Nat.card (ZMod n)=n := by simp [Nat.card_eq_fintype_card,ZMod.card]
  rw [zmod_mul_range_card,hn] at hp
  have hd : Nat.gcd n b ∣ n := Nat.gcd_dvd_left n b
  have hdiv : n/Nat.gcd n b*Nat.gcd n b=n := Nat.div_mul_cancel hd
  have hnpos : 0<n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hq : 0<n/Nat.gcd n b := Nat.div_pos (Nat.le_of_dvd hnpos hd) (Nat.gcd_pos_of_pos_left b hnpos)
  apply Nat.eq_of_mul_eq_mul_right hq
  simpa only [mul_comm] using hp.trans hdiv.symm

theorem zmod_mul_fiber_card {n : ℕ} [NeZero n] (b : ℕ) (i : ZMod n) :
    (Finset.univ.filter (fun j : ZMod n => (b : ZMod n)*i=(b : ZMod n)*j)).card=Nat.gcd n b := by
  classical
  let R : Finset (ZMod n) := Finset.univ.filter (fun j : ZMod n => (b : ZMod n)*i=(b : ZMod n)*j)
  let e : R ≃ (zmodMulAddHom (b : ZMod n)).ker :=
    { toFun := fun x => ⟨x.val-i,by
        change (b : ZMod n)*(x.val-i)=0
        have hx := (Finset.mem_filter.mp x.property).2
        rw [mul_sub,← hx,sub_self]⟩
      invFun := fun x => ⟨x.val+i,by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        have hx : (b : ZMod n)*x.val=0 := x.property
        rw [mul_add,hx,zero_add]⟩
      left_inv := by intro x; apply Subtype.ext; dsimp; ring
      right_inv := by intro x; apply Subtype.ext; dsimp; ring }
  change R.card=Nat.gcd n b
  calc
    _ = Nat.card R := by rw [Nat.card_eq_fintype_card,Fintype.card_coe]
    _ = Nat.card (zmodMulAddHom (b : ZMod n)).ker := Nat.card_congr e
    _ = _ := zmod_mul_kernel_card b

theorem fin_zmod_mul_fiber_card {n : ℕ} [NeZero n] (b : ℕ) (i : Fin n) :
    (Finset.univ.filter (fun j : Fin n => (b : ZMod n)*(ZMod.finEquiv n i)=
      (b : ZMod n)*(ZMod.finEquiv n j))).card=Nat.gcd n b := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => (b : ZMod n)*(ZMod.finEquiv n i)=
      (b : ZMod n)*(ZMod.finEquiv n j))
  let T : Finset (ZMod n) := Finset.univ.filter (fun j : ZMod n => (b : ZMod n)*(ZMod.finEquiv n i)=(b : ZMod n)*j)
  let e : S ≃ T :=
    { toFun := fun x => ⟨ZMod.finEquiv n x.val,by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _,(Finset.mem_filter.mp x.property).2⟩⟩
      invFun := fun x => ⟨(ZMod.finEquiv n).symm x.val,by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        have hx := (Finset.mem_filter.mp x.property).2
        simpa only [RingEquiv.apply_symm_apply] using hx⟩
      left_inv := by intro x; apply Subtype.ext; exact (ZMod.finEquiv n).symm_apply_apply x.val
      right_inv := by intro x; apply Subtype.ext; exact (ZMod.finEquiv n).apply_symm_apply x.val }
  change S.card=Nat.gcd n b
  calc
    _ = Nat.card S := by rw [Nat.card_eq_fintype_card,Fintype.card_coe]
    _ = Nat.card T := Nat.card_congr e
    _ = T.card := by rw [Nat.card_eq_fintype_card,Fintype.card_coe]
    _ = _ := zmod_mul_fiber_card b (ZMod.finEquiv n i)


open scoped ComplexConjugate Matrix

def fiberIndicator {n : ℕ} {α : Type*} [DecidableEq α] (f : Fin n → α) :
    Matrix (Fin n) (Fin n) ℂ := fun i j => if f i=f j then 1 else 0

theorem fiber_indicator_row_sum {n : ℕ} {α : Type*} [DecidableEq α] (f : Fin n → α) (i : Fin n) :
    (∑ j,fiberIndicator f i j)=((Finset.univ.filter (fun j => f i=f j)).card : ℂ) := by
  simp only [fiberIndicator,← Finset.sum_filter]
  simp

theorem fiber_indicator_row_sq_bound {n : ℕ} {α : Type*} [DecidableEq α]
    (f : Fin n → α) (g : ℕ) (hg : ∀ i,(Finset.univ.filter (fun j => f i=f j)).card=g)
    (x : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    ‖∑ j,fiberIndicator f i j*x.ofLp j‖^2 ≤
      (g : ℝ)*(∑ j,if f i=f j then ‖x.ofLp j‖^2 else 0) := by
  have he (j : Fin n) : fiberIndicator f i j*(fiberIndicator f i j*x.ofLp j)=fiberIndicator f i j*x.ofLp j := by
    unfold fiberIndicator
    split_ifs <;> simp
  have hn : (∑ j,‖fiberIndicator f i j‖^2)=(g : ℝ) := by
    calc
      _ = ∑ j,if f i=f j then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        unfold fiberIndicator
        split_ifs <;> norm_num
      _ = _ := by rw [← Finset.sum_filter]; simp [hg i]
  have hb : (∑ j,‖fiberIndicator f i j*x.ofLp j‖^2)=∑ j,if f i=f j then ‖x.ofLp j‖^2 else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    unfold fiberIndicator
    split_ifs <;> simp
  have hc := complex_sum_mul_norm_sq_le (fun j => fiberIndicator f i j) (fun j => fiberIndicator f i j*x.ofLp j)
  simpa only [he,hn,hb] using hc

theorem fiber_indicator_weighted_column {n : ℕ} {α : Type*} [DecidableEq α]
    (f : Fin n → α) (g : ℕ) (hg : ∀ i,(Finset.univ.filter (fun j => f i=f j)).card=g)
    (w : Fin n → ℝ) (j : Fin n) :
    (∑ i,if f i=f j then w j else 0)=(g : ℝ)*w j := by
  have he : Finset.univ.filter (fun i => f i=f j)=Finset.univ.filter (fun i => f j=f i) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,eq_comm]
  rw [← Finset.sum_filter,Finset.sum_const,he,hg j,nsmul_eq_mul]

theorem fiber_indicator_apply_sq_bound {n : ℕ} {α : Type*} [DecidableEq α]
    (f : Fin n → α) (g : ℕ) (hg : ∀ i,(Finset.univ.filter (fun j => f i=f j)).card=g)
    (x : EuclideanSpace ℂ (Fin n)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (fiberIndicator f) x‖^2 ≤ (g : ℝ)^2*‖x‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
  simp_rw [euclidean_matrix_apply_entries]
  calc
    _ ≤ ∑ i,(g : ℝ)*(∑ j,if f i=f j then ‖x.ofLp j‖^2 else 0) :=
      Finset.sum_le_sum (fun i hi => fiber_indicator_row_sq_bound f g hg x i)
    _ = _ := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      simp_rw [fiber_indicator_weighted_column f g hg (fun j => ‖x.ofLp j‖^2)]
      rw [← Finset.mul_sum]
      ring

theorem fiber_indicator_operator_le {n : ℕ} {α : Type*} [DecidableEq α]
    (f : Fin n → α) (g : ℕ) (hg : ∀ i,(Finset.univ.filter (fun j => f i=f j)).card=g) :
    euclideanOperatorNorm (fiberIndicator f) ≤ (g : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Nat.cast_nonneg g)
  intro x
  have hs := fiber_indicator_apply_sq_bound f g hg x
  have hp : 0 ≤ (g : ℝ)*‖x‖ := mul_nonneg (Nat.cast_nonneg g) (norm_nonneg _)
  nlinarith [norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (fiberIndicator f) x)]

theorem fiber_indicator_operator_eq {n : ℕ} (hn : 0<n) {α : Type*} [DecidableEq α]
    (f : Fin n → α) (g : ℕ) (hg : ∀ i,(Finset.univ.filter (fun j => f i=f j)).card=g) :
    euclideanOperatorNorm (fiberIndicator f)=(g : ℝ) := by
  let x : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (fun _ => (1 : ℂ))
  have hx : ‖x‖^2=(n : ℝ) := by rw [PiLp.norm_sq_eq_of_L2]; simp [x]
  have hxpos : 0<‖x‖ := by
    have hnR : (0 : ℝ)<n := by exact_mod_cast hn
    nlinarith [norm_nonneg x]
  have he : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (fiberIndicator f) x=(g : ℂ) • x := by
    ext i
    rw [euclidean_matrix_apply_entries]
    simp only [x,WithLp.ofLp_toLp,mul_one]
    rw [fiber_indicator_row_sum,hg i]
    simp
  have hb := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (fiberIndicator f)).le_opNorm x
  rw [he,norm_smul,Complex.norm_natCast] at hb
  have hu := fiber_indicator_operator_le f g hg
  change (g : ℝ)*‖x‖ ≤ euclideanOperatorNorm (fiberIndicator f)*‖x‖ at hb
  nlinarith


noncomputable def finCharacterMatrix {n : ℕ} [NeZero n] (a : ZMod n) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => characterMatrix a (ZMod.finEquiv n i) (ZMod.finEquiv n j)

theorem fin_character_gram {n : ℕ} [NeZero n] (b : ℕ) :
    finCharacterMatrix (b : ZMod n)*(finCharacterMatrix (b : ZMod n))ᴴ=
      (n : ℂ) • fiberIndicator (fun i : Fin n => (b : ZMod n)*(ZMod.finEquiv n i)) := by
  classical
  ext i k
  change (∑ j : Fin n,characterMatrix (b : ZMod n) (ZMod.finEquiv n i) (ZMod.finEquiv n j)*
    conj (characterMatrix (b : ZMod n) (ZMod.finEquiv n k) (ZMod.finEquiv n j)))=
    (n : ℂ)*(if (b : ZMod n)*(ZMod.finEquiv n i)=(b : ZMod n)*(ZMod.finEquiv n k) then 1 else 0)
  calc
    _ = ∑ j : ZMod n,characterMatrix (b : ZMod n) (ZMod.finEquiv n i) j*conj (characterMatrix (b : ZMod n) (ZMod.finEquiv n k) j) :=
      (ZMod.finEquiv n).toEquiv.sum_comp _
    _ = (if (b : ZMod n)*((ZMod.finEquiv n i)-(ZMod.finEquiv n k))=0 then (n : ℂ) else 0) :=
      characterMatrix_gram (b : ZMod n) (ZMod.finEquiv n i) (ZMod.finEquiv n k)
    _ = _ := by
      by_cases h : (b : ZMod n)*(ZMod.finEquiv n i)=(b : ZMod n)*(ZMod.finEquiv n k)
      · simp [mul_sub,sub_eq_zero,h]
      · simp [mul_sub,sub_eq_zero,h]

theorem euclideanOperatorNorm_smul {n : ℕ} (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    euclideanOperatorNorm (c • A)=‖c‖*euclideanOperatorNorm A := by
  unfold euclideanOperatorNorm
  rw [map_smul,norm_smul]

theorem powered_fourier_operator_sq {n : ℕ} [NeZero n] (b : ℕ) :
    euclideanOperatorNorm (finCharacterMatrix (b : ZMod n))^2=(n : ℝ)*(Nat.gcd n b : ℝ) := by
  have hn : 0<n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hg (i : Fin n) : (Finset.univ.filter (fun j : Fin n => (b : ZMod n)*(ZMod.finEquiv n i)=
      (b : ZMod n)*(ZMod.finEquiv n j))).card=Nat.gcd n b := fin_zmod_mul_fiber_card b i
  have he := euclideanOperatorNorm_gram (finCharacterMatrix (b : ZMod n))
  rw [fin_character_gram,euclideanOperatorNorm_smul,Complex.norm_natCast,
    fiber_indicator_operator_eq hn _ (Nat.gcd n b) hg] at he
  exact he.symm

theorem powered_fourier_operator_norm {n : ℕ} [NeZero n] (b : ℕ) :
    euclideanOperatorNorm (finCharacterMatrix (b : ZMod n))=Real.sqrt ((n : ℝ)*(Nat.gcd n b : ℝ)) := by
  have hp : 0 ≤ euclideanOperatorNorm (finCharacterMatrix (b : ZMod n)) := norm_nonneg _
  rw [← powered_fourier_operator_sq b,Real.sqrt_sq hp]

theorem fourier_rhoFourth {n : ℕ} [NeZero n] :
    rhoFourth (finCharacterMatrix (1 : ZMod n))=Real.sqrt ((Nat.gcd n 4 : ℝ)/(n : ℝ)) := by
  have he : fourthPowerMatrix (finCharacterMatrix (1 : ZMod n))=finCharacterMatrix (4 : ZMod n) := by
    ext i j
    exact fourier_fourth_power (ZMod.finEquiv n i) (ZMod.finEquiv n j)
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  unfold rhoFourth
  rw [he]
  have hs : (euclideanOperatorNorm (finCharacterMatrix (4 : ZMod n))/(n : ℝ))^2=(Nat.gcd n 4 : ℝ)/(n : ℝ) := by
    have hn4 : euclideanOperatorNorm (finCharacterMatrix (4 : ZMod n))^2=(n : ℝ)*(Nat.gcd n 4 : ℝ) := powered_fourier_operator_sq (n := n) 4
    rw [div_pow,hn4]
    field_simp [hn]
  have hp : 0 ≤ euclideanOperatorNorm (finCharacterMatrix (4 : ZMod n))/(n : ℝ) :=
    div_nonneg (norm_nonneg _) (Nat.cast_nonneg n)
  calc
    _ = Real.sqrt ((euclideanOperatorNorm (finCharacterMatrix (4 : ZMod n))/(n : ℝ))^2) := (Real.sqrt_sq hp).symm
    _ = _ := by rw [hs]

theorem fin_character_unit {n : ℕ} [NeZero n] (a : ZMod n) (i j : Fin n) :
    ‖finCharacterMatrix a i j‖=1 := characterMatrix_unit a (ZMod.finEquiv n i) (ZMod.finEquiv n j)

theorem fin_fourier_hadamard_gram {n : ℕ} [NeZero n] (i k : Fin n) :
    complexRowGram (finCharacterMatrix (1 : ZMod n)) i k=if i=k then (n : ℂ) else 0 := by
  change (∑ j : Fin n,characterMatrix (1 : ZMod n) (ZMod.finEquiv n i) (ZMod.finEquiv n j)*
    conj (characterMatrix (1 : ZMod n) (ZMod.finEquiv n k) (ZMod.finEquiv n j)))=_
  calc
    _ = ∑ j : ZMod n,characterMatrix (1 : ZMod n) (ZMod.finEquiv n i) j*conj (characterMatrix (1 : ZMod n) (ZMod.finEquiv n k) j) :=
      (ZMod.finEquiv n).toEquiv.sum_comp _
    _ = (if (1 : ZMod n)*((ZMod.finEquiv n i)-(ZMod.finEquiv n k))=0 then (n : ℂ) else 0) :=
      characterMatrix_gram (1 : ZMod n) (ZMod.finEquiv n i) (ZMod.finEquiv n k)
    _ = _ := by simp [one_mul,sub_eq_zero,(ZMod.finEquiv n).injective.eq_iff]

theorem fin_powered_fourier_rank {n : ℕ} [NeZero n] (b : ℕ) :
    (finCharacterMatrix (b : ZMod n)).rank=n/Nat.gcd n b := by
  calc
    _ = (characterMatrix (b : ZMod n)).rank :=
      Matrix.rank_submatrix _ (ZMod.finEquiv n).toEquiv (ZMod.finEquiv n).toEquiv
    _ = _ := powered_fourier_character_rank b

theorem fourier_phase_accessible_iff_dvd_four {n : ℕ} [NeZero n] :
    HasFourPhaseGauge (finCharacterMatrix (1 : ZMod n)) ↔ n ∣ 4 := by
  have hn : 0<n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  rw [← rhoFourth_one_iff_four_phase_gauge hn _ (fin_character_unit (1 : ZMod n)),fourier_rhoFourth,Real.sqrt_eq_one]
  rw [div_eq_one_iff_eq hnR]
  constructor
  · intro he
    exact Nat.gcd_eq_left_iff_dvd.mp (by exact_mod_cast he)
  · intro hd
    exact_mod_cast Nat.gcd_eq_left_iff_dvd.mpr hd

theorem fourier_rhoFourth_orbit {n : ℕ} [NeZero n] (s t : Equiv.Perm (Fin n))
    (r c : Fin n → ℂ) (hr : ∀ i,‖r i‖=1) (hc : ∀ j,‖c j‖=1) :
    rhoFourth (phaseTransform (permuteMatrix (finCharacterMatrix (1 : ZMod n)) s t) r c)=
      Real.sqrt ((Nat.gcd n 4 : ℝ)/(n : ℝ)) := by
  rw [rhoFourth_phase_invariant _ r c hr hc,rhoFourth_permutation_invariant,fourier_rhoFourth]
end PhaseGeometry
