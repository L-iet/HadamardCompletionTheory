/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import PhaseGeometry.FourierNorm
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PhaseGeometry
open scoped ComplexConjugate Matrix

theorem supported_matrix_row_sq_bound {n : ℕ} {α : Type*} [DecidableEq α]
    (f : Fin n → α) (g : ℕ) (hg : ∀ i,(Finset.univ.filter (fun j => f i=f j)).card=g)
    (A : Matrix (Fin n) (Fin n) ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ i j,‖A i j‖ ≤ K) (hzero : ∀ i j,f i ≠ f j → A i j=0)
    (x : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    ‖∑ j,A i j*x.ofLp j‖^2 ≤ (g : ℝ)*K^2*(∑ j,if f i=f j then ‖x.ofLp j‖^2 else 0) := by
  have he (j : Fin n) : fiberIndicator f i j*(A i j*x.ofLp j)=A i j*x.ofLp j := by
    unfold fiberIndicator
    split_ifs with h
    · simp
    · rw [hzero i j h]; simp
  have hn : (∑ j,‖fiberIndicator f i j‖^2)=(g : ℝ) := by
    calc
      _ = ∑ j,if f i=f j then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        unfold fiberIndicator
        split_ifs <;> norm_num
      _ = _ := by rw [← Finset.sum_filter]; simp [hg i]
  have hb : (∑ j,‖A i j*x.ofLp j‖^2) ≤ K^2*(∑ j,if f i=f j then ‖x.ofLp j‖^2 else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    by_cases h : f i=f j
    · rw [if_pos h,norm_mul,mul_pow]
      have hsq : ‖A i j‖^2 ≤ K^2 := by nlinarith [hbound i j,norm_nonneg (A i j)]
      exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    · rw [if_neg h,hzero i j h]
      simp
  have hc := complex_sum_mul_norm_sq_le (fun j => fiberIndicator f i j) (fun j => A i j*x.ofLp j)
  simp only [he,hn] at hc
  have hm := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg g : (0 : ℝ) ≤ g)
  exact hc.trans (by nlinarith)

theorem supported_matrix_operator_bound {n : ℕ} {α : Type*} [DecidableEq α]
    (f : Fin n → α) (g : ℕ) (hg : ∀ i,(Finset.univ.filter (fun j => f i=f j)).card=g)
    (A : Matrix (Fin n) (Fin n) ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ i j,‖A i j‖ ≤ K) (hzero : ∀ i j,f i ≠ f j → A i j=0) :
    euclideanOperatorNorm A ≤ K*(g : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hK (Nat.cast_nonneg g))
  intro x
  have hs : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) A x‖^2 ≤ (K*(g : ℝ))^2*‖x‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
    simp_rw [euclidean_matrix_apply_entries]
    calc
      _ ≤ ∑ i,(g : ℝ)*K^2*(∑ j,if f i=f j then ‖x.ofLp j‖^2 else 0) :=
        Finset.sum_le_sum (fun i hi => supported_matrix_row_sq_bound f g hg A K hK hbound hzero x i)
      _ = _ := by
        rw [← Finset.mul_sum,Finset.sum_comm]
        simp_rw [fiber_indicator_weighted_column f g hg (fun j => ‖x.ofLp j‖^2)]
        rw [← Finset.mul_sum]
        ring
  have hp : 0 ≤ K*(g : ℝ)*‖x‖ := by positivity
  nlinarith [norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) A x)]

def blockCoordinates (r m : ℕ) : Fin (r*m) ≃ Fin r × Fin m := finProdFinEquiv.symm

noncomputable def ditaMatrix {r m : ℕ} [NeZero m] (A : Matrix (Fin r) (Fin r) ℂ)
    (u : Fin r → Fin m → ℂ) : Matrix (Fin (r*m)) (Fin (r*m)) ℂ :=
  fun s t => A (blockCoordinates r m s).1 (blockCoordinates r m t).1*
    u (blockCoordinates r m t).1 (blockCoordinates r m s).2*
    finCharacterMatrix (1 : ZMod m) (blockCoordinates r m s).2 (blockCoordinates r m t).2

theorem fin_character_power {m : ℕ} [NeZero m] (b : ℕ) (i j : Fin m) :
    (finCharacterMatrix (1 : ZMod m) i j)^b=finCharacterMatrix (b : ZMod m) i j := by
  change (ZMod.stdAddChar ((1 : ZMod m)*(ZMod.finEquiv m i)*(ZMod.finEquiv m j)))^b=_
  rw [← AddChar.map_nsmul_eq_pow]
  change ZMod.stdAddChar (b • ((1 : ZMod m)*(ZMod.finEquiv m i)*(ZMod.finEquiv m j)))=
    ZMod.stdAddChar ((b : ZMod m)*(ZMod.finEquiv m i)*(ZMod.finEquiv m j))
  congr 1
  simp [nsmul_eq_mul,mul_assoc]

theorem dita_power_gram_factor {r m : ℕ} [NeZero m] (A : Matrix (Fin r) (Fin r) ℂ)
    (u : Fin r → Fin m → ℂ) (b : ℕ) (s t : Fin (r*m)) :
    (∑ v,(ditaMatrix A u s v)^b*conj ((ditaMatrix A u t v)^b))=
      (∑ a : Fin r,(A (blockCoordinates r m s).1 a)^b*conj ((A (blockCoordinates r m t).1 a)^b)*
        (u a (blockCoordinates r m s).2)^b*conj ((u a (blockCoordinates r m t).2)^b))*
      complexRowGram (finCharacterMatrix (b : ZMod m)) (blockCoordinates r m s).2 (blockCoordinates r m t).2 := by
  let C : Fin r → ℂ := fun a => (A (blockCoordinates r m s).1 a)^b*conj ((A (blockCoordinates r m t).1 a)^b)*
    (u a (blockCoordinates r m s).2)^b*conj ((u a (blockCoordinates r m t).2)^b)
  let W : Fin m → ℂ := fun j => finCharacterMatrix (b : ZMod m) (blockCoordinates r m s).2 j*
    conj (finCharacterMatrix (b : ZMod m) (blockCoordinates r m t).2 j)
  have he (a : Fin r) (j : Fin m) :
      (ditaMatrix A u s (finProdFinEquiv (a,j)))^b*conj ((ditaMatrix A u t (finProdFinEquiv (a,j)))^b)=C a*W j := by
    simp only [ditaMatrix,blockCoordinates,Equiv.symm_apply_apply,mul_pow,map_mul]
    rw [fin_character_power,fin_character_power]
    dsimp [C,W,blockCoordinates]
    ring
  calc
    _ = ∑ p : Fin r × Fin m,(ditaMatrix A u s (finProdFinEquiv p))^b*conj ((ditaMatrix A u t (finProdFinEquiv p))^b) :=
      (finProdFinEquiv.sum_comp (fun v => (ditaMatrix A u s v)^b*conj ((ditaMatrix A u t v)^b))).symm
    _ = ∑ a : Fin r,∑ j : Fin m,C a*W j := by
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun j hj => he a j))
    _ = (∑ a,C a)*(∑ j,W j) := by rw [Finset.sum_mul]; simp only [Finset.mul_sum]
    _ = _ := rfl

def ditaFrequency {r m : ℕ} [NeZero m] (s : Fin (r*m)) : ZMod m :=
  (4 : ZMod m)*(ZMod.finEquiv m (blockCoordinates r m s).2)

theorem dita_frequency_fiber_card {r m : ℕ} [NeZero m] (s : Fin (r*m)) :
    (Finset.univ.filter (fun t : Fin (r*m) => ditaFrequency s=ditaFrequency t)).card=r*Nat.gcd m 4 := by
  classical
  have hc : (Finset.univ.filter (fun j : Fin m => (4 : ZMod m)*(ZMod.finEquiv m (blockCoordinates r m s).2)=(4 : ZMod m)*(ZMod.finEquiv m j))).card=Nat.gcd m 4 := fin_zmod_mul_fiber_card (n := m) 4 (blockCoordinates r m s).2
  calc
    _ = ((Finset.univ : Finset (Fin r)).product (Finset.univ.filter (fun j : Fin m =>
        (4 : ZMod m)*(ZMod.finEquiv m (blockCoordinates r m s).2)=(4 : ZMod m)*(ZMod.finEquiv m j)))).card := by
      apply Finset.card_equiv (blockCoordinates r m)
      intro t
      simp [ditaFrequency,Finset.mem_product]
    _ = (Finset.univ : Finset (Fin r)).card*(Finset.univ.filter (fun j : Fin m => (4 : ZMod m)*(ZMod.finEquiv m (blockCoordinates r m s).2)=(4 : ZMod m)*(ZMod.finEquiv m j))).card := Finset.card_product _ _
    _ = _ := by rw [Finset.card_univ,Fintype.card_fin,hc]

theorem fin_character_row_gram {m : ℕ} [NeZero m] (b : ℕ) (i k : Fin m) :
    complexRowGram (finCharacterMatrix (b : ZMod m)) i k=
      if (b : ZMod m)*(ZMod.finEquiv m i)=(b : ZMod m)*(ZMod.finEquiv m k) then (m : ℂ) else 0 := by
  change (∑ j : Fin m,characterMatrix (b : ZMod m) (ZMod.finEquiv m i) (ZMod.finEquiv m j)*
    conj (characterMatrix (b : ZMod m) (ZMod.finEquiv m k) (ZMod.finEquiv m j)))=_
  calc
    _ = ∑ j : ZMod m,characterMatrix (b : ZMod m) (ZMod.finEquiv m i) j*conj (characterMatrix (b : ZMod m) (ZMod.finEquiv m k) j) :=
      (ZMod.finEquiv m).toEquiv.sum_comp _
    _ = (if (b : ZMod m)*((ZMod.finEquiv m i)-(ZMod.finEquiv m k))=0 then (m : ℂ) else 0) :=
      characterMatrix_gram (b : ZMod m) (ZMod.finEquiv m i) (ZMod.finEquiv m k)
    _ = _ := by simp only [mul_sub,sub_eq_zero]

theorem dita_unit {r m : ℕ} [NeZero m] (A : Matrix (Fin r) (Fin r) ℂ)
    (u : Fin r → Fin m → ℂ) (hA : ∀ a b,‖A a b‖=1) (hu : ∀ b i,‖u b i‖=1)
    (s t : Fin (r*m)) : ‖ditaMatrix A u s t‖=1 := by
  simp only [ditaMatrix,norm_mul,hA,hu,fin_character_unit,mul_one]

theorem dita_fourth_gram_zero {r m : ℕ} [NeZero m] (A : Matrix (Fin r) (Fin r) ℂ)
    (u : Fin r → Fin m → ℂ) (s t : Fin (r*m)) (h : ditaFrequency s ≠ ditaFrequency t) :
    complexRowGram (fourthPowerMatrix (ditaMatrix A u)) s t=0 := by
  have he : complexRowGram (fourthPowerMatrix (ditaMatrix A u)) s t=
      (∑ a : Fin r,(A (blockCoordinates r m s).1 a)^4*conj ((A (blockCoordinates r m t).1 a)^4)*
        (u a (blockCoordinates r m s).2)^4*conj ((u a (blockCoordinates r m t).2)^4))*
      complexRowGram (finCharacterMatrix (4 : ZMod m)) (blockCoordinates r m s).2 (blockCoordinates r m t).2 := dita_power_gram_factor A u 4 s t
  have hrow : complexRowGram (finCharacterMatrix (4 : ZMod m)) (blockCoordinates r m s).2 (blockCoordinates r m t).2=
      if ditaFrequency s=ditaFrequency t then (m : ℂ) else 0 := fin_character_row_gram (m := m) 4 _ _
  rw [hrow] at he
  have hn : (4 : ZMod m)*(ZMod.finEquiv m (blockCoordinates r m s).2) ≠
      (4 : ZMod m)*(ZMod.finEquiv m (blockCoordinates r m t).2) := h
  rw [if_neg h,mul_zero] at he
  exact he

theorem dita_fourth_gram_bound {r m : ℕ} [NeZero m] (A : Matrix (Fin r) (Fin r) ℂ)
    (u : Fin r → Fin m → ℂ) (hA : ∀ a b,‖A a b‖=1) (hu : ∀ b i,‖u b i‖=1)
    (s t : Fin (r*m)) : ‖complexRowGram (fourthPowerMatrix (ditaMatrix A u)) s t‖ ≤ (r : ℝ)*(m : ℝ) := by
  have he : complexRowGram (fourthPowerMatrix (ditaMatrix A u)) s t=
      (∑ a : Fin r,(A (blockCoordinates r m s).1 a)^4*conj ((A (blockCoordinates r m t).1 a)^4)*
        (u a (blockCoordinates r m s).2)^4*conj ((u a (blockCoordinates r m t).2)^4))*
      complexRowGram (finCharacterMatrix (4 : ZMod m)) (blockCoordinates r m s).2 (blockCoordinates r m t).2 := dita_power_gram_factor A u 4 s t
  rw [he,norm_mul]
  have hc : ‖∑ a : Fin r,(A (blockCoordinates r m s).1 a)^4*conj ((A (blockCoordinates r m t).1 a)^4)*
      (u a (blockCoordinates r m s).2)^4*conj ((u a (blockCoordinates r m t).2)^4)‖ ≤ (r : ℝ) := by
    have hb := norm_sum_le Finset.univ (fun a : Fin r => (A (blockCoordinates r m s).1 a)^4*conj ((A (blockCoordinates r m t).1 a)^4)*
      (u a (blockCoordinates r m s).2)^4*conj ((u a (blockCoordinates r m t).2)^4))
    simpa only [norm_mul,Complex.norm_conj,norm_pow,hA,hu,one_pow,mul_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hb
  have hf : ‖complexRowGram (finCharacterMatrix (4 : ZMod m)) (blockCoordinates r m s).2 (blockCoordinates r m t).2‖ ≤ (m : ℝ) := by
    have hrow : complexRowGram (finCharacterMatrix (4 : ZMod m)) (blockCoordinates r m s).2 (blockCoordinates r m t).2=
        if ditaFrequency s=ditaFrequency t then (m : ℂ) else 0 := fin_character_row_gram (m := m) 4 _ _
    rw [hrow]
    split_ifs <;> simp
  exact mul_le_mul hc hf (norm_nonneg _) (Nat.cast_nonneg r)

theorem dita_fourth_operator_sq_bound {r m : ℕ} [NeZero m] (A : Matrix (Fin r) (Fin r) ℂ)
    (u : Fin r → Fin m → ℂ) (hA : ∀ a b,‖A a b‖=1) (hu : ∀ b i,‖u b i‖=1) :
    euclideanOperatorNorm (fourthPowerMatrix (ditaMatrix A u))^2 ≤ (r : ℝ)^2*(m : ℝ)*(Nat.gcd m 4 : ℝ) := by
  let G : Matrix (Fin (r*m)) (Fin (r*m)) ℂ := fourthPowerMatrix (ditaMatrix A u)*(fourthPowerMatrix (ditaMatrix A u))ᴴ
  have hb (s t : Fin (r*m)) : ‖G s t‖ ≤ (r : ℝ)*(m : ℝ) := dita_fourth_gram_bound A u hA hu s t
  have hz (s t : Fin (r*m)) (h : ditaFrequency s ≠ ditaFrequency t) : G s t=0 := dita_fourth_gram_zero A u s t h
  have hf (s : Fin (r*m)) : (Finset.univ.filter (fun t : Fin (r*m) => ditaFrequency s=ditaFrequency t)).card=r*Nat.gcd m 4 :=
    dita_frequency_fiber_card s
  have hop := supported_matrix_operator_bound ditaFrequency (r*Nat.gcd m 4) hf G ((r : ℝ)*(m : ℝ)) (by positivity) hb hz
  calc
    _ = euclideanOperatorNorm G := (euclideanOperatorNorm_gram (fourthPowerMatrix (ditaMatrix A u))).symm
    _ ≤ ((r : ℝ)*(m : ℝ))*(r*Nat.gcd m 4 : ℕ) := hop
    _ = _ := by push_cast; ring

theorem dita_rhoFourth_bound {r m : ℕ} (hr : 0<r) [NeZero m]
    (A : Matrix (Fin r) (Fin r) ℂ) (u : Fin r → Fin m → ℂ)
    (hA : ∀ a b,‖A a b‖=1) (hu : ∀ b i,‖u b i‖=1) :
    rhoFourth (ditaMatrix A u) ≤ Real.sqrt ((Nat.gcd m 4 : ℝ)/(m : ℝ)) := by
  have hm : (0 : ℝ)<m := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne m))
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have hs := dita_fourth_operator_sq_bound A u hA hu
  have he : ((Nat.gcd m 4 : ℝ)/(m : ℝ))*((r*m : ℕ) : ℝ)^2=
      (r : ℝ)^2*(m : ℝ)*(Nat.gcd m 4 : ℝ) := by
    push_cast
    field_simp [hm.ne']
    <;> ring
  have hsq : rhoFourth (ditaMatrix A u)^2 ≤ (Nat.gcd m 4 : ℝ)/(m : ℝ) := by
    unfold rhoFourth
    rw [div_pow]
    apply (div_le_iff₀ (show 0<((r*m : ℕ) : ℝ)^2 by push_cast; positivity)).mpr
    rw [he]
    exact hs
  exact Real.le_sqrt_of_sq_le hsq

theorem dita_equivalent_distance_bound {r m : ℕ} (hr : 0<r) [NeZero m]
    (A : Matrix (Fin r) (Fin r) ℂ) (u : Fin r → Fin m → ℂ)
    (hA : ∀ a b,‖A a b‖=1) (hu : ∀ b i,‖u b i‖=1)
    (Q : Matrix (Fin (r*m)) (Fin (r*m)) ℂ) (hQ : ∀ i j,IsFourthRoot (Q i j))
    (s t : Equiv.Perm (Fin (r*m))) (v w : Fin (r*m) → ℂ)
    (hv : ∀ i,‖v i‖=1) (hw : ∀ j,‖w j‖=1) :
    (1-Real.sqrt ((Nat.gcd m 4 : ℝ)/(m : ℝ)))/8 ≤
      totalRoundingError (phaseTransform (permuteMatrix (ditaMatrix A u) s t) v w) Q/((r*m : ℕ) : ℝ)^2 := by
  have hn : 0<r*m := Nat.mul_pos hr (Nat.pos_of_ne_zero (NeZero.ne m))
  have hdist := equivalent_quaternary_distance_lower hn (ditaMatrix A u) Q (dita_unit A u hA hu) hQ s t v w hv hw
  have hb := dita_rhoFourth_bound hr A u hA hu
  linarith

theorem dita_not_four_phase_accessible {r m : ℕ} (hr : 0<r) [NeZero m]
    (A : Matrix (Fin r) (Fin r) ℂ) (u : Fin r → Fin m → ℂ)
    (hA : ∀ a b,‖A a b‖=1) (hu : ∀ b i,‖u b i‖=1) (hdiv : ¬ m ∣ 4) :
    ¬ HasFourPhaseGauge (ditaMatrix A u) := by
  have hm : 0<m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hn : 0<r*m := Nat.mul_pos hr hm
  intro hphase
  have he := (rhoFourth_one_iff_four_phase_gauge hn _ (dita_unit A u hA hu)).mpr hphase
  have hb := dita_rhoFourth_bound hr A u hA hu
  rw [he] at hb
  have hg : Nat.gcd m 4<m := lt_of_le_of_ne (Nat.gcd_le_left 4 hm) (by
    intro h
    exact hdiv (Nat.gcd_eq_left_iff_dvd.mp h))
  have hmR : (0 : ℝ)<m := by exact_mod_cast hm
  have hgR : (Nat.gcd m 4 : ℝ)<m := by exact_mod_cast hg
  have hsmall : (Nat.gcd m 4 : ℝ)/(m : ℝ)<1 := (div_lt_one hmR).mpr hgR
  have hnonneg : 0 ≤ (Nat.gcd m 4 : ℝ)/(m : ℝ) := div_nonneg (Nat.cast_nonneg _) hmR.le
  have hs := Real.sq_sqrt hnonneg
  nlinarith [Real.sqrt_nonneg ((Nat.gcd m 4 : ℝ)/(m : ℝ))]

theorem dita_hadamard_gram {r m : ℕ} [NeZero m] (A : Matrix (Fin r) (Fin r) ℂ)
    (u : Fin r → Fin m → ℂ) (hu : ∀ b i,‖u b i‖=1)
    (horth : ∀ a b,complexRowGram A a b=if a=b then (r : ℂ) else 0)
    (s t : Fin (r*m)) : complexRowGram (ditaMatrix A u) s t=if s=t then ((r*m : ℕ) : ℂ) else 0 := by
  have he : complexRowGram (ditaMatrix A u) s t=
      (∑ a : Fin r,A (blockCoordinates r m s).1 a*conj (A (blockCoordinates r m t).1 a)*
        u a (blockCoordinates r m s).2*conj (u a (blockCoordinates r m t).2))*
      complexRowGram (finCharacterMatrix (1 : ZMod m)) (blockCoordinates r m s).2 (blockCoordinates r m t).2 := by
    simpa only [pow_one,Nat.cast_one,complexRowGram] using dita_power_gram_factor A u 1 s t
  rw [fin_fourier_hadamard_gram] at he
  by_cases hi : (blockCoordinates r m s).2=(blockCoordinates r m t).2
  · rw [if_pos hi] at he
    have hc : (∑ a : Fin r,A (blockCoordinates r m s).1 a*conj (A (blockCoordinates r m t).1 a)*
        u a (blockCoordinates r m s).2*conj (u a (blockCoordinates r m t).2))=
        complexRowGram A (blockCoordinates r m s).1 (blockCoordinates r m t).1 := by
      unfold complexRowGram
      apply Finset.sum_congr rfl
      intro a ha
      rw [hi]
      calc
        _ = (A (blockCoordinates r m s).1 a*conj (A (blockCoordinates r m t).1 a))*
          (u a (blockCoordinates r m t).2*conj (u a (blockCoordinates r m t).2)) := by ring
        _ = _ := by rw [unit_mul_conj (hu a _),mul_one]
    rw [hc,horth] at he
    by_cases ha : (blockCoordinates r m s).1=(blockCoordinates r m t).1
    · have hst : s=t := (blockCoordinates r m).injective (Prod.ext ha hi)
      rw [if_pos ha] at he
      rw [if_pos hst]
      rw [he]
      push_cast
      ring
    · have hst : s ≠ t := by intro h; subst t; exact ha rfl
      rw [if_neg ha,zero_mul] at he
      simpa only [if_neg hst] using he
  · have hst : s ≠ t := by intro h; subst t; exact hi rfl
    rw [if_neg hi,mul_zero] at he
    simpa only [if_neg hst] using he
end PhaseGeometry
