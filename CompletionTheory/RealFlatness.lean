/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory
public import PhaseGeometry
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory
open scoped ComplexConjugate Matrix

def complexifyRealMatrix {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (Z i j : ℂ)

noncomputable def nearestSignMatrix {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if 0 ≤ Z i j then 1 else -1

def quarticFlatness {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i,∑ j,(Z i j^2-1)^2

theorem nearest_sign_error_bound (z : ℝ) :
    ((if 0 ≤ z then (1 : ℝ) else -1)-z)^2 ≤ (z^2-1)^2 := by
  split_ifs with h
  · have hp : 0 ≤ z*(z+2)*(z-1)^2 := mul_nonneg (mul_nonneg h (by linarith)) (sq_nonneg _)
    nlinarith
  · have hn : 0 ≤ -z := le_of_lt (neg_pos.mpr (lt_of_not_ge h))
    have hp : 0 ≤ (-z)*(-z+2)*(-z-1)^2 := mul_nonneg (mul_nonneg hn (by linarith)) (sq_nonneg _)
    nlinarith

theorem nearest_signs_isSignMatrix {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ) :
    IsSignMatrix (nearestSignMatrix Z) := by
  intro i j
  unfold nearestSignMatrix
  split_ifs <;> simp [IsSign]

theorem complex_rounding_frobenius_le {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ) :
    PhaseGeometry.matrixFrobeniusSq (complexifyRealMatrix (nearestSignMatrix Z)-complexifyRealMatrix Z) ≤ quarticFlatness Z := by
  unfold PhaseGeometry.matrixFrobeniusSq quarticFlatness
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  have he : Complex.normSq ((complexifyRealMatrix (nearestSignMatrix Z)-complexifyRealMatrix Z) i j)=
      (nearestSignMatrix Z i j-Z i j)^2 := by
    simp [complexifyRealMatrix,Complex.normSq_apply,pow_two]
  rw [he]
  exact nearest_sign_error_bound (Z i j)

theorem euclidean_op_add_bound {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    PhaseGeometry.euclideanOperatorNorm (A+B) ≤ PhaseGeometry.euclideanOperatorNorm A+PhaseGeometry.euclideanOperatorNorm B := by
  unfold PhaseGeometry.euclideanOperatorNorm
  rw [map_add]
  exact norm_add_le _ _

theorem euclidean_op_mul_bound {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    PhaseGeometry.euclideanOperatorNorm (A*B) ≤ PhaseGeometry.euclideanOperatorNorm A*PhaseGeometry.euclideanOperatorNorm B := by
  unfold PhaseGeometry.euclideanOperatorNorm
  rw [map_mul]
  exact norm_mul_le _ _

theorem euclidean_op_conjTranspose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    PhaseGeometry.euclideanOperatorNorm Aᴴ=PhaseGeometry.euclideanOperatorNorm A := by
  open scoped Matrix.Norms.L2Operator in
    exact Matrix.l2_opNorm_conjTranspose A

theorem euclidean_op_entry_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ‖A i j‖ ≤ PhaseGeometry.euclideanOperatorNorm A := by
  let x : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (Pi.single j 1)
  let y : EuclideanSpace ℂ (Fin n) := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) A x
  have hx2 : ‖x‖^2=1 := by
    rw [PiLp.norm_sq_eq_of_L2]
    change (∑ k : Fin n,‖(Pi.single j (1 : ℂ) : Fin n → ℂ) k‖^2)=1
    have he (k : Fin n) : ‖(Pi.single j (1 : ℂ) : Fin n → ℂ) k‖^2=if k=j then (1 : ℝ) else 0 := by
      by_cases hk : k=j
      · subst k; simp
      · simp [Pi.single_apply,hk,Ne.symm hk]
    simp_rw [he]
    simp
  have hx : ‖x‖=1 := by nlinarith [norm_nonneg x]
  have hy : y.ofLp i=A i j := by
    rw [PhaseGeometry.euclidean_matrix_apply_entries]
    simp [x,Pi.single_apply,eq_comm]
  have hs : ‖y.ofLp i‖^2 ≤ ‖y‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    exact Finset.single_le_sum (fun k hk => sq_nonneg ‖y.ofLp k‖) (Finset.mem_univ i)
  have hb := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) A).le_opNorm x
  rw [hx,mul_one] at hb
  change ‖y‖ ≤ PhaseGeometry.euclideanOperatorNorm A at hb
  rw [hy] at hs
  have hp : 0 ≤ PhaseGeometry.euclideanOperatorNorm A := norm_nonneg _
  nlinarith [norm_nonneg y,norm_nonneg (A i j)]

theorem complexify_scaled_orthogonal {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ)
    (hZ : Z*Zᵀ=(n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) :
    complexifyRealMatrix Z*(complexifyRealMatrix Z)ᴴ=(n : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have hrow (i j : Fin n) : (∑ k,Z i k*Z j k)=if i=j then (n : ℝ) else 0 := by
    have hh := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hZ
    simpa [Matrix.mul_apply,Matrix.transpose_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply] using hh
  ext i j
  change (∑ k,(Z i k : ℂ)*conj (Z j k : ℂ))=(n : ℂ)*(if i=j then 1 else 0)
  simp only [Complex.conj_ofReal,← Complex.ofReal_mul,← Complex.ofReal_sum]
  rw [hrow]
  split_ifs <;> simp

open scoped Matrix.Norms.L2Operator in
theorem complexify_scaled_operator_norm {n : ℕ} (hn : 0<n) (Z : Matrix (Fin n) (Fin n) ℝ)
    (hZ : Z*Zᵀ=(n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) :
    PhaseGeometry.euclideanOperatorNorm (complexifyRealMatrix Z)=Real.sqrt (n : ℝ) := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have he := PhaseGeometry.euclideanOperatorNorm_gram (complexifyRealMatrix Z)
  rw [complexify_scaled_orthogonal Z hZ,PhaseGeometry.euclideanOperatorNorm_smul,Complex.norm_natCast] at he
  have hi : PhaseGeometry.euclideanOperatorNorm (1 : Matrix (Fin n) (Fin n) ℂ)=1 := by
    unfold PhaseGeometry.euclideanOperatorNorm
    rw [map_one]
    exact norm_one
  rw [hi,mul_one] at he
  have hp : 0 ≤ PhaseGeometry.euclideanOperatorNorm (complexifyRealMatrix Z) := norm_nonneg _
  rw [he,Real.sqrt_sq hp]

theorem complex_rounding_operator_sq_le {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ) :
    PhaseGeometry.euclideanOperatorNorm (complexifyRealMatrix (nearestSignMatrix Z)-complexifyRealMatrix Z)^2 ≤ quarticFlatness Z := by
  let E : Matrix (Fin n) (Fin n) ℂ := complexifyRealMatrix (nearestSignMatrix Z)-complexifyRealMatrix Z
  have hs := PhaseGeometry.euclideanOperatorNorm_le_frobenius E
  have hS : 0 ≤ PhaseGeometry.matrixFrobeniusSq E :=
    Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => Complex.normSq_nonneg _))
  have he := Real.sq_sqrt hS
  have hp : 0 ≤ PhaseGeometry.euclideanOperatorNorm E := norm_nonneg _
  have hb := complex_rounding_frobenius_le Z
  change PhaseGeometry.matrixFrobeniusSq E ≤ quarticFlatness Z at hb
  nlinarith [Real.sqrt_nonneg (PhaseGeometry.matrixFrobeniusSq E)]

noncomputable def realFlatnessThreshold (n : ℕ) : ℝ :=
  (Real.sqrt ((n : ℝ)+2)-Real.sqrt (n : ℝ))^2

theorem flatness_threshold_quadratic_bound (n : ℕ) {e : ℝ} (he : 0 ≤ e)
    (hs : e^2<realFlatnessThreshold n) : 2*Real.sqrt (n : ℝ)*e+e^2<2 := by
  have hA : (Real.sqrt ((n : ℝ)+2))^2=(n : ℝ)+2 := Real.sq_sqrt (by positivity)
  have hB : (Real.sqrt (n : ℝ))^2=(n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hpos : Real.sqrt (n : ℝ)<Real.sqrt ((n : ℝ)+2) := Real.sqrt_lt_sqrt (Nat.cast_nonneg n) (by linarith)
  unfold realFlatnessThreshold at hs
  have hd : e<Real.sqrt ((n : ℝ)+2)-Real.sqrt (n : ℝ) := by nlinarith
  have hp : 0<(Real.sqrt ((n : ℝ)+2)-Real.sqrt (n : ℝ)-e)*
      (Real.sqrt ((n : ℝ)+2)-Real.sqrt (n : ℝ)+e+2*Real.sqrt (n : ℝ)) :=
    mul_pos (by linarith) (by nlinarith [Real.sqrt_nonneg (n : ℝ)])
  nlinarith

theorem rounded_real_gram_operator_bound {n : ℕ} (hn : 0<n)
    (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : Z*Zᵀ=(n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) :
    PhaseGeometry.euclideanOperatorNorm
      (complexifyRealMatrix (nearestSignMatrix Z)*(complexifyRealMatrix (nearestSignMatrix Z))ᴴ-(n : ℂ) • 1) ≤
      2*Real.sqrt (n : ℝ)*PhaseGeometry.euclideanOperatorNorm (complexifyRealMatrix (nearestSignMatrix Z)-complexifyRealMatrix Z)+
      PhaseGeometry.euclideanOperatorNorm (complexifyRealMatrix (nearestSignMatrix Z)-complexifyRealMatrix Z)^2 := by
  let C := complexifyRealMatrix Z
  let Q := complexifyRealMatrix (nearestSignMatrix Z)
  let E : Matrix (Fin n) (Fin n) ℂ := Q-C
  have hQ : Q=C+E := by dsimp [E]; abel
  have hC : C*Cᴴ=(n : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := complexify_scaled_orthogonal Z hZ
  have hdecomp : Q*Qᴴ-(n : ℂ) • 1=C*Eᴴ+E*Cᴴ+E*Eᴴ := by
    rw [hQ,Matrix.conjTranspose_add,add_mul,mul_add,mul_add,hC]
    abel
  have hCn : PhaseGeometry.euclideanOperatorNorm C=Real.sqrt (n : ℝ) := complexify_scaled_operator_norm hn Z hZ
  have h1 := euclidean_op_mul_bound C Eᴴ
  have h2 := euclidean_op_mul_bound E Cᴴ
  rw [euclidean_op_conjTranspose,hCn] at h1
  rw [euclidean_op_conjTranspose,hCn] at h2
  have h3 := euclidean_op_add_bound (C*Eᴴ) (E*Cᴴ)
  have h4 := euclidean_op_add_bound (C*Eᴴ+E*Cᴴ) (E*Eᴴ)
  have h5 := PhaseGeometry.euclideanOperatorNorm_gram E
  change PhaseGeometry.euclideanOperatorNorm (Q*Qᴴ-(n : ℂ) • 1) ≤
    2*Real.sqrt (n : ℝ)*PhaseGeometry.euclideanOperatorNorm E+PhaseGeometry.euclideanOperatorNorm E^2
  rw [hdecomp]
  nlinarith

theorem rounded_real_gram_operator_lt_two {n : ℕ} (hn : 0<n)
    (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : Z*Zᵀ=(n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hflat : quarticFlatness Z<realFlatnessThreshold n) :
    PhaseGeometry.euclideanOperatorNorm
      (complexifyRealMatrix (nearestSignMatrix Z)*(complexifyRealMatrix (nearestSignMatrix Z))ᴴ-(n : ℂ) • 1)<2 := by
  have hs := complex_rounding_operator_sq_le Z
  have hp : 0 ≤ PhaseGeometry.euclideanOperatorNorm (complexifyRealMatrix (nearestSignMatrix Z)-complexifyRealMatrix Z) := norm_nonneg _
  have hbound := flatness_threshold_quadratic_bound n hp (hs.trans_lt hflat)
  exact (rounded_real_gram_operator_bound hn Z hZ).trans_lt hbound

theorem even_real_sign_gram_zero_of_norm_lt_two {n : ℕ} (hn : Even n)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : IsSignMatrix Q) (i j : Fin n)
    (hsmall : ‖PhaseGeometry.complexRowGram (complexifyRealMatrix Q) i j‖<2) :
    PhaseGeometry.complexRowGram (complexifyRealMatrix Q) i j=0 := by
  have hroot (a b : Fin n) : PhaseGeometry.IsFourthRoot (complexifyRealMatrix Q a b) := by
    rcases hQ a b with h | h
    · exact Or.inl (by simp [complexifyRealMatrix,h])
    · exact Or.inr (Or.inl (by simp [complexifyRealMatrix,h]))
  obtain ⟨a,b,he,hpar⟩ := PhaseGeometry.fourth_root_sum_gaussian
    (fun k => complexifyRealMatrix Q i k*conj (complexifyRealMatrix Q j k))
    (fun k => PhaseGeometry.fourth_root_mul_conj (hroot i k) (hroot j k))
  have him : (PhaseGeometry.complexRowGram (complexifyRealMatrix Q) i j).im=0 := by
    simp [PhaseGeometry.complexRowGram,complexifyRealMatrix]
  have hb : b=0 := by
    have hh := congrArg Complex.im he
    change (PhaseGeometry.complexRowGram (complexifyRealMatrix Q) i j).im=_ at hh
    rw [him] at hh
    have hbR : (b : ℝ)=0 := by simpa using hh.symm
    exact_mod_cast hbR
  subst b
  have hEvenN : Even (n : ℤ) := by exact_mod_cast hn
  have hEvenA : Even a := by
    have hh := hpar.add hEvenN
    simpa using hh
  have hnorm : ‖(a : ℂ)‖<2 := by
    change ‖∑ k,complexifyRealMatrix Q i k*conj (complexifyRealMatrix Q j k)‖<2 at hsmall
    rw [he] at hsmall
    simpa using hsmall
  have haR : |(a : ℝ)|<2 := by simpa using hnorm
  have ha : (-2 : ℤ)<a ∧ a<2 := by exact_mod_cast (abs_lt.mp haR)
  obtain ⟨z,hz⟩ := hEvenA
  have ha0 : a=0 := by omega
  change (∑ k,complexifyRealMatrix Q i k*conj (complexifyRealMatrix Q j k))=0
  simpa [ha0] using he

theorem real_flatness_rounding_hadamard {n : ℕ} (hn : 0<n) (hfour : 4 ∣ n)
    (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : Z*Zᵀ=(n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hflat : quarticFlatness Z<realFlatnessThreshold n) : Matrix.IsHadamard (nearestSignMatrix Z) := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have heven : Even n := by obtain ⟨k,hk⟩ := hfour; exact ⟨2*k,by omega⟩
  let Q := nearestSignMatrix Z
  let C := complexifyRealMatrix Q
  let D : Matrix (Fin n) (Fin n) ℂ := C*Cᴴ-(n : ℂ) • 1
  have hD : PhaseGeometry.euclideanOperatorNorm D<2 := rounded_real_gram_operator_lt_two hn Z hZ hflat
  have hQ := nearest_signs_isSignMatrix Z
  have hgram : Q*Qᵀ=(n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    by_cases hij : i=j
    · subst j
      change (∑ k,Q i k*Q i k)=(n : ℝ)*(if i=i then 1 else 0)
      have he (k : Fin n) : Q i k*Q i k=1 := by have hh := isSign_sq (hQ i k); nlinarith
      simp [he]
    · have he : D i j=PhaseGeometry.complexRowGram C i j := by
        change (∑ k,C i k*conj (C j k))-(n : ℂ)*(if i=j then 1 else 0)=_
        simp only [hij,if_false,mul_zero,sub_zero,PhaseGeometry.complexRowGram]
      have hb : ‖PhaseGeometry.complexRowGram C i j‖<2 := by
        rw [← he]
        exact (euclidean_op_entry_bound D i j).trans_lt hD
      have hz := even_real_sign_gram_zero_of_norm_lt_two heven Q hQ i j hb
      have hreal : (∑ k,Q i k*Q j k)=0 := by
        have hr := congrArg Complex.re hz
        simpa [PhaseGeometry.complexRowGram,complexifyRealMatrix,C] using hr
      change (∑ k,Q i k*Q j k)=(n : ℝ)*(if i=j then 1 else 0)
      simp [hreal,hij]
  exact isHadamard_mathlib ⟨hQ,by simpa only [Q,Fintype.card_fin] using hgram⟩

theorem realFlatnessThreshold_lower (n : ℕ) : 1/((n : ℝ)+2)<realFlatnessThreshold n := by
  have hA : (Real.sqrt ((n : ℝ)+2))^2=(n : ℝ)+2 := Real.sq_sqrt (by positivity)
  have hB : (Real.sqrt (n : ℝ))^2=(n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hpos : Real.sqrt (n : ℝ)<Real.sqrt ((n : ℝ)+2) := Real.sqrt_lt_sqrt (Nat.cast_nonneg n) (by linarith)
  have hAp : 0<Real.sqrt ((n : ℝ)+2) := Real.sqrt_pos.mpr (by positivity)
  have hsum : (Real.sqrt ((n : ℝ)+2)+Real.sqrt (n : ℝ))^2<4*((n : ℝ)+2) := by
    nlinarith [mul_pos hAp (sub_pos.mpr hpos)]
  have hdiff : (Real.sqrt ((n : ℝ)+2)-Real.sqrt (n : ℝ))*(Real.sqrt ((n : ℝ)+2)+Real.sqrt (n : ℝ))=2 := by nlinarith
  have hδ : 0<realFlatnessThreshold n := sq_pos_of_pos (sub_pos.mpr hpos)
  have hprod : realFlatnessThreshold n*(Real.sqrt ((n : ℝ)+2)+Real.sqrt (n : ℝ))^2=4 := by
    calc
      _ = ((Real.sqrt ((n : ℝ)+2)-Real.sqrt (n : ℝ))*(Real.sqrt ((n : ℝ)+2)+Real.sqrt (n : ℝ)))^2 := by unfold realFlatnessThreshold; ring
      _ = 4 := by rw [hdiff]; norm_num
  apply (div_lt_iff₀ (show 0<(n : ℝ)+2 by positivity)).mpr
  have hp := mul_pos hδ (sub_pos.mpr hsum)
  nlinarith

theorem quarticFlatness_identity {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ)
    (hZ : Z*Zᵀ=(n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) :
    quarticFlatness Z=(∑ i,∑ j,Z i j^4)-(n : ℝ)^2 := by
  have hrow (i : Fin n) : (∑ j,Z i j^2)=(n : ℝ) := by
    have hh := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i i) hZ
    simpa [Matrix.mul_apply,Matrix.transpose_apply,pow_two] using hh
  have henergy : (∑ i,∑ j,Z i j^2)=(n : ℝ)^2 := by simp_rw [hrow]; simp; ring
  have he (i j : Fin n) : (Z i j^2-1)^2=Z i j^4-2*Z i j^2+1 := by ring
  unfold quarticFlatness
  simp_rw [he,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
  rw [henergy]
  simp
  ring

theorem nearest_sign_fixed_entry {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (h : IsSign (Z i j)) :
    nearestSignMatrix Z i j=Z i j := by
  rcases h with h | h <;> norm_num [nearestSignMatrix,h]

theorem noncompletable_real_flatness_gap {n : ℕ} (hn : 0<n) (hfour : 4 ∣ n)
    {ι : Type*} (P : Matrix ι (Fin n) ℝ) (hP : IsSignMatrix P) (e : ι → Fin n)
    (hno : ¬ ∃ H : Matrix (Fin n) (Fin n) ℝ,Matrix.IsHadamard H ∧ ∀ i j,H (e i) j=P i j)
    (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : Z*Zᵀ=(n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hret : ∀ i j,Z (e i) j=P i j) :
    realFlatnessThreshold n ≤ quarticFlatness Z ∧ 1/((n : ℝ)+2)<realFlatnessThreshold n := by
  refine ⟨?_,realFlatnessThreshold_lower n⟩
  by_contra! hh
  have hH := real_flatness_rounding_hadamard hn hfour Z hZ hh
  apply hno
  refine ⟨nearestSignMatrix Z,hH,?_⟩
  intro i j
  calc
    _ = Z (e i) j := nearest_sign_fixed_entry Z (e i) j (by rw [hret]; exact hP i j)
    _ = _ := hret i j
end CompletionTheory
