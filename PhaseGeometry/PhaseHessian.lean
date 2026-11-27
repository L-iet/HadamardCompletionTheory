/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Analysis.Matrix.Normed
public import PhaseGeometry.IndexedCalculus
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Basic.Complex.BigOperators
@[expose] public section
namespace PhaseGeometry
open Complex
open scoped ComplexConjugate Matrix.Norms.Elementwise

noncomputable def phaseEntry (a x : ℝ) : ℂ := (a : ℂ)*Complex.exp ((x : ℂ)*Complex.I)

theorem phaseEntry_mul_conj (a b x y : ℝ) :
    phaseEntry a x*conj (phaseEntry b y)=phaseEntry (a*b) (x-y) := by
  simp only [phaseEntry,map_mul,Complex.conj_ofReal,← Complex.exp_conj,Complex.conj_I]
  rw [Complex.ofReal_mul]
  calc
    _ = ((a : ℂ)*(b : ℂ))*(Complex.exp ((x : ℂ)*I)*Complex.exp ((y : ℂ)*(-I))) := by ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      push_cast
      ring

theorem phaseEntry_re (a x : ℝ) : (phaseEntry a x).re=a*Real.cos x := by
  simp [phaseEntry,Complex.mul_re,Complex.exp_ofReal_mul_I_re]

theorem phaseEntry_mul_conj_self (a x : ℝ) :
    phaseEntry a x*conj (phaseEntry a x)=(a^2 : ℝ) := by
  rw [phaseEntry_mul_conj]
  simp [phaseEntry,pow_two]

theorem normSq_eq_mul_conj_re (z : ℂ) : Complex.normSq z=(z*conj z).re := by
  simp [Complex.normSq_apply,Complex.mul_re]

theorem phase_sum_normSq {α : Type*} [Fintype α] (a x : α → ℝ) :
    Complex.normSq (∑ i,phaseEntry (a i) (x i))=
      ∑ i,∑ j,a i*a j*Real.cos (x i-x j) := by
  rw [normSq_eq_mul_conj_re,map_sum,Finset.sum_mul]
  simp_rw [Finset.mul_sum,Complex.re_sum,phaseEntry_mul_conj,phaseEntry_re]

noncomputable def phaseMatrix {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ)
    (θ : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i a => phaseEntry (H i a : ℝ) (θ i a)

noncomputable def phaseGram {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ)
    (θ : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  phaseMatrix H θ*(phaseMatrix H θ).conjTranspose

noncomputable def phaseEnergy {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ)
    (θ : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i,∑ j,Complex.normSq (phaseGram H θ i j-if i=j then (n : ℂ) else 0)

noncomputable def rectangleWeight {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ)
    (i j a b : Fin n) : ℝ := ((H i a : ℝ)*(H j a : ℝ))*((H i b : ℝ)*(H j b : ℝ))

noncomputable def rectangleAngle {n : ℕ} (θ : Matrix (Fin n) (Fin n) ℝ)
    (i j a b : Fin n) : ℝ := (θ i a-θ j a)-(θ i b-θ j b)

theorem phaseGram_entry {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ)
    (θ : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    phaseGram H θ i j=∑ a,phaseEntry ((H i a : ℝ)*(H j a : ℝ)) (θ i a-θ j a) := by
  change (∑ a,phaseEntry (H i a : ℝ) (θ i a)*conj (phaseEntry (H j a : ℝ) (θ j a)))=_
  simp_rw [phaseEntry_mul_conj]

theorem phaseGram_diagonal {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ)
    (hH : Indexed.IsSign H) (θ : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    phaseGram H θ i i=(n : ℂ) := by
  have hs (a : Fin n) : (H i a : ℝ)*(H i a : ℝ)=1 := by
    rcases hH i a with h | h <;> norm_num [h]
  rw [phaseGram_entry]
  simp only [hs,sub_self]
  simp [phaseEntry]

theorem phaseGram_normSq_rectangles {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ)
    (θ : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    Complex.normSq (phaseGram H θ i j)=
      ∑ a,∑ b,rectangleWeight H i j a b*Real.cos (rectangleAngle θ i j a b) := by
  rw [phaseGram_entry,phase_sum_normSq]
  rfl

theorem phaseEnergy_eq_rectangles {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ)
    (hH : Indexed.IsSign H) (θ : Matrix (Fin n) (Fin n) ℝ) :
    phaseEnergy H θ=(∑ i,∑ j,∑ a,∑ b,
      rectangleWeight H i j a b*Real.cos (rectangleAngle θ i j a b))-(n : ℝ)^3 := by
  have he (i j : Fin n) : Complex.normSq (phaseGram H θ i j-if i=j then (n : ℂ) else 0)=
      Complex.normSq (phaseGram H θ i j)-(if i=j then (n : ℝ)^2 else 0) := by
    by_cases hij : i=j
    · subst j
      rw [if_pos rfl,phaseGram_diagonal H hH]
      simp [pow_two]
    · simp [hij]
  unfold phaseEnergy
  simp_rw [he,phaseGram_normSq_rectangles,Finset.sum_sub_distrib]
  have hs : (∑ i : Fin n,∑ j : Fin n,if i=j then (n : ℝ)^2 else 0)=(n : ℝ)^3 := by
    simp
    ring
  rw [hs]

theorem rectangleAngle_smul {n : ℕ} (θ : Matrix (Fin n) (Fin n) ℝ)
    (t : ℝ) (i j a b : Fin n) :
    rectangleAngle (t • θ) i j a b=t*rectangleAngle θ i j a b := by
  simp only [rectangleAngle,Matrix.smul_apply,smul_eq_mul]
  ring

theorem phaseEnergy_line_formula {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ)
    (hH : Indexed.IsSign H) (θ : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    phaseEnergy H (t • θ)=(∑ i,∑ j,∑ a,∑ b,
      rectangleWeight H i j a b*Real.cos (t*rectangleAngle θ i j a b))-(n : ℝ)^3 := by
  simp only [phaseEnergy_eq_rectangles H hH,rectangleAngle_smul]

theorem cosine_line_hasDeriv (a b t : ℝ) :
    HasDerivAt (fun s : ℝ => a*Real.cos (s*b)) (-a*b*Real.sin (t*b)) t := by
  have h := ((Real.hasDerivAt_cos (t*b)).comp t ((hasDerivAt_id t).mul_const b)).const_mul a
  convert! h using 1 <;> ring

theorem cosine_line_second (a b : ℝ) :
    HasDerivAt (fun t : ℝ => -a*b*Real.sin (t*b)) (-a*b^2) 0 := by
  have h := ((Real.hasDerivAt_sin ((0 : ℝ)*b)).comp 0 ((hasDerivAt_id (0 : ℝ)).mul_const b)).const_mul (-a*b)
  convert! h using 1 <;> simp only [zero_mul,Real.cos_zero,one_mul] <;> ring

theorem phaseEnergy_line_hasDeriv {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ)
    (hH : Indexed.IsSign H) (θ : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => phaseEnergy H (s • θ))
      (∑ i,∑ j,∑ a,∑ b,-rectangleWeight H i j a b*rectangleAngle θ i j a b*
        Real.sin (t*rectangleAngle θ i j a b)) t := by
  have hd : HasDerivAt (fun s : ℝ => ∑ i,∑ j,∑ a,∑ b,
      rectangleWeight H i j a b*Real.cos (s*rectangleAngle θ i j a b))
      (∑ i,∑ j,∑ a,∑ b,-rectangleWeight H i j a b*rectangleAngle θ i j a b*
        Real.sin (t*rectangleAngle θ i j a b)) t := by
    apply HasDerivAt.fun_sum
    intro i _
    apply HasDerivAt.fun_sum
    intro j _
    apply HasDerivAt.fun_sum
    intro a _
    apply HasDerivAt.fun_sum
    intro b _
    exact cosine_line_hasDeriv _ _ _
  have hh := hd.sub_const ((n : ℝ)^3)
  convert! hh using 1
  funext s
  exact phaseEnergy_line_formula H hH θ s

theorem phaseEnergy_line_stationary {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ)
    (hH : Indexed.IsSign H) (θ : Matrix (Fin n) (Fin n) ℝ) :
    deriv (fun t : ℝ => phaseEnergy H (t • θ)) 0=0 := by
  simpa only [zero_mul,Real.sin_zero,mul_zero,Finset.sum_const_zero] using
    (phaseEnergy_line_hasDeriv H hH θ 0).deriv

theorem phaseEnergy_line_second_derivative {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ)
    (hH : Indexed.IsSign H) (θ : Matrix (Fin n) (Fin n) ℝ) :
    deriv (deriv (fun t : ℝ => phaseEnergy H (t • θ))) 0=
      -(∑ i,∑ j,∑ a,∑ b,rectangleWeight H i j a b*(rectangleAngle θ i j a b)^2) := by
  have hd : deriv (fun t : ℝ => phaseEnergy H (t • θ)) = fun t : ℝ =>
      ∑ i,∑ j,∑ a,∑ b,-rectangleWeight H i j a b*rectangleAngle θ i j a b*
        Real.sin (t*rectangleAngle θ i j a b) := by
    funext t
    exact (phaseEnergy_line_hasDeriv H hH θ t).deriv
  rw [hd]
  have hs : HasDerivAt (fun t : ℝ => ∑ i,∑ j,∑ a,∑ b,
      -rectangleWeight H i j a b*rectangleAngle θ i j a b*Real.sin (t*rectangleAngle θ i j a b))
      (∑ i,∑ j,∑ a,∑ b,-rectangleWeight H i j a b*(rectangleAngle θ i j a b)^2) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    apply HasDerivAt.fun_sum
    intro j _
    apply HasDerivAt.fun_sum
    intro a _
    apply HasDerivAt.fun_sum
    intro b _
    exact cosine_line_second _ _
  simpa only [neg_mul,Finset.sum_neg_distrib] using hs.deriv

theorem symmetric_sum_twice_upper {n : ℕ} (f : Fin n → Fin n → ℝ)
    (hsym : ∀ i j,f i j=f j i) (hdiag : ∀ i,f i i=0) :
    (∑ i,∑ j,f i j)=2*(∑ i,∑ j,if i<j then f i j else 0) := by
  let g := fun i j => if i<j then f i j else 0
  have he (i j : Fin n) : f i j=g i j+g j i := by
    rcases lt_trichotomy i j with h | h | h
    · simp [g,h,not_lt.mpr h.le]
    · subst j; simp [g,hdiag]
    · simp [g,h,not_lt.mpr h.le,hsym i j]
  calc
    _ = ∑ i,∑ j,(g i j+g j i) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact he i j
    _ = (∑ i,∑ j,g i j)+(∑ i,∑ j,g j i) := by simp_rw [Finset.sum_add_distrib]
    _ = _ := by
      have hswap : (∑ i,∑ j,g j i)=(∑ i,∑ j,g i j) := Finset.sum_comm
      rw [hswap]
      ring

theorem rectangle_quadratic_sum_four_upper {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ)
    (θ : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i,∑ j,∑ a,∑ b,rectangleWeight H i j a b*(rectangleAngle θ i j a b)^2)=
      4*(∑ i,∑ j,∑ a,∑ b,if i<j ∧ a<b then
        rectangleWeight H i j a b*(rectangleAngle θ i j a b)^2 else 0) := by
  let f := fun i j a b => rectangleWeight H i j a b*(rectangleAngle θ i j a b)^2
  have hr : ∀ i j,(∑ a,∑ b,f i j a b)=(∑ a,∑ b,f j i a b) := by
    intro i j
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    dsimp [f,rectangleWeight,rectangleAngle]
    ring
  have hd : ∀ i,(∑ a,∑ b,f i i a b)=0 := by
    intro i
    simp [f,rectangleAngle]
  have hrows := symmetric_sum_twice_upper (fun i j => ∑ a,∑ b,f i j a b) hr hd
  have hcols (i j : Fin n) : (∑ a,∑ b,f i j a b)=2*(∑ a,∑ b,if a<b then f i j a b else 0) := by
    apply symmetric_sum_twice_upper
    · intro a b
      dsimp [f,rectangleWeight,rectangleAngle]
      ring
    · intro a
      simp [f,rectangleAngle]
  have hinner (i j : Fin n) : (if i<j then ∑ a,∑ b,f i j a b else 0)=
      2*(∑ a,∑ b,if i<j ∧ a<b then f i j a b else 0) := by
    by_cases hij : i<j
    · simp only [hij,ite_true,true_and]
      exact hcols i j
    · simp [hij]
  change (∑ i,∑ j,∑ a,∑ b,f i j a b)=4*(∑ i,∑ j,∑ a,∑ b,if i<j ∧ a<b then f i j a b else 0)
  rw [hrows]
  simp_rw [hinner,← Finset.mul_sum]
  ring

theorem phaseEnergy_second_upper_rectangles {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ)
    (hH : Indexed.IsSign H) (θ : Matrix (Fin n) (Fin n) ℝ) :
    deriv (deriv (fun t : ℝ => phaseEnergy H (t • θ))) 0=
      -4*(∑ i,∑ j,∑ a,∑ b,if i<j ∧ a<b then
        rectangleWeight H i j a b*(rectangleAngle θ i j a b)^2 else 0) := by
  rw [phaseEnergy_line_second_derivative H hH,rectangle_quadratic_sum_four_upper]
  ring

def rectangleVector {n : ℕ} (i j a b : Fin n) (p : Fin n × Fin n) : ℤ :=
  (if p=(i,a) then 1 else 0)+(if p=(j,b) then 1 else 0)-
    (if p=(i,b) then 1 else 0)-(if p=(j,a) then 1 else 0)

def rectangleWeightInt {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) (i j a b : Fin n) : ℤ :=
  (H i a*H j a)*(H i b*H j b)

theorem rectangleWeightInt_cast {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) (i j a b : Fin n) :
    (rectangleWeightInt H i j a b : ℝ)=rectangleWeight H i j a b := by
  simp only [rectangleWeightInt,rectangleWeight,Int.cast_mul]

theorem rectangleVector_dot {n : ℕ} (θ : Matrix (Fin n) (Fin n) ℝ) (i j a b : Fin n) :
    (∑ p : Fin n × Fin n,(rectangleVector i j a b p : ℝ)*θ p.1 p.2)=rectangleAngle θ i j a b := by
  have hc (c p : Fin n × Fin n) : (((if p=c then (1 : ℤ) else 0) : ℤ) : ℝ)=
      if p=c then (1 : ℝ) else 0 := by split_ifs <;> norm_num
  simp only [rectangleVector,Int.cast_add,Int.cast_sub,hc,add_mul,sub_mul,ite_mul,
    one_mul,zero_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  dsimp [rectangleAngle]
  ring

theorem integer_outer_sum_quadratic {R K : Type*} [Fintype R] [Fintype K]
    (c : R → ℤ) (v : R → K → ℤ) (x : K → ℝ) :
    (∑ p,x p*(∑ q,((∑ r,c r*v r p*v r q : ℤ) : ℝ)*x q))=
      ∑ r,(c r : ℝ)*(∑ p,(v r p : ℝ)*x p)^2 := by
  let F := fun p q r => (c r : ℝ)*((v r p : ℝ)*x p)*((v r q : ℝ)*x q)
  have hexpand : (∑ p,x p*(∑ q,((∑ r,c r*v r p*v r q : ℤ) : ℝ)*x q))=
      ∑ p,∑ q,∑ r,F p q r := by
    apply Finset.sum_congr rfl
    intro p _
    simp only [Int.cast_sum,Int.cast_mul,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro r _
    dsimp [F]
    ring
  have hterm (r : R) : (∑ p,∑ q,F p q r)=(c r : ℝ)*(∑ p,(v r p : ℝ)*x p)^2 := by
    rw [pow_two]
    simp only [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    dsimp [F]
    ring
  calc
    _ = ∑ p,∑ q,∑ r,F p q r := hexpand
    _ = ∑ p,∑ r,∑ q,F p q r := by
      apply Finset.sum_congr rfl
      intro p _
      exact Finset.sum_comm
    _ = ∑ r,∑ p,∑ q,F p q r := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun r _ => hterm r)

def integerPhaseHessian {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℤ := fun p q =>
  -4*(∑ i,∑ j,∑ a,∑ b,if i<j ∧ a<b then
    rectangleWeightInt H i j a b*rectangleVector i j a b p*rectangleVector i j a b q else 0)

theorem integerPhaseHessian_symmetric {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) :
    (integerPhaseHessian H).transpose=integerPhaseHessian H := by
  ext p q
  change integerPhaseHessian H q p=integerPhaseHessian H p q
  unfold integerPhaseHessian
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> ring

theorem rectangle_bilinear_sum_four_upper {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ)
    (θ φ : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i,∑ j,∑ a,∑ b,rectangleWeight H i j a b*rectangleAngle θ i j a b*rectangleAngle φ i j a b)=
      4*(∑ i,∑ j,∑ a,∑ b,if i<j ∧ a<b then
        rectangleWeight H i j a b*rectangleAngle θ i j a b*rectangleAngle φ i j a b else 0) := by
  let f := fun i j a b => rectangleWeight H i j a b*rectangleAngle θ i j a b*rectangleAngle φ i j a b
  have hr : ∀ i j,(∑ a,∑ b,f i j a b)=(∑ a,∑ b,f j i a b) := by
    intro i j
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    dsimp [f,rectangleWeight,rectangleAngle]
    ring
  have hd : ∀ i,(∑ a,∑ b,f i i a b)=0 := by
    intro i
    simp [f,rectangleAngle]
  have hrows := symmetric_sum_twice_upper (fun i j => ∑ a,∑ b,f i j a b) hr hd
  have hcols (i j : Fin n) : (∑ a,∑ b,f i j a b)=2*(∑ a,∑ b,if a<b then f i j a b else 0) := by
    apply symmetric_sum_twice_upper
    · intro a b
      dsimp [f,rectangleWeight,rectangleAngle]
      ring
    · intro a
      simp [f,rectangleAngle]
  have hinner (i j : Fin n) : (if i<j then ∑ a,∑ b,f i j a b else 0)=
      2*(∑ a,∑ b,if i<j ∧ a<b then f i j a b else 0) := by
    by_cases hij : i<j
    · simp only [hij,ite_true,true_and]
      exact hcols i j
    · simp [hij]
  change (∑ i,∑ j,∑ a,∑ b,f i j a b)=4*(∑ i,∑ j,∑ a,∑ b,if i<j ∧ a<b then f i j a b else 0)
  rw [hrows]
  simp_rw [hinner,← Finset.mul_sum]
  ring


abbrev RectangleIndex (n : ℕ) := (Fin n × Fin n) × (Fin n × Fin n)

theorem rectangleAngle_add {n : ℕ} (θ φ : Matrix (Fin n) (Fin n) ℝ) (i j a b : Fin n) :
    rectangleAngle (θ+φ) i j a b=rectangleAngle θ i j a b+rectangleAngle φ i j a b := by
  simp only [rectangleAngle,Matrix.add_apply]
  ring

theorem phaseEnergy_contDiff {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ)
    (hH : Indexed.IsSign H) (m : ℕ) : ContDiff ℝ m (phaseEnergy H) := by
  have hfun : phaseEnergy H = fun θ : Matrix (Fin n) (Fin n) ℝ =>
      (∑ i,∑ j,∑ a,∑ b,rectangleWeight H i j a b*Real.cos (rectangleAngle θ i j a b))-(n : ℝ)^3 := by
    funext θ
    exact phaseEnergy_eq_rectangles H hH θ
  rw [hfun]
  dsimp only [rectangleAngle]
  fun_prop

theorem affine_cosine_hasDeriv (c a b s t : ℝ) :
    HasDerivAt (fun u : ℝ => c*Real.cos (s*a+u*b)) (-c*b*Real.sin (s*a+t*b)) t := by
  have hi : HasDerivAt (fun u : ℝ => s*a+u*b) b t := by
    convert! ((hasDerivAt_id t).mul_const b).const_add (s*a) using 1 <;> ring
  have h := ((Real.hasDerivAt_cos (s*a+t*b)).comp t hi).const_mul c
  convert! h using 1 <;> ring

theorem sine_line_zero_hasDeriv (a b : ℝ) :
    HasDerivAt (fun t : ℝ => a*Real.sin (t*b)) (a*b) 0 := by
  have h := ((Real.hasDerivAt_sin ((0 : ℝ)*b)).comp 0 ((hasDerivAt_id (0 : ℝ)).mul_const b)).const_mul a
  convert! h using 1 <;> simp only [zero_mul,Real.cos_zero,one_mul] <;> ring

theorem finite_cosine_mixed_derivative {R : Type*} [Fintype R]
    (c a b : R → ℝ) (d : ℝ) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => (∑ r,c r*Real.cos (s*a r+t*b r))-d) 0) 0=
      -(∑ r,c r*a r*b r) := by
  have ht (s : ℝ) : HasDerivAt
      (fun t : ℝ => (∑ r,c r*Real.cos (s*a r+t*b r))-d)
      (∑ r,-c r*b r*Real.sin (s*a r)) 0 := by
    have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun r _ => affine_cosine_hasDeriv (c r) (a r) (b r) s 0)
    simpa only [zero_mul,add_zero] using hd.sub_const d
  have he : (fun s : ℝ => deriv (fun t : ℝ => (∑ r,c r*Real.cos (s*a r+t*b r))-d) 0)=
      fun s : ℝ => ∑ r,-c r*b r*Real.sin (s*a r) := by
    funext s
    exact (ht s).deriv
  rw [he]
  have hs : HasDerivAt (fun s : ℝ => ∑ r,-c r*b r*Real.sin (s*a r))
      (∑ r,(-c r*b r)*a r) 0 := HasDerivAt.fun_sum (u := Finset.univ)
        (fun r _ => sine_line_zero_hasDeriv (-c r*b r) (a r))
  rw [hs.deriv,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem phaseEnergy_mixed_derivative_ordered {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ)
    (hH : Indexed.IsSign H) (u v : Matrix (Fin n) (Fin n) ℝ) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => phaseEnergy H (s • u+t • v)) 0) 0=
      -(∑ i,∑ j,∑ a,∑ b,rectangleWeight H i j a b*
        rectangleAngle u i j a b*rectangleAngle v i j a b) := by
  let c := fun r : RectangleIndex n => rectangleWeight H r.1.1 r.1.2 r.2.1 r.2.2
  let a := fun r : RectangleIndex n => rectangleAngle u r.1.1 r.1.2 r.2.1 r.2.2
  let b := fun r : RectangleIndex n => rectangleAngle v r.1.1 r.1.2 r.2.1 r.2.2
  have hE (s t : ℝ) : phaseEnergy H (s • u+t • v)=
      (∑ r : RectangleIndex n,c r*Real.cos (s*a r+t*b r))-(n : ℝ)^3 := by
    simp only [phaseEnergy_eq_rectangles H hH,rectangleAngle_add,rectangleAngle_smul,
      c,a,b,Fintype.sum_prod_type]
  have hfun : (fun s : ℝ => deriv (fun t : ℝ => phaseEnergy H (s • u+t • v)) 0)=
      (fun s : ℝ => deriv (fun t : ℝ => (∑ r : RectangleIndex n,c r*Real.cos (s*a r+t*b r))-(n : ℝ)^3) 0) := by
    funext s
    congr 1
    funext t
    exact hE s t
  rw [hfun,finite_cosine_mixed_derivative]
  simp only [c,a,b,Fintype.sum_prod_type]

theorem phaseEnergy_mixed_derivative_upper {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ)
    (hH : Indexed.IsSign H) (u v : Matrix (Fin n) (Fin n) ℝ) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => phaseEnergy H (s • u+t • v)) 0) 0=
      -4*(∑ i,∑ j,∑ a,∑ b,if i<j ∧ a<b then rectangleWeight H i j a b*
        rectangleAngle u i j a b*rectangleAngle v i j a b else 0) := by
  rw [phaseEnergy_mixed_derivative_ordered H hH,rectangle_bilinear_sum_four_upper]
  ring

theorem rectangleAngle_single {n : ℕ} (i j a b : Fin n) (p : Fin n × Fin n) :
    rectangleAngle (Matrix.single p.1 p.2 (1 : ℝ)) i j a b=(rectangleVector i j a b p : ℝ) := by
  have h := rectangleVector_dot (Matrix.single p.1 p.2 (1 : ℝ)) i j a b
  have hs : (∑ q : Fin n × Fin n,(rectangleVector i j a b q : ℝ)*
      (Matrix.single p.1 p.2 (1 : ℝ)) q.1 q.2)=(rectangleVector i j a b p : ℝ) := by
    rw [Fintype.sum_prod_type]
    have hrow (x : Fin n) : (∑ y : Fin n,(rectangleVector i j a b (x,y) : ℝ)*
        (Matrix.single p.1 p.2 (1 : ℝ)) x y)=
        if x=p.1 then (rectangleVector i j a b p : ℝ) else 0 := by
      by_cases hx : x=p.1
      · subst x
        simp [Matrix.single_apply,mul_ite]
      · simp [Matrix.single_apply,mul_ite,Ne.symm hx,hx]
    simp_rw [hrow]
    simp
  exact h.symm.trans hs

theorem integerPhaseHessian_actual_mixed {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ)
    (hH : Indexed.IsSign H) (p q : Fin n × Fin n) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => phaseEnergy H
      (s • Matrix.single p.1 p.2 (1 : ℝ)+t • Matrix.single q.1 q.2 (1 : ℝ))) 0) 0=
      (integerPhaseHessian H p q : ℝ) := by
  have hc (i j a b : Fin n) :
      (((if i<j ∧ a<b then rectangleWeightInt H i j a b*rectangleVector i j a b p*
        rectangleVector i j a b q else 0) : ℤ) : ℝ)=
      if i<j ∧ a<b then rectangleWeight H i j a b*(rectangleVector i j a b p : ℝ)*
        (rectangleVector i j a b q : ℝ) else 0 := by
    split_ifs <;> simp only [Int.cast_mul,rectangleWeightInt_cast,Int.cast_zero]
  rw [phaseEnergy_mixed_derivative_upper H hH]
  simp only [rectangleAngle_single,integerPhaseHessian,Int.cast_mul,Int.cast_neg,
    Int.cast_ofNat,Int.cast_sum,hc]

theorem phaseMatrix_unit_modulus {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ)
    (hH : Indexed.IsSign H) (θ : Matrix (Fin n) (Fin n) ℝ) (i a : Fin n) :
    ‖phaseMatrix H θ i a‖=1 := by
  rcases hH i a with h | h <;>
    simp [phaseMatrix,phaseEntry,h,Complex.norm_exp_ofReal_mul_I]

theorem phaseEnergy_eq_entry_norm_sq {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ)
    (θ : Matrix (Fin n) (Fin n) ℝ) :
    phaseEnergy H θ=∑ i,∑ j,‖(phaseMatrix H θ*(phaseMatrix H θ).conjTranspose-
      (n : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) i j‖^2 := by
  simp only [phaseEnergy,phaseGram,Complex.normSq_eq_norm_sq,Matrix.sub_apply,
    Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,mul_ite,mul_one,mul_zero]

theorem phase_integer_hessian_rectangle_formula {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ)
    (hH : Indexed.IsSign H) :
    (∀ θ,phaseEnergy H θ=∑ i,∑ j,‖(phaseMatrix H θ*(phaseMatrix H θ).conjTranspose-
      (n : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) i j‖^2) ∧
    ContDiff ℝ (2 : ℕ) (phaseEnergy H) ∧
    ∃ L : Matrix (Fin n × Fin n) (Fin n × Fin n) ℤ,
      L.transpose=L ∧
      (∀ p q,L p q= -4*(∑ i,∑ j,∑ a,∑ b,if i<j ∧ a<b then
        rectangleWeightInt H i j a b*rectangleVector i j a b p*rectangleVector i j a b q else 0)) ∧
      ∀ p q,deriv (fun s : ℝ => deriv (fun t : ℝ => phaseEnergy H
        (s • Matrix.single p.1 p.2 (1 : ℝ)+t • Matrix.single q.1 q.2 (1 : ℝ))) 0) 0=(L p q : ℝ) := by
  refine ⟨phaseEnergy_eq_entry_norm_sq H,phaseEnergy_contDiff H hH 2,integerPhaseHessian H,integerPhaseHessian_symmetric H,?_,?_⟩
  · intro p q; rfl
  · exact integerPhaseHessian_actual_mixed H hH

end PhaseGeometry
