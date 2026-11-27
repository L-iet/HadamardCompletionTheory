/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import HadamardMultibase.LogarithmSeparation
public import HadamardMultibase.Results
public import Mathlib.Analysis.Asymptotics.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Tactic
@[expose] public section
set_option autoImplicit false
namespace CompletionTheory
open HadamardMultibase

theorem unconditional_uniform_multiplier_buffer :
    ∃ T : ℕ → ℕ, (∀ n, 2≤T n) ∧
      Asymptotics.IsBigO Filter.atTop (fun n : ℕ => (T n : ℝ)) (fun n : ℕ => logScale n) ∧
      (∀ n q : ℕ, Odd q → q≤n → HadamardOrder (2^(T n)*q)) ∧
      (∀ n k : ℕ, 1≤k → k≤n → HadamardOrder (2^(T n)*k)) := by
  classical
  have hSparse : SparseRepresentationBound := sparseRepresentationBound_of_not_liouville
    (not_liouville_log_ratio (by norm_num : 2≤(2:ℕ)) (by norm_num : 2≤(10:ℕ)) irrational_log_ten_div_log_two)
  obtain ⟨C,hC,N,hUniform⟩ := uniform_exponent_bound_of_inputs golayFamily craigenTransfer hSparse
  let chooseT (n : ℕ) := Classical.choose (hUniform (max N n) (le_max_left N n))
  have hChoose (n : ℕ) : (chooseT n : ℝ)≤C*logScale (max N n) ∧
      ∀ q : ℕ, Odd q → q≤max N n → HadamardOrder (2^(chooseT n)*q) :=
    Classical.choose_spec (hUniform (max N n) (le_max_left N n))
  let T (n : ℕ) := 2+chooseT n
  have hOdd (n q : ℕ) (hq : Odd q) (hqn : q≤n) : HadamardOrder (2^(T n)*q) := by
    have ho := (hChoose n).2 q hq (hqn.trans (le_max_right N n))
    simpa only [T,pow_add,mul_assoc] using ho.two_pow_mul 2
  refine ⟨T,fun n => by dsimp [T]; omega,?_,hOdd,?_⟩
  · apply Asymptotics.IsBigO.of_bound (C+2)
    filter_upwards [Filter.eventually_ge_atTop N,eventually_logScale_threshold] with n hn hLog
    have hOne : 1≤logScale n := one_le_logScaleReal hLog
    have hb := (hChoose n).1
    rw [max_eq_right hn] at hb
    have hT : (T n : ℝ)≤(C+2)*logScale n := by
      dsimp [T]
      push_cast
      nlinarith
    simpa only [Real.norm_eq_abs,abs_of_nonneg (show (0:ℝ)≤T n by positivity),
      abs_of_nonneg (by linarith : 0≤logScale n)] using hT
  · intro n k hk hkn
    obtain ⟨v,q,hq,hEq⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : k≠0)
    have hp : 0<(2:ℕ)^v := by positivity
    have hqk : q≤k := by rw [hEq]; nlinarith
    have ho := hOdd n q hq (hqk.trans hkn)
    have h := ho.two_pow_mul v
    simpa only [hEq,mul_assoc,mul_left_comm] using h


theorem bigo_logscale_buffer_is_subpower (T : ℕ → ℕ)
    (hO : Asymptotics.IsBigO Filter.atTop (fun n : ℕ => (T n : ℝ)) (fun n : ℕ => logScale n))
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in Filter.atTop, (2:ℝ)^(T n)≤(n:ℝ)^ε := by
  obtain ⟨C,hC,hBound⟩ := hO.exists_pos
  have hLog2 : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  let D := C*Real.log (2:ℝ)
  have hD : 0<D := mul_pos hC hLog2
  have hSmall : ∀ᶠ n : ℕ in Filter.atTop, logScale n/Real.log n<ε/D :=
    tendsto_logScale_div_log.eventually (gt_mem_nhds (div_pos hε hD))
  filter_upwards [hBound.bound,eventually_logScale_threshold,Filter.eventually_ge_atTop 2,hSmall] with n hb hLog hn hs
  have hnPos : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hnOne : (1:ℝ)<n := by exact_mod_cast (by omega : 1<n)
  have hLogPos : 0<Real.log (n:ℝ) := Real.log_pos hnOne
  have hScalePos : 0≤logScale n := le_trans (by norm_num) (one_le_logScaleReal hLog)
  simp only [Real.norm_eq_abs,abs_of_nonneg (show (0:ℝ)≤T n by positivity),abs_of_nonneg hScalePos] at hb
  have hs' := (div_lt_iff₀ hLogPos).mp hs
  have hExp : (T n : ℝ)*Real.log (2:ℝ)≤ε*Real.log n := by
    calc
      _≤(C*logScale n)*Real.log (2:ℝ) := mul_le_mul_of_nonneg_right hb hLog2.le
      _=D*logScale n := by dsimp [D]; ring
      _≤D*(ε/D*Real.log n) := mul_le_mul_of_nonneg_left hs'.le hD.le
      _=ε*Real.log n := by field_simp
  rw [← Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : 0<(2:ℝ)),Real.rpow_def_of_pos hnPos]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem unconditional_uniform_power_buffer :
    ∃ T : ℕ → ℕ, (∀ n, 2≤T n) ∧
      Asymptotics.IsBigO Filter.atTop (fun n : ℕ => (T n : ℝ)) (fun n : ℕ => logScale n) ∧
      (∀ n q : ℕ, Odd q → q≤n → ∀ h : HasExponent q, tau q h≤T n) ∧
      (∀ n k : ℕ, 1≤k → k≤n → HadamardOrder (2^(T n)*k)) ∧
      (∀ ε : ℝ, 0<ε → ∀ᶠ n : ℕ in Filter.atTop, (2:ℝ)^(T n)≤(n:ℝ)^ε) := by
  obtain ⟨T,hTwo,hO,hOdd,hAll⟩ := unconditional_uniform_multiplier_buffer
  refine ⟨T,hTwo,hO,?_,hAll,bigo_logscale_buffer_is_subpower T hO⟩
  intro n q hq hqn h
  exact tau_le h (hOdd n q hq hqn)

end CompletionTheory
