/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
@[expose] public section
namespace CompletionTheory.ThreeSquares
open MeasureTheory Metric Module

 theorem ball_sqrt_two_volume_dim_three {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hd : finrank ℝ E=3) :
    (2:ENNReal)^finrank ℝ E<volume (Metric.ball (0:E) (Real.sqrt 2)) := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hs1 : (1:ℝ)<Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
  have hc : (Real.sqrt 2)^3=2*Real.sqrt 2 := by rw [pow_succ,hs]
  have hp : (3:ℝ)<Real.pi*Real.sqrt 2 := by
    nlinarith [Real.pi_gt_three,mul_pos (sub_pos.mpr Real.pi_gt_three) (show 0<Real.sqrt (2:ℝ) by linarith)]
  have hr : (8:ℝ)<(Real.sqrt 2)^3*(Real.pi*4/3) := by rw [hc];nlinarith
  calc
    _=(8:ENNReal) := by rw [hd];norm_num
    _<ENNReal.ofReal ((Real.sqrt 2)^3*(Real.pi*4/3)) := by
      simpa using (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num : (0:ℝ)≤8)).mpr hr
    _=volume (Metric.ball (0:E) (Real.sqrt 2)) := by
      rw [InnerProductSpace.volume_ball_of_dim_odd (k:=1) (by omega : finrank ℝ E=2*1+1),hd]
      rw [ENNReal.ofReal_mul (by positivity : (0:ℝ)≤(Real.sqrt 2)^3),
        ENNReal.ofReal_pow (Real.sqrt_nonneg (2:ℝ))]
      norm_num [Nat.doubleFactorial]

 theorem ball_sqrt_two_volume_dim_two {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hd : finrank ℝ E=2) :
    (2:ENNReal)^finrank ℝ E<volume (Metric.ball (0:E) (Real.sqrt 2)) := by
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos (R:=ℝ) (by rw [hd];norm_num)
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hr : (4:ℝ)<(Real.sqrt 2)^2*Real.pi := by rw [hs];nlinarith [Real.pi_gt_three]
  calc
    _=(4:ENNReal) := by rw [hd];norm_num
    _<ENNReal.ofReal ((Real.sqrt 2)^2*Real.pi) := by
      simpa using (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num : (0:ℝ)≤4)).mpr hr
    _=volume (Metric.ball (0:E) (Real.sqrt 2)) := by
      rw [InnerProductSpace.volume_ball_of_dim_even (k:=1) (by omega : finrank ℝ E=2*1),hd]
      rw [ENNReal.ofReal_mul (by positivity : (0:ℝ)≤(Real.sqrt 2)^2),
        ENNReal.ofReal_pow (Real.sqrt_nonneg (2:ℝ))]
      norm_num

end CompletionTheory.ThreeSquares
