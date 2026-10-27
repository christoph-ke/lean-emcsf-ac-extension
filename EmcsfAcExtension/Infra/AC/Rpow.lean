/- Copyright (c) 2026. All rights reserved. -/

module

public import EmcsfAcExtension.Infra.AC.Relabel
public import EmcsfAcExtension.Infra.AC.Quotient

/-!
# Positive powers of monotone absolutely continuous functions

Every positive real power is absolutely continuous on compact real intervals.
Pullback along a monotone AC radius preserves absolute continuity, even at zero.
-/

public section

open Set MeasureTheory

namespace AbsolutelyContinuousOnInterval

/-- A positive real power is absolutely continuous on every compact interval. -/
theorem rpow_fun {p a b : ℝ} (hp : 0 < p) :
    AbsolutelyContinuousOnInterval (fun x : ℝ => x ^ p) a b := by
  have hi : IntervalIntegrable (fun x : ℝ => p * x ^ (p - 1)) volume a b :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith only [hp])).const_mul p
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => a ^ p) a b :=
    (LipschitzWith.const (a ^ p)).lipschitzOnWith.absolutelyContinuousOnInterval
  apply (hconst.fun_add (hi.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)).congr
  intro x hx
  dsimp only
  rw [intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith only [hp]))]
  have hpow : p - 1 + 1 = p := sub_add_cancel p 1
  rw [hpow]
  field_simp
  ring

/-- Every positive real power of a monotone AC scalar function is AC,
including intervals meeting the zero set of the function. -/
theorem rpow_of_monotoneOn {f : ℝ → ℝ} {a b p : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hm : MonotoneOn f (uIcc a b))
    (hp : 0 < p) : AbsolutelyContinuousOnInterval (fun x => (f x) ^ p) a b :=
  (rpow_fun hp).comp_monotoneOn hf hm

end AbsolutelyContinuousOnInterval
