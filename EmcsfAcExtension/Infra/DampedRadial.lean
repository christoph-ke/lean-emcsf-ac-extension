/- Copyright (c) 2026. All rights reserved. -/

module

public import EmcsfAcExtension.Infra.Hardy
public import EmcsfAcExtension.Infra.Gronwall

/-!
# Damped radial differential inequalities

The damping coefficient `p * w / ρ` can fail to be integrable at the axis.
Nonnegativity and the differential inequality nevertheless imply integrability
of its product with the solution. The forcing itself is required to be L¹;
for a forcing written `w * g`, this means integrability of the product.
The constant in the moment estimate is exactly `1 / p`, uniformly in the data.
-/

public section

open Set MeasureTheory Filter

namespace EmcsfAcExtension

/-- A nonnegative AC radial subsolution has an integrable damped moment. This
endpoint balance permits signed forcing and does not require `p ≤ 1`. -/
theorem integrable_and_integral_damped_radial_le {w y q : ℝ → ℝ} {a b p : ℝ}
    (hab : a ≤ b) (hp : 0 < p) (hw : IntervalIntegrable w volume a b)
    (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x) (hy : AbsolutelyContinuousOnInterval y a b)
    (hy0 : ∀ x ∈ Icc a b, 0 ≤ y x) (hq : IntervalIntegrable q volume a b)
    (hineq : ∀ᵐ x ∂volume.restrict (Icc a b),
      deriv y x + p * (w x / (∫ s in a..x, w s) * y x) ≤ q x) :
    IntervalIntegrable (fun x => w x / (∫ s in a..x, w s) * y x) volume a b ∧
    (∫ x in a..b, w x / (∫ s in a..x, w s) * y x) ≤
      p⁻¹ * ((∫ x in a..b, q x) + y a - y b) := by
  have hnonneg : ∀ x ∈ Icc a b, 0 ≤ w x / (∫ s in a..x, w s) * y x := by
    intro x hx
    exact mul_nonneg (div_nonneg (hw0 x hx)
      (intervalIntegral.integral_nonneg hx.1 (fun t ht => hw0 t ⟨ht.1, ht.2.trans hx.2⟩)))
      (hy0 x hx)
  have hdy := hy.intervalIntegrable_deriv
  have hRi :=
    (hw.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).continuousOn
      |>.intervalIntegrable (μ := volume)
  have hyi := hy.continuousOn.intervalIntegrable (μ := volume)
  have hk : IntervalIntegrable (fun x => w x / (∫ s in a..x, w s) * y x) volume a b := by
    have hB := (hq.sub hdy).const_mul p⁻¹
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab] at hw hRi hyi hB ⊢
    refine hB.mono' ((hw.aestronglyMeasurable.div₀ hRi.aestronglyMeasurable).mul
      hyi.aestronglyMeasurable) ?_
    filter_upwards [hineq, ae_restrict_mem measurableSet_Icc] with x hx hmem
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg x hmem)]
    rw [← div_eq_inv_mul]
    apply (le_div_iff₀ hp).2
    rw [mul_comm]
    exact (le_sub_iff_add_le').2 hx
  refine ⟨hk, ?_⟩
  have hi := intervalIntegral.integral_mono_ae_restrict hab
    (hdy.add (hk.const_mul p)) hq hineq
  rw [intervalIntegral.integral_add hdy (hk.const_mul p),
    intervalIntegral.integral_const_mul, hy.integral_deriv_eq_sub] at hi
  rw [← div_eq_inv_mul, le_div_iff₀ hp, mul_comm]
  linarith only [hi]

/-- The axis-to-endpoint damped radial moment estimate, with constant `1 / p`.
Integrability at the axis is a conclusion. -/
theorem integral_damped_radial_le {w y q : ℝ → ℝ} {a b p : ℝ}
    (hab : a ≤ b) (hp : 0 < p) (hw : IntervalIntegrable w volume a b)
    (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x) (hy : AbsolutelyContinuousOnInterval y a b)
    (hy0 : ∀ x ∈ Icc a b, 0 ≤ y x) (hya : y a = 0)
    (hq : IntervalIntegrable q volume a b)
    (hineq : ∀ᵐ x ∂volume.restrict (Icc a b),
      deriv y x + p * (w x / (∫ s in a..x, w s) * y x) ≤ q x) :
    (∫ x in a..b, w x / (∫ s in a..x, w s) * y x) ≤ p⁻¹ * ∫ x in a..b, q x := by
  have hi := (integrable_and_integral_damped_radial_le hab hp hw hw0 hy hy0 hq hineq).2
  rw [hya, add_zero] at hi
  exact hi.trans (mul_le_mul_of_nonneg_left (sub_le_self _ (hy0 b (right_mem_Icc.mpr hab)))
    (inv_nonneg.mpr hp.le))

end EmcsfAcExtension
