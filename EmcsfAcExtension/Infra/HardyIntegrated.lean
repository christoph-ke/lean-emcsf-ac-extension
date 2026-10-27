/- Copyright (c) 2026. All rights reserved. -/

module

public import EmcsfAcExtension.Infra.HardyMonotone

/-!
# Integrated Hardy estimates from monotone majorants

The derivative of a scalar weighted average gives its exact weighted deviation.
For a nonnegative monotone function, that derivative is integrable and its
integral is bounded by the terminal value. No lower radius bound is needed.
-/

public section

open Set MeasureTheory Filter

namespace EmcsfAcExtension

/-- Almost everywhere differentiation of a scalar radial average wherever the
radius is nonzero. Both the weight and its product with the function are L¹. -/
theorem ae_hasDerivAt_radialAverage {w F : ℝ → ℝ} {a b : ℝ}
    (hw : IntervalIntegrable w volume a b)
    (hWF : IntervalIntegrable (fun x => w x * F x) volume a b) :
    ∀ᵐ x, x ∈ uIcc a b → (∫ s in a..x, w s) ≠ 0 →
      HasDerivAt (radialAverage w F a)
        (w x / (∫ s in a..x, w s) * (F x - radialAverage w F a x)) x := by
  filter_upwards [hw.ae_hasDerivAt_integral, hWF.ae_hasDerivAt_integral]
    with x hx hFx hmem hne
  have hd := ((hx hmem a left_mem_uIcc).inv hne).mul (hFx hmem a left_mem_uIcc)
  convert hd using 1
  · rfl
  · dsimp only [radialAverage, smul_eq_mul, Pi.inv_apply]
    field_simp
    ring

/-- The weighted deviation of a nonnegative monotone function is nonnegative
and bounded almost everywhere by the derivative of its radial average. -/
theorem ae_weighted_deviation_le_deriv_radialAverage {w F : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hw : IntervalIntegrable w volume a b)
    (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x)
    (hF : MonotoneOn F (Icc a b)) (hF0 : ∀ x ∈ Icc a b, 0 ≤ F x) :
    ∀ᵐ x ∂volume.restrict (Icc a b),
      0 ≤ w x / (∫ s in a..x, w s) * (F x - radialAverage w F a x) ∧
      w x / (∫ s in a..x, w s) * (F x - radialAverage w F a x) ≤
        deriv (radialAverage w F a) x := by
  have hWF := intervalIntegrable_weight_mul_monotone hab hw hF hF0
  have hM := monotoneOn_radialAverage hab hw hw0 hF hF0
  have hne_a : ∀ᵐ x : ℝ, x ≠ a := by simp [ae_iff, measure_singleton]
  have hne_b : ∀ᵐ x : ℝ, x ≠ b := by simp [ae_iff, measure_singleton]
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [ae_hasDerivAt_radialAverage hw hWF, hne_a, hne_b] with x hd hxa hxb hx
  have hxu : x ∈ uIcc a b := Icc_subset_uIcc hx
  have hax := uIcc_subset_uIcc left_mem_uIcc hxu
  have hMx := radialAverage_le_of_monotoneOn hx.1 (hw.mono_set hax)
    (fun t ht => hw0 t ⟨ht.1, ht.2.trans hx.2⟩)
    (hF.mono (Icc_subset_Icc le_rfl hx.2))
    (fun t ht => hF0 t ⟨ht.1, ht.2.trans hx.2⟩)
  have hr : 0 ≤ ∫ s in a..x, w s := intervalIntegral.integral_nonneg hx.1
    (fun t ht => hw0 t ⟨ht.1, ht.2.trans hx.2⟩)
  refine ⟨mul_nonneg (div_nonneg (hw0 x hx) hr) (sub_nonneg.mpr hMx), ?_⟩
  by_cases hzero : (∫ s in a..x, w s) = 0
  · rw [hzero, div_zero, zero_mul]
    rw [← derivWithin_of_mem_nhds
      (Icc_mem_nhds (lt_of_le_of_ne hx.1 hxa.symm) (lt_of_le_of_ne hx.2 hxb))]
    exact hM.derivWithin_nonneg
  · exact (hd hxu hzero).deriv.ge

/-- The weighted deviation of a nonnegative monotone scalar function is
integrable up to the zero-radius endpoint. -/
theorem intervalIntegrable_weighted_deviation_monotone {w F : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hw : IntervalIntegrable w volume a b)
    (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x)
    (hF : MonotoneOn F (Icc a b)) (hF0 : ∀ x ∈ Icc a b, 0 ≤ F x) :
    IntervalIntegrable (fun x => w x / (∫ s in a..x, w s) *
      (F x - radialAverage w F a x)) volume a b := by
  have hM := monotoneOn_radialAverage hab hw hw0 hF hF0
  have hMu : MonotoneOn (radialAverage w F a) (uIcc a b) := by
    rwa [uIcc_of_le hab]
  have hWF := intervalIntegrable_weight_mul_monotone hab hw hF hF0
  have hFi : IntervalIntegrable F volume a b :=
    (by simpa only [uIcc_of_le hab] using hF : MonotoneOn F (uIcc a b)).intervalIntegrable
  have hRi :=
    (hw.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).continuousOn
      |>.intervalIntegrable (μ := volume)
  have hNi :=
    (hWF.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).continuousOn
      |>.intervalIntegrable (μ := volume)
  have hd := hMu.intervalIntegrable_deriv
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab] at hw hFi hRi hNi hd ⊢
  have hMMeas : AEStronglyMeasurable (radialAverage w F a) (volume.restrict (Icc a b)) :=
    hRi.aestronglyMeasurable.inv₀.mul hNi.aestronglyMeasurable
  refine hd.mono'
    ((hw.aestronglyMeasurable.div₀ hRi.aestronglyMeasurable).mul
      (hFi.aestronglyMeasurable.sub hMMeas)) ?_
  filter_upwards [ae_weighted_deviation_le_deriv_radialAverage hab
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hw) hw0 hF hF0] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
  exact hx.2

/-- The integrated weighted deviation of a nonnegative monotone scalar function
is bounded by its terminal value, with universal constant one. -/
theorem integral_weighted_deviation_monotone_le {w F : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hw : IntervalIntegrable w volume a b)
    (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x)
    (hF : MonotoneOn F (Icc a b)) (hF0 : ∀ x ∈ Icc a b, 0 ≤ F x) :
    (∫ x in a..b, w x / (∫ s in a..x, w s) *
      (F x - radialAverage w F a x)) ≤ F b := by
  have hM : MonotoneOn (radialAverage w F a) (uIcc a b) := by
    simpa only [uIcc_of_le hab] using monotoneOn_radialAverage hab hw hw0 hF hF0
  have hbound := intervalIntegral.integral_mono_ae_restrict hab
    (intervalIntegrable_weighted_deviation_monotone hab hw hw0 hF hF0)
    hM.intervalIntegrable_deriv
    ((ae_weighted_deviation_le_deriv_radialAverage hab hw hw0 hF hF0).mono fun _ hx => hx.2)
  have hderiv := hM.intervalIntegral_deriv_mem_uIcc
  have hn : 0 ≤ radialAverage w F a b := radialAverage_nonneg hab hw0 hF0
  rw [radialAverage_self, sub_zero, uIcc_of_le hn] at hderiv
  exact hbound.trans (hderiv.2.trans (radialAverage_le_of_monotoneOn hab hw hw0 hF hF0))

end EmcsfAcExtension
