/- Copyright (c) 2026. All rights reserved. -/

module

public import EmcsfAcExtension.Infra.HardyIntegrated

/-!
# Hardy bounds for continuous curves of bounded variation

Cumulative variation is a nonnegative monotone majorant of every increment.
Its weighted average controls the norm deviation of the original curve.
This proves the BV Hardy estimate at `charged_SF_new_version.tex:L5771–L5771` directly,
without imposing absolute continuity or a derivative representation on the curve.
-/

public section

open Set MeasureTheory Filter

namespace EmcsfAcExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A monotone scalar majorant of increments also majorizes deviation from a
weighted radial average. -/
theorem norm_sub_radialAverage_le_monotone_deviation {w V : ℝ → ℝ} {f : ℝ → E}
    {a b : ℝ} (hab : a ≤ b) (hw : IntervalIntegrable w volume a b)
    (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x) (hf : ContinuousOn f (Icc a b))
    (hV : MonotoneOn V (Icc a b)) (hV0 : ∀ x ∈ Icc a b, 0 ≤ V x)
    (hinc : ∀ s ∈ Icc a b, ‖f b - f s‖ ≤ V b - V s)
    (hr : 0 < ∫ s in a..b, w s) :
    ‖f b - radialAverage w f a b‖ ≤ V b - radialAverage w V a b := by
  have hfu : ContinuousOn f (uIcc a b) := by rwa [uIcc_of_le hab]
  have hwf := hw.smul_continuousOn hfu
  have hwc : IntervalIntegrable (fun s => w s • f b) volume a b :=
    hw.smul_continuousOn continuousOn_const
  have hwV := intervalIntegrable_weight_mul_monotone hab hw hV hV0
  have hfc : ContinuousOn (fun s => f b - f s) (uIcc a b) := continuousOn_const.sub hfu
  have hi : IntervalIntegrable (fun s => w s • (f b - f s)) volume a b :=
    hw.smul_continuousOn hfc
  have heq : f b - radialAverage w f a b =
      (∫ s in a..b, w s)⁻¹ • ∫ s in a..b, w s • (f b - f s) := by
    simp_rw [smul_sub]
    rw [intervalIntegral.integral_sub hwc hwf,
      intervalIntegral.integral_smul_const, smul_sub, smul_smul,
      inv_mul_cancel₀ hr.ne', one_smul]
    rfl
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  calc
    _ ≤ (∫ s in a..b, w s)⁻¹ * ∫ s in a..b, ‖w s • (f b - f s)‖ :=
      mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm hab)
        (inv_nonneg.mpr hr.le)
    _ ≤ (∫ s in a..b, w s)⁻¹ * ∫ s in a..b, w s * (V b - V s) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hr.le)
      apply intervalIntegral.integral_mono_on hab hi.norm
        (((hw.mul_const (V b)).sub hwV).congr (fun s _ => by ring))
      intro s hs
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 s hs)]
      exact mul_le_mul_of_nonneg_left (hinc s hs) (hw0 s hs)
    _ = _ := by
      simp_rw [mul_sub]
      rw [intervalIntegral.integral_sub (hw.mul_const (V b)) hwV,
        intervalIntegral.integral_mul_const]
      dsimp only [radialAverage, smul_eq_mul]
      field_simp

/-- The continuous BV weighted deviation is integrable and has integral at most
the real total variation. The constant one is uniform in the weight and interval. -/
theorem integrable_and_integral_weighted_deviation_le_variation {w : ℝ → ℝ} {f : ℝ → E}
    {a b : ℝ} (hab : a ≤ b) (hw : IntervalIntegrable w volume a b)
    (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x) (hf : ContinuousOn f (Icc a b))
    (hBV : BoundedVariationOn f (Icc a b)) :
    IntervalIntegrable (fun x => w x / (∫ s in a..x, w s) *
      ‖f x - radialAverage w f a x‖) volume a b ∧
    (∫ x in a..b, w x / (∫ s in a..x, w s) *
      ‖f x - radialAverage w f a x‖) ≤ (eVariationOn f (Icc a b)).toReal := by
  let V := variationOnFromTo f (Icc a b) a
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hV : MonotoneOn V (Icc a b) := variationOnFromTo.monotoneOn hBV.locallyBoundedVariationOn ha
  have hVa : V a = 0 := variationOnFromTo.self f (Icc a b) a
  have hV0 : ∀ x ∈ Icc a b, 0 ≤ V x := by
    intro x hx
    rw [← hVa]
    exact hV ha hx hx.1
  have hVi := intervalIntegrable_weighted_deviation_monotone hab hw hw0 hV hV0
  have hdom : ∀ x ∈ Icc a b,
      w x / (∫ s in a..x, w s) * ‖f x - radialAverage w f a x‖ ≤
      w x / (∫ s in a..x, w s) * (V x - radialAverage w V a x) := by
    intro x hx
    have hr : 0 ≤ ∫ s in a..x, w s := intervalIntegral.integral_nonneg hx.1
      (fun t ht => hw0 t ⟨ht.1, ht.2.trans hx.2⟩)
    rcases eq_or_lt_of_le hr with hr | hr
    · simp only [← hr, div_zero, zero_mul, le_refl]
    · apply mul_le_mul_of_nonneg_left _ (div_nonneg (hw0 x hx) hr.le)
      exact norm_sub_radialAverage_le_monotone_deviation hx.1
        (hw.mono_set (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc hx)))
        (fun t ht => hw0 t ⟨ht.1, ht.2.trans hx.2⟩)
        (hf.mono (Icc_subset_Icc le_rfl hx.2)) (hV.mono (Icc_subset_Icc le_rfl hx.2))
        (fun t ht => hV0 t ⟨ht.1, ht.2.trans hx.2⟩)
        (fun s hs => variationOnFromTo.norm_sub_le_sub_of_le hBV ha
          ⟨hs.1, hs.2.trans hx.2⟩ hx hs.2) hr
  have hfu : ContinuousOn f (uIcc a b) := by rwa [uIcc_of_le hab]
  have hFi := hfu.intervalIntegrable (μ := volume)
  have hRi :=
    (hw.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).continuousOn
      |>.intervalIntegrable (μ := volume)
  have hNi := ((hw.smul_continuousOn hfu).absolutelyContinuousOnInterval_intervalIntegral_normed
    left_mem_uIcc).continuousOn.intervalIntegrable (μ := volume)
  have hk : IntervalIntegrable (fun x => w x / (∫ s in a..x, w s) *
      ‖f x - radialAverage w f a x‖) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab] at hVi hw hFi hRi hNi ⊢
    have hMeas : AEStronglyMeasurable (radialAverage w f a) (volume.restrict (Icc a b)) :=
      hRi.aestronglyMeasurable.inv₀.smul hNi.aestronglyMeasurable
    refine hVi.mono' ((hw.aestronglyMeasurable.div₀ hRi.aestronglyMeasurable).mul
      (hFi.aestronglyMeasurable.sub hMeas).norm) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hdom x hx
    · exact mul_nonneg (div_nonneg (hw0 x hx)
        (intervalIntegral.integral_nonneg hx.1 (fun t ht => hw0 t ⟨ht.1, ht.2.trans hx.2⟩)))
        (norm_nonneg _)
  refine ⟨hk, ?_⟩
  calc
    _ ≤ ∫ x in a..b, w x / (∫ s in a..x, w s) * (V x - radialAverage w V a x) :=
      intervalIntegral.integral_mono_on hab hk hVi hdom
    _ ≤ V b := integral_weighted_deviation_monotone_le hab hw hw0 hV hV0
    _ = _ := by
      dsimp only [V]
      rw [variationOnFromTo.eq_of_le _ _ hab, inter_self]

end EmcsfAcExtension
