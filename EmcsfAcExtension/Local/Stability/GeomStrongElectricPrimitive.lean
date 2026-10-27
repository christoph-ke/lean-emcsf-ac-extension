module

public import EmcsfAcExtension.Local.Defs.Setting

/-! # Cubic cancellation for electric curvature primitives

A quadratic inner vanishing cancels the cubic outer kernel exactly.
Absolute integrability is proved from the positive polynomial majorant
before any complex primitive is subtracted.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

/-- A measurable complex forcing with a quadratic polynomial majorant
is integrable on the full closed interval. The coefficient `D` is an
explicit input, uniform in the function and endpoints.
-/
theorem stab_quadratic_majorant_integrable {a b D : ℝ} {f : ℝ → ℂ}
    (hab : a ≤ b) (hf : AEStronglyMeasurable f (volume.restrict (Icc a b)))
    (hbound : ∀ t ∈ Icc a b, ‖f t‖ ≤ D * (t - a) ^ 2) :
    Integrable f (volume.restrict (Icc a b)) := by
  have hi : Integrable (fun t : ℝ => D * (t - a) ^ 2) (volume.restrict (Icc a b)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).1
      ((by fun_prop : Continuous (fun t : ℝ => D * (t - a) ^ 2)).intervalIntegrable a b)
  apply hi.mono' hf
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hbound t ht

/-- A quadratic primitive with outer cubic coefficient has exact norm
cost `C D/3`. The factor `1/3` is universal, independent of endpoints,
functions, scales and any minimum radius.
-/
theorem stab_electric_primitive_norm_of_quadratic_bound
    {a b C D : ℝ} {c : ℂ} {f : ℝ → ℂ} (hab : a < b) (hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hf : AEStronglyMeasurable f (volume.restrict (Icc a b)))
    (hbound : ∀ t ∈ Icc a b, ‖f t‖ ≤ D * (t - a) ^ 2)
    (hc : ‖c‖ ≤ C / (b - a) ^ 3) :
    ‖c * ∫ t in a..b, f t‖ ≤ C * D / 3 := by
  have hL : 0 < b - a := sub_pos.mpr hab
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).2
    (stab_quadratic_majorant_integrable hab.le hf hbound)
  have hpoly : IntervalIntegrable (fun t : ℝ => D * (t - a) ^ 2) volume a b :=
    (by fun_prop : Continuous (fun t : ℝ => D * (t - a) ^ 2)).intervalIntegrable a b
  have hprimitive : (∫ t in a..b, (t - a) ^ 2) = (b - a) ^ 3 / 3 := by
    have hd t : HasDerivAt (fun t : ℝ => (t - a) ^ 3 / 3) ((t - a) ^ 2) t := by
      convert (((hasDerivAt_id t).sub_const a).pow 3).div_const 3 using 1 <;> norm_num
    have hp := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le
      (by fun_prop : ContinuousOn (fun t : ℝ => (t - a) ^ 3 / 3) (Icc a b))
      (fun t ht => hd t)
      ((by fun_prop : Continuous (fun t : ℝ => (t - a) ^ 2)).intervalIntegrable a b)
    simpa only [sub_self, zero_pow (by decide : 3 ≠ 0), zero_div, sub_zero] using hp
  have hn := (intervalIntegral.norm_integral_le_integral_norm
    (μ := volume) (f := f) hab.le).trans
    (intervalIntegral.integral_mono_on hab.le hi.norm hpoly hbound)
  rw [intervalIntegral.integral_const_mul, hprimitive] at hn
  rw [norm_mul]
  apply (mul_le_mul hc hn (norm_nonneg _) (div_nonneg hC (pow_nonneg hL.le 3))).trans_eq
  field_simp

/-- Electric primitive subtraction has the two exact costs
`(C Dδ + Cδ D)/3`. The four coefficients are explicit and universal
in their role, before any field or scale parameters.
-/
theorem stab_electric_primitive_difference_of_quadratic_bounds
    {a b C Cδ D Dδ : ℝ} {c₁ c₂ : ℂ} {f₁ f₂ : ℝ → ℂ}
    (hab : a < b) (hC : 0 ≤ C) (hCδ : 0 ≤ Cδ) (hD : 0 ≤ D) (hDδ : 0 ≤ Dδ)
    (hf₁ : IntervalIntegrable f₁ volume a b) (hf₂ : IntervalIntegrable f₂ volume a b)
    (hbound₂ : ∀ t ∈ Icc a b, ‖f₂ t‖ ≤ D * (t - a) ^ 2)
    (hboundδ : ∀ t ∈ Icc a b, ‖f₁ t - f₂ t‖ ≤ Dδ * (t - a) ^ 2)
    (hc₁ : ‖c₁‖ ≤ C / (b - a) ^ 3) (hcδ : ‖c₁ - c₂‖ ≤ Cδ / (b - a) ^ 3) :
    ‖c₁ * (∫ t in a..b, f₁ t) - c₂ * (∫ t in a..b, f₂ t)‖ ≤
      (C * Dδ + Cδ * D) / 3 := by
  have hδ := stab_electric_primitive_norm_of_quadratic_bound hab hC hDδ
    (((intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).1 hf₁).sub
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).1 hf₂)).aestronglyMeasurable
    hboundδ hc₁
  have h₂ := stab_electric_primitive_norm_of_quadratic_bound hab hCδ hD
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).1 hf₂).aestronglyMeasurable
    hbound₂ hcδ
  have heq : c₁ * (∫ t in a..b, f₁ t) - c₂ * (∫ t in a..b, f₂ t) =
      c₁ * (∫ t in a..b, f₁ t - f₂ t) + (c₁ - c₂) * (∫ t in a..b, f₂ t) := by
    rw [intervalIntegral.integral_sub hf₁ hf₂]
    ring
  rw [heq]
  exact (norm_add_le _ _).trans ((add_le_add hδ h₂).trans_eq (by ring))

end EmcsfAcExtension.Local
