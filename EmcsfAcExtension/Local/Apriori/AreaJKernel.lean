module

public import EmcsfAcExtension.Infra.Triangle
import EmcsfAcExtension.Infra.RadialKernel

/-! # Ordered integration for the outgoing scalar area estimate

The inverse-cube coordinate kernel is integrated before taking a sectional
bound. This preserves the opposite-direction Hardy integral in
`charged_SF_new_version.tex:L4699–L4717`.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local.Area

private theorem coordinate_kernel_le {u a T : ℝ} (hua : u < a) (haT : a ≤ T) :
    (∫⁻ v in Icc a T, ENNReal.ofReal (1 / (v - u) ^ 3)) ≤
      ENNReal.ofReal (1 / (2 * (a - u) ^ 2)) := by
  have hc : ContinuousOn (fun v : ℝ => v - u) (uIcc a T) :=
    continuousOn_id.sub continuousOn_const
  have hq : ContinuousOn (fun v : ℝ => 1 / (v - u) ^ 3) (uIcc a T) := by
    apply continuousOn_const.div (hc.pow 3)
    intro v hv
    rw [uIcc_of_le haT] at hv
    exact pow_ne_zero _ (sub_pos.mpr (hua.trans_le hv.1)).ne'
  have hi := hq.intervalIntegrable (μ := volume)
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Icc_of_le haT).mp hi)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
      exact div_nonneg zero_le_one (pow_nonneg (sub_nonneg.mpr (hua.le.trans hv.1)) _)),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le haT]
  apply ENNReal.ofReal_le_ofReal
  apply integral_radial_inv_cube_le haT
    (show ContDiffOn ℝ 1 (fun v : ℝ => v - u) (uIcc a T) from
      contDiffOn_id.sub contDiffOn_const).absolutelyContinuousOnInterval
    (sub_pos.mpr hua)
    (fun x _ y _ hxy => sub_le_sub_right hxy u)
  filter_upwards with v
  exact (hasDerivAt_id v |>.sub_const u).deriv

/-- The three-variable inverse-cube area kernel leaves an inverse-square
weight on the primitive variable. The universal coefficient is exactly `1/2`,
uniformly in the interval and measurable nonnegative input; infinite masses
are allowed. This is Tonelli in the source's required order.
-/
theorem outgoing_primitive_area_le {a₀ T : ℝ} {F : ℝ × ℝ → ℝ≥0∞}
    (hF : Measurable F) :
    (∫⁻ u in Icc a₀ T, ∫⁻ v in Icc u T,
      ENNReal.ofReal (1 / (v - u) ^ 3) * ∫⁻ a in Icc u v, F (u, a)) ≤
      ∫⁻ a in Icc a₀ T, ∫⁻ u in Icc a₀ a,
        ENNReal.ofReal (1 / (2 * (a - u) ^ 2)) * F (u, a) := by
  have hb (u : ℝ) :
      (∫⁻ v in Icc u T,
        ENNReal.ofReal (1 / (v - u) ^ 3) * ∫⁻ a in Icc u v, F (u, a)) ≤
      ∫⁻ a in Icc u T, ENNReal.ofReal (1 / (2 * (a - u) ^ 2)) * F (u, a) := by
    have heq :
        (∫⁻ v in Icc u T,
          ENNReal.ofReal (1 / (v - u) ^ 3) * ∫⁻ a in Icc u v, F (u, a)) =
        ∫⁻ a in Icc u T, ∫⁻ v in Icc a T,
          ENNReal.ofReal (1 / (v - u) ^ 3) * F (u, a) := by
      rw [lintegral_lintegral_swap_triangle
        (F := fun q : ℝ × ℝ => ENNReal.ofReal (1 / (q.2 - u) ^ 3) * F (u, q.1))
        (by fun_prop)]
      apply lintegral_congr
      intro v
      exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    rw [heq]
    have hne : ∀ᵐ a : ℝ, a ≠ u := by simp [ae_iff, measure_singleton]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with a ha hne
    rw [lintegral_mul_const'' _ (by fun_prop :
      AEMeasurable (fun v : ℝ => ENNReal.ofReal (1 / (v - u) ^ 3)) _)]
    exact mul_le_mul' (coordinate_kernel_le (lt_of_le_of_ne ha.1 hne.symm) ha.2) le_rfl
  calc
    _ ≤ ∫⁻ u in Icc a₀ T, ∫⁻ a in Icc u T,
        ENNReal.ofReal (1 / (2 * (a - u) ^ 2)) * F (u, a) :=
      lintegral_mono hb
    _ = _ := lintegral_lintegral_swap_triangle
      (F := fun p : ℝ × ℝ => ENNReal.ofReal (1 / (2 * (p.2 - p.1) ^ 2)) * F p)
      (by fun_prop)

end EmcsfAcExtension.Local.Area
