/- Copyright (c) 2026. All rights reserved. -/

module

public import EmcsfAcExtension.Infra.DampedRadialKernel

/-!
# Extended nonnegative radial bounds

These forms require only measurability of the nonnegative forcing. Thus they
apply to `q = w * g` when `w` and `g` are separately integrable, even if their
product is not. The finite real-integral forms are supplied by the other modules.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension

/-- Pointwise damped comparison with an extended nonnegative kernel integral.
The forcing need only be measurable and nonnegative. -/
theorem ofReal_le_lintegral_damped_radial_kernel {w y q : ℝ → ℝ} {a b p : ℝ}
    (hab : a ≤ b) (hp : 0 < p) (hw : IntervalIntegrable w volume a b)
    (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x) (hy : AbsolutelyContinuousOnInterval y a b)
    (hya : y a = 0) (hrb : 0 < ∫ s in a..b, w s)
    (hq : AEStronglyMeasurable q (volume.restrict (Ioc a b)))
    (hq0 : ∀ x ∈ Icc a b, 0 ≤ q x)
    (hineq : ∀ᵐ x ∂volume.restrict (Icc a b),
      deriv y x + p * (w x / (∫ s in a..x, w s) * y x) ≤ q x) :
    ENNReal.ofReal (y b) ≤ ∫⁻ x in Ioc a b,
      ENNReal.ofReal (((∫ s in a..x, w s) / (∫ s in a..b, w s)) ^ p * q x) := by
  let R := fun x => ∫ s in a..x, w s
  let k := fun x => (R x / R b) ^ p * q x
  have hR := hw.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hR0 : ∀ x ∈ Icc a b, 0 ≤ R x := by
    intro x hx
    exact intervalIntegral.integral_nonneg hx.1
      (fun s hs => hw0 s ⟨hs.1, hs.2.trans hx.2⟩)
  have hc : ContinuousOn (fun x => (R x / R b) ^ p) (uIcc a b) :=
    (Real.continuous_rpow_const hp.le).comp_continuousOn
      (by simpa only [div_eq_mul_inv, Pi.mul_def] using!
        hR.continuousOn.mul continuousOn_const)
  have hkmeas : AEStronglyMeasurable k (volume.restrict (Ioc a b)) :=
    (hc.intervalIntegrable (μ := volume)).aestronglyMeasurable.mul hq
  have hk0 : 0 ≤ᵐ[volume.restrict (Ioc a b)] k := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact mul_nonneg (Real.rpow_nonneg (div_nonneg (hR0 x ⟨hx.1.le, hx.2⟩) hrb.le) p)
      (hq0 x ⟨hx.1.le, hx.2⟩)
  by_cases hki : Integrable k (volume.restrict (Ioc a b))
  · have hki' := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hki
    have hQ : IntervalIntegrable (fun x => (R x) ^ p * q x) volume a b := by
      apply (hki'.const_mul ((R b) ^ p)).congr
      intro x hx
      have hx' : x ∈ Icc a b := by
        simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hx
      dsimp only [k, R]
      rw [Real.div_rpow (hR0 x hx') hrb.le]
      have hb : (∫ s in a..b, w s) ^ p ≠ 0 := (Real.rpow_pos_of_pos hrb p).ne'
      field_simp
      dsimp only [R]
      ring
    have hi := le_damped_radial_kernel_of_integrable_moment hab hp hw hw0 hy hya hrb hQ hineq
    have heq := ofReal_integral_eq_lintegral_ofReal hki hk0
    rw [← heq]
    apply ENNReal.ofReal_le_ofReal
    simpa only [k, R, intervalIntegral.integral_of_le hab] using hi
  · have htop : (∫⁻ x in Ioc a b, ENNReal.ofReal (k x)) = ⊤ := by
      by_contra hne
      exact hki ((lintegral_ofReal_ne_top_iff_integrable hkmeas hk0).1 hne)
    rw [show (∫⁻ x in Ioc a b,
      ENNReal.ofReal ((R x / R b) ^ p * q x)) = ⊤ from htop]
    exact le_top

/-- The damped moment estimate with extended nonnegative integrals requires
no integrability of the forcing, and retains the exact constant `1 / p`. -/
theorem lintegral_damped_radial_le {w y q : ℝ → ℝ} {a b p : ℝ}
    (hab : a ≤ b) (hp : 0 < p) (hw : IntervalIntegrable w volume a b)
    (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x) (hy : AbsolutelyContinuousOnInterval y a b)
    (hy0 : ∀ x ∈ Icc a b, 0 ≤ y x) (hya : y a = 0)
    (hq : AEStronglyMeasurable q (volume.restrict (Ioc a b)))
    (hq0 : ∀ x ∈ Icc a b, 0 ≤ q x)
    (hineq : ∀ᵐ x ∂volume.restrict (Icc a b),
      deriv y x + p * (w x / (∫ s in a..x, w s) * y x) ≤ q x) :
    (∫⁻ x in Ioc a b, ENNReal.ofReal (w x / (∫ s in a..x, w s) * y x)) ≤
      ENNReal.ofReal p⁻¹ * ∫⁻ x in Ioc a b, ENNReal.ofReal (q x) := by
  have hq0' : 0 ≤ᵐ[volume.restrict (Ioc a b)] q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hq0 x ⟨hx.1.le, hx.2⟩
  by_cases hqi : Integrable q (volume.restrict (Ioc a b))
  · have hqi' := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hqi
    have hk := (integrable_and_integral_damped_radial_le hab hp hw hw0 hy hy0 hqi' hineq).1
    have hki := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hk
    have hk0 : 0 ≤ᵐ[volume.restrict (Ioc a b)]
        (fun x => w x / (∫ s in a..x, w s) * y x) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hx' : x ∈ Icc a b := ⟨hx.1.le, hx.2⟩
      exact mul_nonneg (div_nonneg (hw0 x hx')
        (intervalIntegral.integral_nonneg hx.1.le
          (fun s hs => hw0 s ⟨hs.1, hs.2.trans hx.2⟩))) (hy0 x hx')
    rw [← ofReal_integral_eq_lintegral_ofReal hki hk0,
      ← ofReal_integral_eq_lintegral_ofReal hqi hq0', ← ENNReal.ofReal_mul (inv_nonneg.mpr hp.le)]
    apply ENNReal.ofReal_le_ofReal
    simpa only [intervalIntegral.integral_of_le hab] using
      integral_damped_radial_le hab hp hw hw0 hy hy0 hya hqi' hineq
  · have htop : (∫⁻ x in Ioc a b, ENNReal.ofReal (q x)) = ⊤ := by
      by_contra hne
      exact hqi ((lintegral_ofReal_ne_top_iff_integrable hq hq0').1 hne)
    rw [htop, ENNReal.mul_top (by simpa only [ne_eq, ENNReal.ofReal_eq_zero] using
      (not_le.mpr (inv_pos.mpr hp)))]
    exact le_top

end EmcsfAcExtension
