module

public import EmcsfAcExtension.Local.Stability.DifferenceMomentsAlgebra
public import EmcsfAcExtension.Infra.DampedRadialExtended

/-! # Damped comparison for radial differences

The real cubic monotonicity estimate supplies the difference exponent
`p ≤ 1 - 3ε²`. A real connection cancels in the norm equation. The
nonnegative forcing integrals are allowed to be infinite; no integrability
premise is inserted into the later field estimates.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem ae_norm_radial_difference_le
    {f g q : ℝ → ℂ} {w α : ℝ → ℝ} {a b ε p : ℝ}
    (hp : p ≤ 1 - 3 * ε ^ 2)
    (_hw : IntervalIntegrable w volume a b)
    (hw0 : ∀ t ∈ Icc a b, 0 ≤ w t)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hfε : ∀ t ∈ Ioo a b, ‖f t‖ ≤ ε)
    (hgε : ∀ t ∈ Ioo a b, ‖g t‖ ≤ ε)
    (hidentity : ∀ t ∈ Ioo a b,
      HasDerivWithinAt (fun s => f s - g s)
        (q t - (w t / ∫ s in a..t, w s) •
          ((f t - ‖f t‖ ^ 2 • f t) - (g t - ‖g t‖ ^ 2 • g t)) -
          α t • (Complex.I * (f t - g t))) (Icc a b) t) :
    ∀ᵐ t ∂volume.restrict (Icc a b),
      deriv (fun s => ‖f s - g s‖) t +
        p * (w t / (∫ s in a..t, w s) * ‖f t - g t‖) ≤ ‖q t‖ := by
  have hy : AbsolutelyContinuousOnInterval (fun t => ‖f t - g t‖) a b :=
    lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval (hf.sub hg)
  have hna : ∀ᵐ t : ℝ, t ≠ a := by simp [ae_iff, measure_singleton]
  have hnb : ∀ᵐ t : ℝ, t ≠ b := by simp [ae_iff, measure_singleton]
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hy.ae_differentiableAt, hna, hnb] with t hyt hta htb ht
  have ht' : t ∈ Ioo a b :=
    ⟨lt_of_le_of_ne ht.1 hta.symm, lt_of_le_of_ne ht.2 htb⟩
  have hrad : 0 ≤ w t / ∫ s in a..t, w s := div_nonneg (hw0 t ht)
    (intervalIntegral.integral_nonneg ht.1 (fun s hs => hw0 s ⟨hs.1, hs.2.trans ht.2⟩))
  have hn := stab_norm_deriv_radial_difference_le hrad (hfε t ht') (hgε t ht')
    ((hidentity t ht').hasDerivAt (Icc_mem_nhds ht'.1 ht'.2))
    (hyt (Icc_subset_uIcc ht))
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp hrad) (norm_nonneg (f t - g t))
  calc
    _ = deriv (fun s => ‖f s - g s‖) t +
        (w t / (∫ s in a..t, w s) * p) * ‖f t - g t‖ := by ring
    _ ≤ deriv (fun s => ‖f s - g s‖) t +
        (w t / (∫ s in a..t, w s) * (1 - 3 * ε ^ 2)) * ‖f t - g t‖ :=
      add_le_add le_rfl hm
    _ ≤ ‖q t‖ := hn

/-- A radial difference has the `p` moment whenever its exact sectional
equation has monotonicity margin `p ≤ 1 - 3ε²`. The literal coefficient
is `1`, independent of the interval, curves, weight, connection and radius.
This conditional analytic helper closes no field graph node. -/
theorem stab_radial_difference_moment_of_identity
    {f g q : ℝ → ℂ} {w α : ℝ → ℝ} {a b ε p : ℝ}
    (hab : a ≤ b) (hp0 : 0 < p) (hp : p ≤ 1 - 3 * ε ^ 2)
    (hw : IntervalIntegrable w volume a b)
    (hw0 : ∀ t ∈ Icc a b, 0 ≤ w t)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) (haxis : f a = g a)
    (hfε : ∀ t ∈ Ioo a b, ‖f t‖ ≤ ε)
    (hgε : ∀ t ∈ Ioo a b, ‖g t‖ ≤ ε)
    (hrb : 0 < ∫ s in a..b, w s)
    (hq : AEStronglyMeasurable (fun t => ‖q t‖) (volume.restrict (Ioc a b)))
    (hidentity : ∀ t ∈ Ioo a b,
      HasDerivWithinAt (fun s => f s - g s)
        (q t - (w t / ∫ s in a..t, w s) •
          ((f t - ‖f t‖ ^ 2 • f t) - (g t - ‖g t‖ ^ 2 • g t)) -
          α t • (Complex.I * (f t - g t))) (Icc a b) t) :
    ENNReal.ofReal ‖f b - g b‖ ≤ ∫⁻ t in Ioc a b,
      ENNReal.ofReal (((∫ s in a..t, w s) / (∫ s in a..b, w s)) ^ p * ‖q t‖) := by
  apply ofReal_le_lintegral_damped_radial_kernel hab hp0 hw hw0
    (lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval (hf.sub hg))
    (by change ‖f a - g a‖ = 0
        rw [haxis, sub_self, norm_zero]) hrb hq (fun t _ => norm_nonneg _)
  exact ae_norm_radial_difference_le hp hw hw0 hf hg hfε hgε hidentity

/-- The same radial difference equation gives a weighted Hardy estimate
with the exact coefficient `1/p`, uniformly in all curves and parameters.
The nonnegative integrals require only measurability of the forcing. -/
theorem stab_radial_difference_hardy_of_identity
    {f g q : ℝ → ℂ} {w α : ℝ → ℝ} {a b ε p : ℝ}
    (hab : a ≤ b) (hp0 : 0 < p) (hp : p ≤ 1 - 3 * ε ^ 2)
    (hw : IntervalIntegrable w volume a b)
    (hw0 : ∀ t ∈ Icc a b, 0 ≤ w t)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) (haxis : f a = g a)
    (hfε : ∀ t ∈ Ioo a b, ‖f t‖ ≤ ε)
    (hgε : ∀ t ∈ Ioo a b, ‖g t‖ ≤ ε)
    (hq : AEStronglyMeasurable (fun t => ‖q t‖) (volume.restrict (Ioc a b)))
    (hidentity : ∀ t ∈ Ioo a b,
      HasDerivWithinAt (fun s => f s - g s)
        (q t - (w t / ∫ s in a..t, w s) •
          ((f t - ‖f t‖ ^ 2 • f t) - (g t - ‖g t‖ ^ 2 • g t)) -
          α t • (Complex.I * (f t - g t))) (Icc a b) t) :
    (∫⁻ t in Ioc a b, ENNReal.ofReal
      (w t / (∫ s in a..t, w s) * ‖f t - g t‖)) ≤
        ENNReal.ofReal p⁻¹ * ∫⁻ t in Ioc a b, ENNReal.ofReal ‖q t‖ := by
  apply lintegral_damped_radial_le hab hp0 hw hw0
    (lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval (hf.sub hg))
    (fun t _ => norm_nonneg _)
    (by
      change ‖f a - g a‖ = 0
      rw [haxis, sub_self, norm_zero])
    hq (fun t _ => norm_nonneg _)
  exact ae_norm_radial_difference_le hp hw hw0 hf hg hfε hgε hidentity

end EmcsfAcExtension.Local
