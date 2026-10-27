module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Infra.LinearTransport

/-! # Modulus bounds for the characteristic transport

Integrating factors retain only the real part of the homogeneous coefficient.
This supplies the amplification and damping step of
`charged_SF_new_version.tex:L4674–L4679` and `charged_SF_new_version.tex:L4734–L4743`.
-/

public section

open Set MeasureTheory Filter Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- A complex characteristic with continuous coefficient and forcing satisfies
the exact endpoint integrating-factor formula. No constant or smallness
assumption is implicit. Only interior derivatives are required. -/
theorem characteristic_transport_formula {a b : ℝ} {g c q : ℝ → ℂ}
    (hab : a ≤ b) (hg : ContinuousOn g (Icc a b))
    (hc : ContinuousOn c (Icc a b)) (hq : ContinuousOn q (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt g (c x * g x + q x) x) :
    g b = Complex.exp (∫ x in a..b, c x) * g a +
      ∫ x in a..b, Complex.exp (∫ y in x..b, c y) * q x := by
  have hi := hc.intervalIntegrable_of_Icc (μ := volume) hab
  let w : ℝ → ℂ := fun x => Complex.exp (∫ y in x..b, c y)
  have cw : ContinuousOn w (Icc a b) := by
    apply Complex.continuous_exp.comp_continuousOn
    apply (intervalIntegral.continuousOn_primitive_interval_left
      (show IntegrableOn c (uIcc a b) volume from ?_)).mono (by
        rw [uIcc_of_le hab])
    rw [uIcc_of_le hab]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hi
  have hwq := (cw.mul hq).intervalIntegrable_of_Icc (μ := volume) hab
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab (cw.mul hg)
    (f' := fun x => w x * q x) (fun x hx => ?_) hwq
  · have hwb : w b = 1 := by simp [w]
    simp only [Pi.mul_apply, hwb, one_mul] at hf
    dsimp only [w] at hf
    linear_combination -hf
  · have hxc : ContinuousAt c x := (hc x ⟨hx.1.le, hx.2.le⟩).continuousAt
      (Icc_mem_nhds hx.1 hx.2)
    have hix : IntervalIntegrable c volume x b := hi.mono_set (by
      rw [uIcc_of_le hx.2.le, uIcc_of_le hab]
      exact Icc_subset_Icc hx.1.le le_rfl)
    have dw : HasDerivAt w (w x * (-c x)) x :=
      (intervalIntegral.integral_hasDerivAt_left hix
        (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
          (hc.mono Ioo_subset_Icc_self) x hx) hxc).cexp
    apply (dw.mul (hd x hx)).congr_deriv
    ring

/-- A common upper bound for the moduli of all propagators bounds the
transported modulus. The displayed factor `H` is exact and uniform in the
coefficient, the forcing, and the interval. Imaginary coefficients have no
effect on this factor. -/
theorem characteristic_transport_norm_le {a b H : ℝ} {g c q : ℝ → ℂ}
    (hab : a ≤ b) (hg : ContinuousOn g (Icc a b))
    (hc : ContinuousOn c (Icc a b)) (hq : ContinuousOn q (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt g (c x * g x + q x) x)
    (hH : ∀ x ∈ Icc a b, Real.exp (∫ y in x..b, (c y).re) ≤ H) :
    ‖g b‖ ≤ H * (‖g a‖ + ∫ x in a..b, ‖q x‖) := by
  have hi := hc.intervalIntegrable_of_Icc (μ := volume) hab
  let w : ℝ → ℂ := fun x => Complex.exp (∫ y in x..b, c y)
  have cw : ContinuousOn w (Icc a b) := by
    apply Complex.continuous_exp.comp_continuousOn
    apply (intervalIntegral.continuousOn_primitive_interval_left
      (show IntegrableOn c (uIcc a b) volume from ?_)).mono (by
        rw [uIcc_of_le hab])
    rw [uIcc_of_le hab]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hi
  have hn (x : ℝ) (hx : x ∈ Icc a b) : ‖w x‖ ≤ H := by
    dsimp only [w]
    have hix : IntervalIntegrable c volume x b := hi.mono_set (by
      rw [uIcc_of_le hx.2, uIcc_of_le hab]
      exact Icc_subset_Icc hx.1 le_rfl)
    have he : (∫ y in x..b, c y).re = ∫ y in x..b, (c y).re :=
      (Complex.reCLM.intervalIntegral_comp_comm hix).symm
    rw [Complex.norm_exp, he]
    exact hH x hx
  rw [characteristic_transport_formula hab hg hc hq hd]
  calc
    _ ≤ ‖w a * g a‖ + ‖∫ x in a..b, w x * q x‖ := norm_add_le _ _
    _ ≤ H * ‖g a‖ + ∫ x in a..b, ‖w x * q x‖ := by
      apply add_le_add
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hn a ⟨le_rfl, hab⟩) (norm_nonneg _)
      · exact intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ H * ‖g a‖ + ∫ x in a..b, H * ‖q x‖ := by
      apply add_le_add le_rfl
      apply intervalIntegral.integral_mono_on hab
        ((cw.mul hq).norm.intervalIntegrable_of_Icc hab)
        ((hq.norm.const_mul H).intervalIntegrable_of_Icc hab)
      intro x hx
      simp only [Pi.mul_apply, norm_mul]
      exact mul_le_mul_of_nonneg_right (hn x hx) (norm_nonneg _)
    _ = _ := by rw [intervalIntegral.integral_const_mul, mul_add]

end EmcsfAcExtension.Local
