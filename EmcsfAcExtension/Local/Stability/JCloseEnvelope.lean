module

public import EmcsfAcExtension.Local.Defs.Envelope
public import EmcsfAcExtension.Local.Stability.JCloseLinear
import EmcsfAcExtension.Local.Stability.MomentsFieldMeasurable

/-! # Incoming transport controls the outgoing label envelope

Classical interior equations and integrable forcing are sufficient at the
axis. All estimates use the actual suprema of the closed characteristic.
-/

public section

open Set MeasureTheory Complex Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- The outgoing label envelope of an incoming linear transport.
The multiplier is exactly `exp B`; the real propagator budget is explicit.
Forcing integrability is needed only on almost every incoming section. -/
theorem outEnv_integral_le_of_transport {T B : ℝ} {g c q : ℝ → ℝ → ℂ}
    (_hT : 0 ≤ T) (hg : ContinuousOn (Function.uncurry g) (triangle 0 T))
    (hc : ∀ v ∈ Icc 0 T, IntervalIntegrable (fun u => c u v) volume 0 v)
    (hq : ∀ᵐ v ∂volume.restrict (Icc 0 T),
      IntervalIntegrable (fun u => q u v) volume 0 v)
    (hd : ∀ v ∈ Icc 0 T, ∀ u ∈ Ioo 0 v,
      HasDerivAt (fun w => g w v) (c u v * g u v + q u v) u)
    (hB : ∀ v ∈ Icc 0 T, ∀ s ∈ Icc 0 v, ∀ t ∈ Icc s v,
      (∫ u in s..t, c u v).re ≤ B) :
    (∫⁻ v in Icc 0 T, outEnv 0 g v) ≤ ENNReal.ofReal (Real.exp B) *
      ((∫⁻ v in Icc 0 T, ‖g 0 v‖ₑ) +
        ∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, ‖q u v‖ₑ) := by
  have hg₀ : ContinuousOn (fun v => g 0 v) (Icc 0 T) :=
    hg.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨le_rfl, hv.1, hv.2⟩)
  have hmeas₀ : AEMeasurable (fun v => ‖g 0 v‖ₑ) (volume.restrict (Icc 0 T)) :=
    hg₀.enorm.aemeasurable measurableSet_Icc
  calc
    _ ≤ ∫⁻ v in Icc 0 T, ENNReal.ofReal (Real.exp B) *
        (‖g 0 v‖ₑ + ∫⁻ u in Icc 0 v, ‖q u v‖ₑ) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc, hq] with v hv hqv
      have hgv : ContinuousOn (fun u => g u v) (Icc 0 v) :=
        hg.comp (continuous_id.prodMk continuous_const).continuousOn
          (fun u hu => ⟨hu.1, hu.2, hv.2⟩)
      have hac := ac_of_continuous_transport hv.1 hgv (hc v hv) hqv (hd v hv)
      have hbound := norm_transport_le_exp_budget hv.1 hac (hc v hv) hqv
        (ae_deriv_eq_of_transport (hd v hv)) (hB v hv)
      have hqnorm : (∫⁻ u in Icc 0 v, ‖q u v‖ₑ) =
          ENNReal.ofReal (∫ u in 0..v, ‖q u v‖) := by
        rw [intervalIntegral.integral_of_le hv.1, restrict_Ioc_eq_restrict_Icc]
        exact (ofReal_integral_norm_eq_lintegral_enorm
          ((intervalIntegrable_iff_integrableOn_Icc_of_le hv.1).mp hqv)).symm
      apply iSup₂_le
      intro u hu
      rw [← ofReal_norm, hqnorm, ← ofReal_norm,
        ← ENNReal.ofReal_add (norm_nonneg _) (intervalIntegral.integral_nonneg hv.1
          (fun _ _ => norm_nonneg _)), ← ENNReal.ofReal_mul (Real.exp_pos B).le]
      apply ENNReal.ofReal_le_ofReal
      apply (hbound u hu).trans
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos B).le
      apply add_le_add le_rfl
      exact intervalIntegral.integral_mono_interval le_rfl hu.1 hu.2
        (Eventually.of_forall (fun _ => norm_nonneg _)) hqv.norm
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_left' hmeas₀]

end EmcsfAcExtension.Local.Stab
