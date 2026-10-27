module

public import EmcsfAcExtension.Local.Defs.Envelope
public import EmcsfAcExtension.Local.Stability.JCloseLinear
import EmcsfAcExtension.Local.Stability.MomentsFieldMeasurable

/-! # Outgoing transport controls the incoming label envelope

Classical interior equations and integrable forcing are sufficient at the
axis. All estimates use the actual suprema of the closed characteristic.
-/

public section

open Set MeasureTheory Complex Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- The incoming label envelope of an outgoing linear transport.
The multiplier is exactly `exp B`; the real propagator budget is explicit.
Forcing integrability is needed only on almost every outgoing section. -/
theorem inEnv_integral_le_of_transport {T B : ℝ} {g c q : ℝ → ℝ → ℂ}
    (_hT : 0 ≤ T) (hg : ContinuousOn (Function.uncurry g) (triangle 0 T))
    (hc : ∀ u ∈ Icc 0 T, IntervalIntegrable (c u) volume u T)
    (hq : ∀ᵐ u ∂volume.restrict (Icc 0 T), IntervalIntegrable (q u) volume u T)
    (hd : ∀ u ∈ Icc 0 T, ∀ v ∈ Ioo u T,
      HasDerivAt (g u) (c u v * g u v + q u v) v)
    (hB : ∀ u ∈ Icc 0 T, ∀ s ∈ Icc u T, ∀ t ∈ Icc s T,
      (∫ v in s..t, c u v).re ≤ B) :
    (∫⁻ u in Icc 0 T, inEnv T g u) ≤ ENNReal.ofReal (Real.exp B) *
      ((∫⁻ u in Icc 0 T, ‖g u u‖ₑ) +
        ∫⁻ u in Icc 0 T, ∫⁻ v in Icc u T, ‖q u v‖ₑ) := by
  have hg₀ : ContinuousOn (fun u => g u u) (Icc 0 T) :=
    hg.comp (continuous_id.prodMk continuous_id).continuousOn
      (fun u hu => ⟨hu.1, le_rfl, hu.2⟩)
  have hmeas₀ : AEMeasurable (fun u => ‖g u u‖ₑ) (volume.restrict (Icc 0 T)) :=
    hg₀.enorm.aemeasurable measurableSet_Icc
  calc
    _ ≤ ∫⁻ u in Icc 0 T, ENNReal.ofReal (Real.exp B) *
        (‖g u u‖ₑ + ∫⁻ v in Icc u T, ‖q u v‖ₑ) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc, hq] with u hu hqu
      have hgu : ContinuousOn (g u) (Icc u T) :=
        hg.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun v hv => ⟨hu.1, hv.1, hv.2⟩)
      have hac := ac_of_continuous_transport hu.2 hgu (hc u hu) hqu (hd u hu)
      have hbound := norm_transport_le_exp_budget hu.2 hac (hc u hu) hqu
        (ae_deriv_eq_of_transport (hd u hu)) (hB u hu)
      have hqnorm : (∫⁻ v in Icc u T, ‖q u v‖ₑ) =
          ENNReal.ofReal (∫ v in u..T, ‖q u v‖) := by
        rw [intervalIntegral.integral_of_le hu.2, restrict_Ioc_eq_restrict_Icc]
        exact (ofReal_integral_norm_eq_lintegral_enorm
          ((intervalIntegrable_iff_integrableOn_Icc_of_le hu.2).mp hqu)).symm
      apply iSup₂_le
      intro v hv
      rw [← ofReal_norm, hqnorm, ← ofReal_norm,
        ← ENNReal.ofReal_add (norm_nonneg _) (intervalIntegral.integral_nonneg hu.2
          (fun _ _ => norm_nonneg _)), ← ENNReal.ofReal_mul (Real.exp_pos B).le]
      apply ENNReal.ofReal_le_ofReal
      apply (hbound v hv).trans
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos B).le
      apply add_le_add le_rfl
      exact intervalIntegral.integral_mono_interval le_rfl hv.1 hv.2
        (Eventually.of_forall (fun _ => norm_nonneg _)) hqu.norm
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_left' hmeas₀]

end EmcsfAcExtension.Local.Stab
