module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Calculus.AxisMatch
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity
import EmcsfAcExtension.Infra.AC.Variation

/-! # The smooth axis variation budget

The diagonal derivative is the outgoing renormalized derivative in the restart
axis gauge. Its integral is bounded by the outgoing envelope, as used in
`charged_SF_new_version.tex:L4755–L4767`. The proof works on the classical C¹ class.
-/

public section

open Set MeasureTheory Filter Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The scalar variation along the classical regular axis is exactly the
integral of the renormalized diagonal derivative in the restart axis gauge.
The identity is uniform in all parameters and derivative norms.
Positive time is internal project record. -/
theorem smooth_axis_variation_eq_lintegral {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T))
    (hA : ∀ t ∈ Icc 0 T, S.A t t = 0) :
  eVariationOn (fun t => S.phi t t) (Icc 0 T) =
      ∫⁻ t in Icc 0 T, ‖jC1 (triangle 0 T) S t t‖ₑ := by
  have hc : ContDiffOn ℝ 1 (fun t => S.phi t t) (Icc 0 T) :=
    hS.c1_phi.comp (contDiffOn_id.prodMk contDiffOn_id)
      (fun t ht => ⟨ht.1, le_rfl, ht.2⟩)
  have hac : AbsolutelyContinuousOnInterval (fun t => S.phi t t) 0 T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hT.le] using hc
  have cj : ContinuousOn (fun t => jC1 (triangle 0 T) S t t) (Icc 0 T) :=
    (continuousOn_jC1_aux hT hS).comp (f := fun t : ℝ => (t, t))
      (continuous_id.prodMk continuous_id).continuousOn
      (fun t ht => ⟨ht.1, le_rfl, ht.2⟩)
  have hj := cj.intervalIntegrable_of_Icc (μ := volume) hT.le
  have heq : (∫ t in 0..T, ‖deriv (fun t => S.phi t t) t‖) =
      ∫ t in 0..T, ‖jC1 (triangle 0 T) S t t‖ := by
    apply intervalIntegral.integral_congr_ae
    have h0 : ∀ᵐ t : ℝ, t ≠ 0 := by simp [ae_iff, measure_singleton]
    have hT' : ∀ᵐ t : ℝ, t ≠ T := by simp [ae_iff, measure_singleton]
    filter_upwards [h0, hT'] with t ht0 htT ht
    rw [uIoc_of_le hT.le] at ht
    have hd := (bv_axis_match hT hS hA ⟨ht.1.le, ht.2⟩).2
    rw [(hd.hasDerivAt (Icc_mem_nhds ht.1 (lt_of_le_of_ne ht.2 htT))).deriv]
  rw [hac.eVariationOn_eq_integral_norm_deriv hT.le, heq,
    intervalIntegral.integral_of_le hT.le, ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_norm_eq_lintegral_enorm
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mp hj)]

/-- [node restart-sec-independent-area#smooth-axis-variation-budget]
The scalar variation along the regular axis is bounded by the outgoing
envelope. The exact coefficient one is independent of every solution parameter
and of the size of its derivatives. Positive time is internal project record.
-/
theorem smooth_axis_variation_budget {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T))
    (hA : ∀ t ∈ Icc 0 T, S.A t t = 0) :
    eVariationOn (fun t => S.phi t t) (Icc 0 T) ≤
      ∫⁻ v in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S) v := by
  rw [smooth_axis_variation_eq_lintegral hT hS hA]
  apply setLIntegral_mono' measurableSet_Icc
  intro t ht
  exact le_iSup₂_of_le t ⟨ht.1, le_rfl⟩ le_rfl

end EmcsfAcExtension.Local
