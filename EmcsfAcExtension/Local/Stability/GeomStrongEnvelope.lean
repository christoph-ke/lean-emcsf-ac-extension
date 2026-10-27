module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeomStrongTransport
import EmcsfAcExtension.Local.Stability.GeomStrongRegularity
import EmcsfAcExtension.Local.Calculus.Geometric
import EmcsfAcExtension.Local.Calculus.GeometricAxis

/-! # Actual geometric envelope transport differences

The differentiated field equations and the regular-axis match supply
the hypotheses of the positive envelope transport estimate. The two
source integration orders remain explicit before area closure.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [internal]
The renormalized geometric envelope difference is bounded by its
initial difference and the actual common source in both integration
orders. The numerical coefficients `2,2,1` are universal, independently
of all field parameters, data, derivative suprema and minimum radii.
-/
theorem stab_geometric_envelope_transport_difference_c1
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) :
    (∫⁻ v in Icc 0 T, outEnv 0 (fun u v =>
      geomL (triangle 0 T) S₁ u v - geomL (triangle 0 T) S₂ u v) v) +
    (∫⁻ u in Icc 0 T, inEnv T (fun u v =>
      geomN (triangle 0 T) S₁ u v - geomN (triangle 0 T) S₂ u v) u) ≤
      2 * (∫⁻ v in Icc 0 T, ‖geomL (triangle 0 T) S₁ 0 v -
        geomL (triangle 0 T) S₂ 0 v‖ₑ) +
      2 * (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, ‖geomSource S₁ u v - geomSource S₂ u v‖ₑ) +
      ∫⁻ u in Icc 0 T, ∫⁻ v in Icc u T, ‖geomSource S₁ u v - geomSource S₂ u v‖ₑ := by
  have cL : ContinuousOn (Function.uncurry (fun u v =>
      geomL (triangle 0 T) S₁ u v - geomL (triangle 0 T) S₂ u v)) (triangle 0 T) := by
    simpa only [Function.uncurry_def, Pi.sub_apply] using!
      (stab_geomL_continuous_c1 h₁s).sub (stab_geomL_continuous_c1 h₂s)
  have cN : ContinuousOn (Function.uncurry (fun u v =>
      geomN (triangle 0 T) S₁ u v - geomN (triangle 0 T) S₂ u v)) (triangle 0 T) := by
    simpa only [Function.uncurry_def, Pi.sub_apply] using!
      (stab_geomN_continuous_c1 h₁s).sub (stab_geomN_continuous_c1 h₂s)
  apply stab_geometric_envelopes_of_transport_c1 h₁s.pos.le cL cN
  · intro v hv
    have hm : MapsTo (fun u : ℝ => (u, v)) (Icc 0 v) (triangle 0 T) :=
      fun u hu => ⟨hu.1, hu.2, hv.2⟩
    exact ((stab_geomSource_aemeasurable_on_c1 h₁s
      (continuous_id.prodMk continuous_const).continuousOn hm).sub
      (stab_geomSource_aemeasurable_on_c1 h₂s
        (continuous_id.prodMk continuous_const).continuousOn hm)).aestronglyMeasurable
  · intro u hu
    have hm : MapsTo (fun v : ℝ => (u, v)) (Icc u T) (triangle 0 T) :=
      fun v hv => ⟨hu.1, hv.1, hv.2⟩
    exact ((stab_geomSource_aemeasurable_on_c1 h₁s
      (continuous_const.prodMk continuous_id).continuousOn hm).sub
      (stab_geomSource_aemeasurable_on_c1 h₂s
        (continuous_const.prodMk continuous_id).continuousOn hm)).aestronglyMeasurable
  · intro v hv u hu
    have d₁ := (bv_geom_trans_out h₁s.c1 hu.1.le hu.2 hv.2).hasDerivAt
      (Icc_mem_nhds hu.1 hu.2)
    have d₂ := (bv_geom_trans_out h₂s.c1 hu.1.le hu.2 hv.2).hasDerivAt
      (Icc_mem_nhds hu.1 hu.2)
    simpa only [Pi.sub_apply] using! d₁.sub d₂
  · intro u hu v hv
    have d₁ := (bv_geom_trans_in h₁s.c1 hu.1 hv.1 hv.2.le).hasDerivAt
      (Icc_mem_nhds hv.1 hv.2)
    have d₂ := (bv_geom_trans_in h₂s.c1 hu.1 hv.1 hv.2.le).hasDerivAt
      (Icc_mem_nhds hv.1 hv.2)
    simpa only [Pi.sub_apply] using! d₁.sub d₂
  · intro t ht
    rw [← (Area.smooth_geometric_axis_match h₁s.pos h₁s.c1 ht).1,
      ← (Area.smooth_geometric_axis_match h₂s.pos h₂s.c1 ht).1]

end EmcsfAcExtension.Local
