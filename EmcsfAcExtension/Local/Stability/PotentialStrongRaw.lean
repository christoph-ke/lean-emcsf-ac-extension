module

public import EmcsfAcExtension.Local.Stability.PotentialSource
import EmcsfAcExtension.Local.Stability.PotentialPrimitiveC1
import EmcsfAcExtension.Local.Stability.PotentialArea

/-! # Incoming potential derivative differences from the true area density

The complete-section primitive identity identifies the actual ordinary
partial before its norm is estimated. The area density is a continuous
representative of the A11p expression, identified off the diagonal.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- An outgoing primitive of a continuous triangle density has incoming
section L¹ norm at most the complete density area norm. The coefficient
one is universal, with no quantitative regularity or radius bound. -/
theorem stab_potential_primitive_section_norm_le_area {T : ℝ} {H : ℝ → ℝ → ℝ}
    (cH : ContinuousOn (Function.uncurry H) (triangle 0 T)) {v : ℝ} (hv : v ∈ Icc 0 T) :
    (∫⁻ u in Icc 0 v, ‖∫ w in u..v, H u w‖ₑ) ≤
      ∫⁻ p in triangle 0 T, ‖H p.1 p.2‖ₑ := by
  have hsub : triangle 0 v ⊆ triangle 0 T :=
    fun p hp => ⟨hp.1, hp.2.1, hp.2.2.trans hv.2⟩
  have hm : AEMeasurable (fun p : ℝ × ℝ => ‖H p.1 p.2‖ₑ)
      (volume.restrict (triangle 0 v)) := by
    simpa only [Function.uncurry_def] using!
      (cH.mono hsub).enorm.aemeasurable (μ := volume) (measurableSet_triangle 0 v)
  have hb : (∫⁻ u in Icc 0 v, ‖∫ w in u..v, H u w‖ₑ) ≤
      ∫⁻ u in Icc 0 v, ∫⁻ w in Icc u v, ‖H u w‖ₑ := by
    apply setLIntegral_mono' measurableSet_Icc
    intro u hu
    rw [intervalIntegral.integral_of_le hu.2, restrict_Ioc_eq_restrict_Icc]
    exact enorm_integral_le_lintegral_enorm _
  apply hb.trans
  rw [← stab_triangle_lintegral_out_of_aemeasurable hm]
  exact lintegral_mono_set hsub

/-- [internal]
The classical incoming potential-partial difference is bounded by the
area norm of its two genuine continuous incoming source representatives.
The exact coefficient one is universal. Both representatives agree with
A11p off the axis; the full general-AC node remains in internal project record. No source
area bound, strong derivative conclusion or radius cutoff is assumed.
-/
theorem stab_potential_incoming_difference_le_area_c1
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) :
    ∃ H₁ H₂ : ℝ → ℝ → ℝ,
      ContinuousOn (Function.uncurry H₁) (triangle 0 T) ∧
      ContinuousOn (Function.uncurry H₂) (triangle 0 T) ∧
      (∀ u v, 0 ≤ u → u < v → v ≤ T → H₁ u v = potentialIncomingSource e (triangle 0 T) S₁ u v) ∧
      (∀ u v, 0 ≤ u → u < v → v ≤ T → H₂ u v = potentialIncomingSource e (triangle 0 T) S₂ u v) ∧
      (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
        ‖pdU (triangle 0 T) S₁.A u v - pdU (triangle 0 T) S₂.A u v‖ₑ) ≤
        ∫⁻ p in triangle 0 T, ‖H₁ p.1 p.2 - H₂ p.1 p.2‖ₑ := by
  obtain ⟨H₁, cH₁, hH₁, hP₁⟩ := stab_potential_incoming_primitive_c1 h₁s
  obtain ⟨H₂, cH₂, hH₂, hP₂⟩ := stab_potential_incoming_primitive_c1 h₂s
  have cH : ContinuousOn (Function.uncurry (fun u v => H₁ u v - H₂ u v)) (triangle 0 T) := by
    simpa only [Function.uncurry_def, Pi.sub_apply] using! cH₁.sub cH₂
  refine ⟨H₁, H₂, cH₁, cH₂, hH₁, hH₂, ?_⟩
  apply iSup₂_le
  intro v hv
  have heq : (∫⁻ u in Icc 0 v, ‖pdU (triangle 0 T) S₁.A u v - pdU (triangle 0 T) S₂.A u v‖ₑ) =
      ∫⁻ u in Icc 0 v, ‖∫ w in u..v, H₁ u w - H₂ u w‖ₑ := by
    apply lintegral_congr_ae
    filter_upwards [(hP₁ v hv).2, (hP₂ v hv).2, ae_restrict_mem measurableSet_Icc] with u hu₁ hu₂ hu
    have hm : MapsTo (fun w : ℝ => (u, w)) (Icc u v) (triangle 0 T) :=
      fun w hw => ⟨hu.1, hw.1, hw.2.trans hv.2⟩
    have cp : ContinuousOn (fun w : ℝ => (u, w)) (Icc u v) :=
      (continuous_const.prodMk continuous_id).continuousOn
    have i₁ : IntervalIntegrable (H₁ u) volume u v := ContinuousOn.intervalIntegrable_of_Icc (μ :=
        volume) hu.2 (cH₁.comp cp hm)
    have i₂ : IntervalIntegrable (H₂ u) volume u v := ContinuousOn.intervalIntegrable_of_Icc (μ :=
        volume) hu.2 (cH₂.comp cp hm)
    rw [hu₁, hu₂, intervalIntegral.integral_sub i₁ i₂]
  rw [heq]
  exact stab_potential_primitive_section_norm_le_area cH hv

end EmcsfAcExtension.Local
