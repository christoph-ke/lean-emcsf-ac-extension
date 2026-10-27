module

public import EmcsfAcExtension.Local.Stability.MomentsForcing

/-! # Reversing incoming radial sections

The parameter `t = -u` increases away from the incoming axis. Negation
preserves Lebesgue measure, so both limits and the sign in the radius
primitive are retained explicitly.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- Reversing both endpoints preserves a nonnegative interval integral.
The integrand need not be measurable or integrable. -/
theorem stab_lintegral_neg_Icc (f : ℝ → ℝ≥0∞) (a b : ℝ) :
    (∫⁻ t in Icc (-b) (-a), f (-t)) = ∫⁻ s in Icc a b, f s := by
  simpa only [image_neg_Icc, neg_neg] using
    (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_emb
      (Homeomorph.neg ℝ).measurableEmbedding f (Icc (-b) (-a))

/-- Negation pulls back sectional measurability to the reversed closed
section. This uses preservation of the restricted measures. -/
theorem stab_aestronglyMeasurable_neg_Icc {E : Type*} [TopologicalSpace E]
    {f : ℝ → E} {a b : ℝ} (hf : AEStronglyMeasurable f (volume.restrict (Icc a b))) :
    AEStronglyMeasurable (fun t => f (-t)) (volume.restrict (Icc (-b) (-a))) := by
  have hpre : Neg.neg ⁻¹' Icc a b = Icc (-b) (-a) := by
    ext t
    simp only [mem_preimage, mem_Icc]
    constructor <;> rintro ⟨ht1, ht2⟩ <;> constructor <;> linarith only [ht1, ht2]
  have hm := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
    (measurableSet_Icc (a := a) (b := b))
  rw [hpre] at hm
  exact hf.comp_measurePreserving hm

/-- The incoming radius primitive in the outward parameter `t = -u`.
The weight is `-ν`, so its sign is positive in the fixed box. -/
theorem stab_radius_reflected_integral {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {u v t : ℝ}
    (hu : 0 ≤ u) (_huv : u ≤ v) (hvT : v ≤ T) (ht : t ∈ Icc (-v) (-u)) :
    (∫ s in -v..t, -S.nu (-s) v) = S.r (-t) v := by
  rw [intervalIntegral.integral_comp_neg (f := fun s => -S.nu s v), neg_neg]
  exact stab_radius_in_integral hset (by linarith only [hu, ht.2])
    (by linarith only [ht.1]) hvT

end EmcsfAcExtension.Local
