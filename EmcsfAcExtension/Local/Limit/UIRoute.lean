module

public import EmcsfAcExtension.Local.Limit.UI
import EmcsfAcExtension.Local.Limit.UIAux
import EmcsfAcExtension.Infra.Mixed.Envelope

/-! # The coefficient-one strong-comparison route for envelopes

`charged_SF_new_version.tex:L5567–5576`: the L¹ distance of the scalar norm envelopes
is bounded by the mixed-envelope distance of the original fields. Together
with completeness this supplies the internal project record uniform-integrability route.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

private theorem sup_enorm_difference_le {a b : ℝ} {f g : ℝ → ℂ} (hab : a ≤ b)
    (hf : BddAbove ((fun x => ‖f x‖) '' Icc a b))
    (hg : BddAbove ((fun x => ‖g x‖) '' Icc a b))
    (hd : BddAbove ((fun x => ‖f x - g x‖) '' Icc a b)) :
    ENNReal.ofReal |(⨆ x ∈ Icc a b, ‖f x‖ₑ).toReal - (⨆ x ∈ Icc a b, ‖g x‖ₑ).toReal| ≤
      ⨆ x ∈ Icc a b, ‖f x - g x‖ₑ := by
  have hfn : 0 ≤ normEnvelopeReal (fun x _ => f x) a b :=
    (norm_nonneg (f a)).trans
      (norm_le_normEnvelopeReal (f := fun x _ => f x) hf ⟨le_rfl, hab⟩)
  have hgn : 0 ≤ normEnvelopeReal (fun x _ => g x) a b :=
    (norm_nonneg (g a)).trans
      (norm_le_normEnvelopeReal (f := fun x _ => g x) hg ⟨le_rfl, hab⟩)
  change ENNReal.ofReal |(normEnvelope (fun x _ => f x) a b).toReal -
    (normEnvelope (fun x _ => g x) a b).toReal| ≤
      normEnvelope (fun x _ => f x - g x) a b
  rw [normEnvelope_eq_ofReal hab hf, normEnvelope_eq_ofReal hab hg,
    normEnvelope_eq_ofReal hab hd, ENNReal.toReal_ofReal hfn, ENNReal.toReal_ofReal hgn]
  exact ENNReal.ofReal_le_ofReal (Mixed.abs_normEnvelopeReal_sub_le hab hf hg hd)

/-- [internal]
Both scalar envelope distances are bounded by the original mixed distances with
the literal coefficient one. The bound is uniform in the coupling, time, data,
and all classical derivative suprema. -/
theorem Stab.envelope_difference_le {e T : ℝ} {S₁ S₂ : Fields} (hT : 0 < T)
    (h₁ : IsC1Solution e S₁ (triangle 0 T)) (h₂ : IsC1Solution e S₂ (triangle 0 T)) :
    (∫⁻ v in Icc 0 T, ENNReal.ofReal
      |(outEnv 0 (jC1 (triangle 0 T) S₁) v).toReal -
        (outEnv 0 (jC1 (triangle 0 T) S₂) v).toReal|) ≤ jDist T S₁ S₂ ∧
      (∫⁻ u in Icc 0 T, ENNReal.ofReal
        |(inEnv T (kC1 e (triangle 0 T) S₁) u).toReal -
          (inEnv T (kC1 e (triangle 0 T) S₂) u).toReal|) ≤ kDist e T S₁ S₂ := by
  have hj₁ := h₁.continuousOn_jC1 hT
  have hj₂ := h₂.continuousOn_jC1 hT
  have hk₁ := h₁.continuousOn_kC1 hT
  have hk₂ := h₂.continuousOn_kC1 hT
  have hjd : ContinuousOn (Function.uncurry (fun u v =>
      jC1 (triangle 0 T) S₁ u v - jC1 (triangle 0 T) S₂ u v)) (triangle 0 T) := by
    apply (hj₁.sub hj₂).congr
    intro p hp
    rfl
  constructor
  · apply setLIntegral_mono' measurableSet_Icc
    intro v hv
    exact sup_enorm_difference_le hv.1 (bddAbove_norm_incoming hj₁ hv)
      (bddAbove_norm_incoming hj₂ hv) (bddAbove_norm_incoming hjd hv)
  · apply setLIntegral_mono' measurableSet_Icc
    intro u hu
    have hsec : Continuous (fun v : ℝ => (u, v)) := continuous_const.prodMk continuous_id
    have hm : MapsTo (fun v : ℝ => (u, v)) (Icc u T) (triangle 0 T) :=
      fun v hv => ⟨hu.1, hv.1, hv.2⟩
    have hc₁ : ContinuousOn (fun v => kC1 e (triangle 0 T) S₁ u v) (Icc u T) := by
      apply (hk₁.comp hsec.continuousOn hm).congr
      intro v hv
      rfl
    have hc₂ : ContinuousOn (fun v => kC1 e (triangle 0 T) S₂ u v) (Icc u T) := by
      apply (hk₂.comp hsec.continuousOn hm).congr
      intro v hv
      rfl
    have hcd : ContinuousOn (fun v => kC1 e (triangle 0 T) S₁ u v -
        kC1 e (triangle 0 T) S₂ u v) (Icc u T) := by
      apply (hc₁.sub hc₂).congr
      intro v hv
      rfl
    exact sup_enorm_difference_le hu.2 (isCompact_Icc.bddAbove_image hc₁.norm)
      (isCompact_Icc.bddAbove_image hc₂.norm)
      (isCompact_Icc.bddAbove_image hcd.norm)

end EmcsfAcExtension.Local
