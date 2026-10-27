module

public import EmcsfAcExtension.Local.Stability.JCloseInitial
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity
import EmcsfAcExtension.Infra.AC.Variation

/-! # Exact initial derivative-norm identities for AC data

The within-triangle partial agrees with the ordinary datum derivative
almost everywhere. No endpoint derivative value is used.
-/

public section

open Set MeasureTheory Complex Filter

namespace EmcsfAcExtension.Local.Stab

/-- The initial ordinary partial has norm integral exactly the datum's
real variation, with universal coefficient one. -/
theorem initial_partial_integral_eq_variation {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hs : StabSetting e T ε M A S h) :
    (∫ v in 0..T, ‖pdV (triangle 0 T) S.a 0 v‖) = datumVar h T := by
  rw [datumVar, (initial_datum_ac hs).toReal_eVariationOn_eq_integral_norm_deriv hs.pos.le]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le hs.pos.le, restrict_Ioc_eq_restrict_Icc]
  filter_upwards [initial_pdV_eq_deriv_ae hs] with v hv
  rw [hv]

/-- The initial partial-difference norm integral is exactly the variation
of the difference datum, with universal coefficient one. -/
theorem initial_partial_difference_integral_eq_variation {e T ε M A : ℝ}
    {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (hs₁ : StabSetting e T ε M A S₁ h₁) (hs₂ : StabSetting e T ε M A S₂ h₂) :
    (∫ v in 0..T, ‖pdV (triangle 0 T) S₁.a 0 v - pdV (triangle 0 T) S₂.a 0 v‖) =
      datumVar (h₁ - h₂) T := by
  have hac₁ := initial_datum_ac hs₁
  have hac₂ := initial_datum_ac hs₂
  rw [datumVar, (hac₁.sub hac₂).toReal_eVariationOn_eq_integral_norm_deriv hs₁.pos.le]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le hs₁.pos.le, restrict_Ioc_eq_restrict_Icc]
  filter_upwards [initial_pdV_eq_deriv_ae hs₁, initial_pdV_eq_deriv_ae hs₂,
    ae_restrict_of_ae hac₁.ae_differentiableAt_of_mem_uIcc,
    ae_restrict_of_ae hac₂.ae_differentiableAt_of_mem_uIcc,
    ae_restrict_mem measurableSet_Icc] with v hv₁ hv₂ hd₁ hd₂ hv
  have hv' : v ∈ uIcc 0 T := Icc_subset_uIcc hv
  have heq : deriv (h₁ - h₂) v = deriv h₁ v - deriv h₂ v := by
    simpa only [Pi.sub_def] using! ((hd₁ hv').hasDerivAt.sub (hd₂ hv').hasDerivAt).deriv
  rw [hv₁, hv₂, heq]

end EmcsfAcExtension.Local.Stab
