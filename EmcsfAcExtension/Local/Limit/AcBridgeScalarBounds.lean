module

public import EmcsfAcExtension.Local.Assembly.Bundles
public import EmcsfAcExtension.Infra.W11.Completeness

/-! # Ordinary scalar comparisons on actual AC sections

internal project record item 7.5: the passed variation estimate becomes an ordinary
derivative estimate for arbitrary AC representatives, without smoothness.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- Extract the uniform pointwise geometry and scalar estimate from the frozen
stability conclusion. The coefficient is unchanged. Nonnegativity of both
integrable envelopes follows from their actual full-section domination. -/
theorem StabConclusion.pointwise_of_stability {C e T : ℝ}
    {h₁ h₂ : ℝ → ℂ} {S₁ S₂ : Fields} (hT : 0 ≤ T)
    (hb : StabConclusion C e T h₁ h₂ S₁ S₂) :
    ∀ p ∈ triangle 0 T,
      |S₁.lam p.1 p.2 - S₂.lam p.1 p.2| + |S₁.nu p.1 p.2 - S₂.nu p.1 p.2| +
        |S₁.r p.1 p.2 - S₂.r p.1 p.2| / S₁.r p.1 p.2 +
        ‖S₁.a p.1 p.2 - S₂.a p.1 p.2‖ + ‖S₁.b p.1 p.2 - S₂.b p.1 p.2‖ +
        ‖S₁.phi p.1 p.2 - S₂.phi p.1 p.2‖ ≤ C * dataDist h₁ h₂ T := by
  obtain ⟨⟨J, K, _, _, hj, hk, hmain⟩, _⟩ := hb
  have hJ : 0 ≤ ∫ v in (0 : ℝ)..T, J v := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hT
    filter_upwards [hj 0 ⟨le_rfl, hT⟩] with v hv
    exact (norm_nonneg _).trans hv
  have hK : 0 ≤ ∫ u in (0 : ℝ)..T, K u := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hT
    filter_upwards [hk T ⟨hT, le_rfl⟩] with u hu
    exact (norm_nonneg _).trans hu
  intro p hp
  have hh := hmain p hp p hp p hp p hp
  change _ ≤ C * (‖h₁ 0 - h₂ 0‖ + datumVar (h₁ - h₂) T)
  linarith only [hh, hJ, hK]

/-- Convert the quantitative characteristic variation comparison to ordinary
L¹ derivative comparisons on the original AC pair. The coefficient `C` is
retained, uniformly over both characteristic families and all pair parameters.
This helper consumes regularity only on the sections being differentiated. -/
theorem StabConclusion.derivative_bounds_of_ac {C e T : ℝ}
    {h₁ h₂ : ℝ → ℂ} {S₁ S₂ : Fields}
    (hC : 0 ≤ C) (hb : StabConclusion C e T h₁ h₂ S₁ S₂)
    (ho₁ : ∀ u ∈ Icc 0 T, AbsolutelyContinuousOnInterval (S₁.a u) u T)
    (ho₂ : ∀ u ∈ Icc 0 T, AbsolutelyContinuousOnInterval (S₂.a u) u T)
    (hi₁ : ∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun u => S₁.b u v) 0 v)
    (hi₂ : ∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun u => S₂.b u v) 0 v) :
    (∀ u ∈ Icc 0 T, (∫ v in u..T,
      ‖deriv (S₁.a u) v - deriv (S₂.a u) v‖) ≤ C * dataDist h₁ h₂ T) ∧
    (∀ v ∈ Icc 0 T, (∫ u in (0 : ℝ)..v,
      ‖deriv (fun u => S₁.b u v) u - deriv (fun u => S₂.b u v) u‖) ≤
        C * dataDist h₁ h₂ T) := by
  have hD : 0 ≤ C * dataDist h₁ h₂ T :=
    mul_nonneg hC (add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg)
  constructor
  · intro u hu
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      ((le_iSup₂ u hu).trans (le_self_add.trans hb.2))
    change (eVariationOn (S₁.a u - S₂.a u) (Icc u T)).toReal ≤
      (ENNReal.ofReal (C * dataDist h₁ h₂ T)).toReal at hh
    rw [ENNReal.toReal_ofReal hD] at hh
    simpa only [W11.variation_sub_eq_integral hu.2 (ho₁ u hu) (ho₂ u hu)] using hh
  · intro v hv
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      ((le_iSup₂ v hv).trans (le_add_self.trans hb.2))
    change (eVariationOn ((fun u => S₁.b u v) - (fun u => S₂.b u v)) (Icc 0 v)).toReal ≤
      (ENNReal.ofReal (C * dataDist h₁ h₂ T)).toReal at hh
    rw [ENNReal.toReal_ofReal hD] at hh
    simpa only [W11.variation_sub_eq_integral hv.1 (hi₁ v hv) (hi₂ v hv)] using hh

end EmcsfAcExtension.Local
