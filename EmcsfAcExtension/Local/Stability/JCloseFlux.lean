module

public import EmcsfAcExtension.Local.Stability.JCloseCoefficient
public import EmcsfAcExtension.Local.Stability.SourceDifferenceCoefficient

/-! # Sharp incoming coefficient forcing for j

The incoming flux comparison is multiplied by the opposite label envelope
before its full `σ ε³ H` remainder is simplified.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- [internal]
 Sharp coefficient forcing in the incoming j comparison.
`C` depends only on the fixed envelope and incoming flux constants `A,D`,
uniformly in every physical parameter, pair and derivative supremum. -/
theorem j_coefficient_area_sharp_of_differences (A D : ℝ) (hA : 0 < A) (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      IncomingFluxDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v,
        ‖((jRealCoefficient S₁ u v - jRealCoefficient S₂ u v : ℝ) : ℂ) *
          jC1 (triangle 0 T) S₂ u v‖ₑ) ≤ ENNReal.ofReal
        (C * (ε ^ 2 * (kDist e T S₁ S₂).toReal + ε ^ 3 * (geomDist T S₁ S₂).toReal +
          sigma e M T * ε ^ 3 * ((jDist T S₁ S₂).toReal + ε * (geomDist T S₁ S₂).toReal +
            ε * dataDist h₁ h₂ T / M))) := by
  refine ⟨A * D, mul_pos hA hD, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hflux
  have hε : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans
    (hs₂.box.2 (0, 0) ⟨le_rfl, le_rfl, hs₂.pos.le⟩).2.2.2.2.2.1
  have hσ : 0 ≤ sigma e M T := by unfold sigma; positivity
  have hM : 0 ≤ M := zero_le_one.trans hs₂.box.1
  have hδ : 0 ≤ dataDist h₁ h₂ T := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hbase := homogeneous_coefficient_area_of_differences hs₂ hflux
  have henv := (le_add_right le_rfl).trans hs₂.env
  have heq : (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v,
      ‖((jRealCoefficient S₁ u v - jRealCoefficient S₂ u v : ℝ) : ℂ) * jC1 (triangle 0 T) S₂ u v‖ₑ)
          =
      (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v,
      ‖(((-S₁.nu u v / S₁.r u v * ‖S₁.xi u v / S₁.nu u v‖ ^ 2) -
        (-S₂.nu u v / S₂.r u v * ‖S₂.xi u v / S₂.nu u v‖ ^ 2) : ℝ) : ℂ) *
          jC1 (triangle 0 T) S₂ u v‖ₑ) := by
    apply setLIntegral_congr_fun measurableSet_Icc
    intro v hv
    apply setLIntegral_congr_fun measurableSet_Icc
    intro u hu
    dsimp only [jRealCoefficient]
    rw [j_coefficient_eq_flux hs₁ ⟨hu.1, hu.2, hv.2⟩,
      j_coefficient_eq_flux hs₂ ⟨hu.1, hu.2, hv.2⟩]
  rw [heq]
  apply (hbase.trans (mul_le_mul' le_rfl henv)).trans
  apply le_trans (b := ENNReal.ofReal
    ((A * D) * (ε ^ 2 * (kDist e T S₁ S₂).toReal +
      ε ^ 3 * (geomDist T S₁ S₂).toReal + sigma e M T * ε ^ 3 / M *
        ((jDist T S₁ S₂).toReal + ε * (geomDist T S₁ S₂).toReal +
          ε * dataDist h₁ h₂ T / M))))
  · apply le_of_eq
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ D *
      (ε * (kDist e T S₁ S₂).toReal + ε ^ 2 * (geomDist T S₁ S₂).toReal +
        sigma e M T * ε ^ 2 / M * ((jDist T S₁ S₂).toReal + ε * (geomDist T S₁ S₂).toReal +
          ε * dataDist h₁ h₂ T / M)))]
    congr 1
    ring
  · apply ENNReal.ofReal_le_ofReal
    gcongr
    exact div_le_self (by positivity : 0 ≤ sigma e M T * ε ^ 3) hs₂.box.1

end EmcsfAcExtension.Local.Stab
