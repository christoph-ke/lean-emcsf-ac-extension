module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Defs.Bounds
import EmcsfAcExtension.Local.Stability.MainLipschitz
import EmcsfAcExtension.Local.Stability.ExtendedMain

/-! # The complete smooth stability theorem

Main Lipschitz stability supplies the only comparison input to the
independent extended-record assembly. Every internal project record field is included.
-/

public section

namespace EmcsfAcExtension.Local

/-- [internal]
The full §1.3 stability export for the Limit layer. The positive
threshold and constant depend only on the envelope-bound constant `A`
and the fixed box, before every field, datum, coupling, scale and
background parameter. The conclusion contains all ten clauses,
including `hardyDiff`, `muFluxDiff`, `geomEnvDiff` and `xiRatioArea`,
uniformly in higher initial derivatives and minimum radii. -/
theorem stab_extended (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        StabBounds C e T M (dataDist h₁ h₂ T) S₁ S₂ := by
  obtain ⟨ηm, C₀, hηm, hC₀, hMain⟩ := stab_main_lipschitz A hA
  obtain ⟨ηx, C, hηx, hC, hExtended⟩ := stab_extended_of_main_lipschitz A C₀ hA hC₀
  refine ⟨min ηm ηx, C, lt_min hηm hηx, hC, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall
  exact hExtended T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hsmall.trans (min_le_right _ _))
    (hMain T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hsmall.trans (min_le_left _ _)))

end EmcsfAcExtension.Local
