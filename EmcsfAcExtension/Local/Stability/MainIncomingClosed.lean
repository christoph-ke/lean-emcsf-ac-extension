module

public import EmcsfAcExtension.Local.Stability.MainComparison
import EmcsfAcExtension.Local.Stability.MainIncoming

/-! # Incoming normalized field from the first-half comparison records

The derivative and geometry norms are closed before the identity
`b = phi + xi/nu` is used. No incoming field estimate is assumed or read
back from a final norm containing the same conclusion.
-/

public section

open Set Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- [internal]
 Conditional helper for
`restart-sec-bv-stability-independent#incoming-normalized-field-comparison`.
Threshold and constant depend only on fixed `A,D`, uniformly in all pair
parameters and derivative suprema. Only the listed first-half records are inputs. -/
theorem incoming_normalized_field_comparison_of_differences (A D : ℝ) (hA : 0 < A) (hD : 0 < D) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
    ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ^ 2 + sigma e M T ≤ η →
      RatioDifferences D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      FieldDifference D T ε (dataDist h₁ h₂ T) S₁ S₂ →
      ChargeDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      PotentialDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      IncomingFluxDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      OutgoingFluxDifference D T ε S₁ S₂ →
      GeometryDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      supDist T S₁.b S₂.b ≤ ENNReal.ofReal (C * dataDist h₁ h₂ T) := by
  obtain ⟨η₀, L, hη₀, hL, hclose⟩ := comparison_norms_of_differences A D hA hD
  obtain ⟨C, hC, hb⟩ := incoming_normalized_field_comparison_of_closed_distances D L hD hL
  refine ⟨min η₀ 1, C, lt_min hη₀ zero_lt_one, hC, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hsmall hratio hfield hcharge hpot hfi hfo hgeom
  have hσ : 0 ≤ sigma e M T := by unfold sigma; positivity
  have hsmall₁ := hsmall.trans (min_le_right _ _)
  have hε₁ : ε ≤ 1 := by nlinarith only [hsmall₁, hσ]
  have hσ₁ : sigma e M T ≤ 1 := by nlinarith only [hsmall₁, sq_nonneg ε]
  exact hb T e ε M A S₁ S₂ h₁ h₂ hs₁ hs₂ hε₁ hσ₁ hfield hratio
    (hclose T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ (hsmall.trans (min_le_left _ _))
      hratio hfield hcharge hpot hfi hfo hgeom)

end EmcsfAcExtension.Local.Stab
