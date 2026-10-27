module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeometryDifferenceFeedback
import EmcsfAcExtension.Local.Stability.DifferenceMomentsAbsorption

/-! # Coarse mass comparison from the optical identities

This control suffices in the potential constraint. It is weaker than
the mass-Volterra comparison and carries no tag for that later node.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- Optical mass control by `G + εΔj`. Constants depend only on `A`
and the fixed box, before all other parameters and the pair. This
coarse estimate is not the sharper weighted mass-Volterra assertion. -/
theorem stab_mass_optical_le (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        (supDist T S₁.mu S₂.mu).toReal ≤
          C * ((geomDist T S₁ S₂).toReal + ε * (jDist T S₁ S₂).toReal) := by
  refine ⟨min (1 / 12) (1 / (524288 * A)), 40 + 303104 * A + 262144,
    lt_min (by norm_num) (one_div_pos.mpr (by positivity)), by positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall
  have hσ : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hεsq : ε ^ 2 ≤ min (1 / 12) (1 / (524288 * A)) :=
    (le_add_of_nonneg_right hσ).trans hsmall
  have hε12 : ε ^ 2 ≤ 1 / 12 := hεsq.trans (min_le_left _ _)
  have hcoeff : 524288 * A * ε ^ 2 ≤ 1 := by
    have hc := (le_div_iff₀ (show 0 < 524288 * A by positivity)).mp
      (hεsq.trans (min_le_right _ _))
    nlinarith only [hc]
  have hraw := stab_out_mass_feedback_before_absorption hA h₁s h₂s
    (by linarith only [hε12])
  have hbound := stab_mass_le_of_feedback hA ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    (by linarith only [hε12]) hcoeff hraw
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hG : 0 ≤ (geomDist T S₁ S₂).toReal := ENNReal.toReal_nonneg
  have heJ : 0 ≤ ε * (jDist T S₁ S₂).toReal := mul_nonneg hε0 ENNReal.toReal_nonneg
  have hcross := mul_nonneg (show 0 ≤ 40 + 303104 * A by positivity) heJ
  nlinarith only [hbound, hG, hcross]

end EmcsfAcExtension.Local
