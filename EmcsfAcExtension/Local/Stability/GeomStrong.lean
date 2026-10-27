module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeomStrongSource

/-! # The common geometric source comparison

This is the canonical graph-node interface for G1. Its smooth source
comparison retains every approved small parameter in the estimate.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [node restart-sec-bv-stability-independent#geometric-source-difference]
The common geometric source satisfies G1, charged_SF_new_version.tex:L5414–5424,
with the repaired primitive subtraction in approved internal project record A1–A12.
The positive threshold and constant depend only on `A` and the fixed
box, before all fields, coupling, background, time and data, uniformly
in minimum radii and initial derivative suprema. All `ε,σ` factors
in the approved source comparison are retained. -/
theorem Stab.geometric_source_difference (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        (∫⁻ p in triangle 0 T, ‖geomSource S₁ p.1 p.2 - geomSource S₂ p.1 p.2‖ₑ) ≤
          ENNReal.ofReal (C * ε * ((jDist T S₁ S₂).toReal + (kDist e T S₁ S₂).toReal) +
            C * ε ^ 2 * (geomDist T S₁ S₂).toReal + C * sigma e M T *
              (dataDist h₁ h₂ T + (jDist T S₁ S₂).toReal + (kDist e T S₁ S₂).toReal +
                ε * (geomDist T S₁ S₂).toReal)) := by
  exact stab_geometric_source_difference A hA

end EmcsfAcExtension.Local
