module

public import Mathlib
public import EmcsfAcExtension.Local.Defs.Renormalized
public import EmcsfAcExtension.Frozen.JOut

/-! # Root A Renormalized

Literal objects from internal project record, adopted by internal project record.
Source: `source/charged_SF_new_version.tex`; individual declarations give line references.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global

/-- [def-node sec:charged-step7#exterior-interaction-variable]
Normalized outgoing derivative, charged_SF_new_version.tex:L1427–L1435. -/
noncomputable def alphaPrime (S : Fields) (u v : ℝ) : ℂ :=
  deriv (S.a u) v / (S.lam u v : ℂ)

/-- [internal]
Weighted frozen renormalized derivative, charged_SF_new_version.tex:L3170–L3174. -/
noncomputable def weightedJ (S : Fields) (u v : ℝ) : ℂ :=
  (S.lam u v / (1 - S.mu u v) : ℝ) * jOut S u v

/-- [internal]
Weighted covariant transport source, charged_SF_new_version.tex:L3170–L3183. -/
noncomputable def weightedJSource (e : ℝ) (S : Fields) (u v : ℝ) : ℂ :=
  S.nu u v * S.lam u v * S.theta u v / ((1 - S.mu u v) * S.r u v ^ 2) *
    (Local.curv S u v + 2 * starRingEnd ℂ (Local.curv S u v)) +
  ((S.lam u v / (1 - S.mu u v) : ℝ) : ℂ) * Local.emSourceJ e S u v

/-- [internal]
Derivative-free density forcing, charged_SF_new_version.tex:L1260–L1272. -/
noncomputable def rawDensitySource (e : ℝ) (S : Fields) (u v : ℝ) : ℂ :=
  let y := S.theta u v / (S.lam u v : ℂ)
  let q : ℝ := S.Q u v ^ 2 / S.r u v ^ 2
  let B : ℝ := S.lam u v * (-S.nu u v) / ((1 - S.mu u v) * S.r u v ^ 2)
  B * (((1 - q) * ‖y‖ ^ 2 - 3 * S.mu u v + 5 * q +
    2 * e * S.Q u v * (starRingEnd ℂ (S.phi u v) * y).im : ℝ) * y) +
  I * e * B * (3 * S.Q u v * y + S.Q u v * S.phi u v * (1 + ‖y‖ ^ 2) -
    e * S.r u v ^ 2 * S.phi u v * (starRingEnd ℂ (S.phi u v) * y).im)

/-- [internal]
Fixed-initial density representative, charged_SF_new_version.tex:L1410–L1412. -/
noncomputable def densityRepresentative (e : ℝ) (S : Fields) (u₀ u v : ℝ) : ℂ :=
  (S.lam u₀ v / S.lam u v : ℝ) *
    Complex.exp (-I * e * ∫ s in u₀..u, S.A s v) * deriv (S.a u₀) v +
  ∫ s in u₀..u, (S.lam s v / S.lam u v : ℝ) *
    Complex.exp (-I * e * ∫ t in s..u, S.A t v) * rawDensitySource e S s v

/-- Unfold `densityRepresentative` to the source formula above. -/
theorem densityRepresentative_def (e : ℝ) (S : Fields) (u₀ u v : ℝ) :
    densityRepresentative e S u₀ u v =
  (S.lam u₀ v / S.lam u v : ℝ) *
    Complex.exp (-I * e * ∫ s in u₀..u, S.A s v) * deriv (S.a u₀) v +
  ∫ s in u₀..u, (S.lam s v / S.lam u v : ℝ) *
    Complex.exp (-I * e * ∫ t in s..u, S.A t v) * rawDensitySource e S s v := rfl

/-- [internal]
Unitary weighted-derivative representative, charged_SF_new_version.tex:L3838–L3881. -/
noncomputable def weightedJRepresentative (e : ℝ) (S : Fields) (u₀ u v : ℝ) : ℂ :=
  Complex.exp (-I * e * ∫ s in u₀..u, S.A s v) * weightedJ S u₀ v +
  ∫ s in u₀..u, Complex.exp (-I * e * ∫ t in s..u, S.A t v) *
    weightedJSource e S s v

end EmcsfAcExtension.Global
