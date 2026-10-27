module

public import Mathlib
public import EmcsfAcExtension.Global.Defs.Renormalized

/-! # Root A Interaction

Literal objects from internal project record, adopted by internal project record.
Source: `source/charged_SF_new_version.tex`; individual declarations give line references.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global

/-- [internal]
Initial interaction integral, charged_SF_new_version.tex:L3872–L3877. -/
noncomputable def initialInteraction (S : Fields) (u₀ v₀ : ℝ) : ℝ≥0∞ :=
  ∫⁻ v in Icc v₀ 0, ‖weightedJ S u₀ v‖ₑ

/-- [internal]
Additive incoming label envelope, charged_SF_new_version.tex:L3838–L3971. -/
noncomputable def incomingEnvelope (e : ℝ) (S : Fields) (D : Set (ℝ × ℝ))
    (u₀ v : ℝ) : ℝ≥0∞ :=
  ‖weightedJ S u₀ v‖ₑ + ∫⁻ u in {u | (u, v) ∈ D}, ‖weightedJSource e S u v‖ₑ

/-- [internal]
Label-first source interaction integral, charged_SF_new_version.tex:L3599–L3607 and L3874–L3876. -/
noncomputable def sourceInteraction (e : ℝ) (S : Fields) (D : Set (ℝ × ℝ))
    (v₀ : ℝ) : ℝ≥0∞ :=
  ∫⁻ v in Icc v₀ 0, ∫⁻ u in {u | (u, v) ∈ D}, ‖weightedJSource e S u v‖ₑ

/-- [internal]
Integrated incoming envelope, charged_SF_new_version.tex:L3935–L3936. -/
noncomputable def interactionNorm (e : ℝ) (S : Fields) (D : Set (ℝ × ℝ))
    (u₀ v₀ : ℝ) : ℝ≥0∞ :=
  ∫⁻ v in Icc v₀ 0, incomingEnvelope e S D u₀ v

/-- [internal]
Numeric exterior stopping parameters, charged_SF_new_version.tex:L3265–L3282 and L3847–L3860. -/
def ExteriorBox (δ c Λ F ε ρ : ℝ) : Prop :=
  0 < δ ∧ δ ≤ 1 ∧ 0 < c ∧ c ≤ Λ ∧ 0 ≤ F ∧ F < 1 ∧ 0 ≤ ε ∧
  max ε (1 / 2) < 1 - F ^ 2 ∧ 0 < ρ ∧ ρ < 1

/-- [internal]
Exterior field stops including relative charge, charged_SF_new_version.tex:L3936–L3945. -/
def ExteriorStops (S : Fields) (D : Set (ℝ × ℝ)) (δ c Λ F ε : ℝ) : Prop :=
  ∀ p ∈ D, 0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2 ∧
    c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ Λ ∧
    ‖S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ)‖ ≤ F ∧
    S.mu p.1 p.2 / (1 - S.mu p.1 p.2) ≤ ε ∧
    S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 ≤ S.mu p.1 p.2 / 2

end EmcsfAcExtension.Global
