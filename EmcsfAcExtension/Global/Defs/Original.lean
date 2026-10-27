module

public import Mathlib
public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Frozen.OrigDomain
public import EmcsfAcExtension.Frozen.SignedExpIntegrand
public import EmcsfAcExtension.Frozen.PositiveExpIntegrand

/-! # Root A Original

Literal objects from internal project record, adopted by internal project record.
Source: `source/charged_SF_new_version.tex`; individual declarations give line references.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global

/-- [def-node thm:charged-main#local-solution-class]
Original-development premises, charged_SF_new_version.tex:L124–L182. -/
structure OriginalData (ui e : ℝ) (S : Fields) : Prop where
  /-- Strictly negative initial label. -/
  ui_neg : ui < 0
  /-- Frozen AC/BV solution on the original development. -/
  solution : IsSolution e S (origDomain ui)
  /-- Vanishing axis potential. -/
  gauge : ∀ t, ui ≤ t → t < 0 → S.A t t = 0
  /-- Nonnegative mass ratio strictly below one. -/
  mu : ∀ p ∈ origDomain ui, 0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1
  /-- Initial outgoing radius normalization. -/
  radius : ∀ v ∈ Icc ui 0, S.r ui v = (v - ui) / 2
  /-- Absolutely continuous initial normalized scalar. -/
  datumAC : AbsolutelyContinuousOnInterval (S.a ui) ui 0

/-- [internal]
Bounded signed terminal exponent, charged_SF_new_version.tex:L179–L182. -/
def SignedTerminalBound (ui : ℝ) (S : Fields) : Prop :=
  BddAbove ((fun u => ∫ s in ui..u, signedExpIntegrand S s 0) '' Ioo ui 0)

/-- [internal]
Finite positive terminal exponent, charged_SF_new_version.tex:L204–L206. -/
def PositiveTerminalFinite (ui : ℝ) (S : Fields) : Prop :=
  ∫⁻ u in Ico ui 0, ENNReal.ofReal (positiveExpIntegrand S u 0) < ⊤

/-- [internal]
Charge correction to the exponent, charged_SF_new_version.tex:L1016–L1025. -/
noncomputable def chargeCorrection (S : Fields) (u v : ℝ) : ℝ :=
  -S.nu u v * S.Q u v ^ 2 / ((1 - S.mu u v) * S.r u v ^ 3)

/-- [internal]
Terminal radius in the original label, charged_SF_new_version.tex:L931–L937. -/
noncomputable def terminalRadius (S : Fields) (u : ℝ) : ℝ := S.r u 0

/-- Unfold `terminalRadius` to the source formula above. -/
theorem terminalRadius_def (S : Fields) (u : ℝ) :
    terminalRadius S u = S.r u 0 := rfl

/-- [internal]
Terminal mass in the original label, charged_SF_new_version.tex:L1767–L1772. -/
noncomputable def terminalMass (S : Fields) (u : ℝ) : ℝ := S.m u 0

/-- Unfold `terminalMass` to the source formula above. -/
theorem terminalMass_def (S : Fields) (u : ℝ) :
    terminalMass S u = S.m u 0 := rfl

end EmcsfAcExtension.Global
