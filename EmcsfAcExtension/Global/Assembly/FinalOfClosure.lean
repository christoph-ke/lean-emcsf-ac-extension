module

public import EmcsfAcExtension.Global.Assembly.Main
import EmcsfAcExtension.Frozen.RestartChargedLocalBV

/-! # Root A assembly from the sealed local theorem

internal project record permits this cross-provider edge after Root B sealing. The sealed
local theorem discharges the exact `LocalTheoremStatement` premise; only
`ClosureObligations` remains. Source: charged_SF_new_version.tex:L170–199, internal project record.
-/

public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global

/-- [internal]
The exact frozen charged-main conclusion, conditional only on the remaining
shrinking-construction obligations. The local theorem is supplied by the
sealed Root B anchor. Closure constants retain the per-development scope
and quantifier order of `ClosureObligations`. This helper does not seal Root A.
-/
theorem charged_main_of_closure (h : ClosureObligations) (ui e : ℝ) (hui : ui < 0) (S : Fields)
    (hS : IsSolution e S (origDomain ui))
    (hgauge : ∀ t, ui ≤ t → t < 0 → S.A t t = 0)
    (hmu : ∀ p ∈ origDomain ui, 0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1)
    (hr : ∀ v ∈ Icc ui 0, S.r ui v = (v - ui) / 2)
    (hdata : AbsolutelyContinuousOnInterval (S.a ui) ui 0) :
    (BddAbove ((fun u => ∫ s in ui..u, signedExpIntegrand S s 0) '' Ioo ui 0) ↔
      ∫⁻ u in Ico ui 0, ENNReal.ofReal (positiveExpIntegrand S u 0) < ⊤) ∧
    (BddAbove ((fun u => ∫ s in ui..u, signedExpIntegrand S s 0) '' Ioo ui 0) →
      (∃ us vp : ℝ, ∃ S' : Fields, ui < us ∧ us < 0 ∧ 0 < vp ∧
        IsSolution e S' (origDomain ui ∪ triangle us vp) ∧
        (∀ t ∈ Icc us vp, S'.A t t = 0) ∧ S'.EqOn S (origDomain ui)) ∧
      eVariationOn (fun u => S.phi u 0) (Ico ui 0) < ⊤ ∧
      eVariationOn (fun u => S.b u 0) (Ico ui 0) < ⊤ ∧
      eVariationOn (fun u => Real.log (-S.nu u 0)) (Ico ui 0) < ⊤ ∧
      (⨆ v ∈ Ioo ui 0, ∫⁻ u in Ico ui v, ENNReal.ofReal (positiveExpIntegrand S u v)) < ⊤) := by
  exact charged_main_of_local_statement_of_closure restart_charged_local_BV h
    ui e hui S hS hgauge hmu hr hdata

end EmcsfAcExtension.Global
