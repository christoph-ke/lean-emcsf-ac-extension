module

public import EmcsfAcExtension.Global.Assembly.FinalOfClosure
import EmcsfAcExtension.Global.Closure.Final

/-! # Provider for the frozen charged-main anchor

The registered implementation module of `thm.charged_main.v1`
(`FROZEN_MANIFEST.json`). While the anchor is `DRAFT_SORRY` it stays quarantined: only the
frozen charged-main anchor may import it. `chargedMain` proves the exact frozen statement:
the local theory is the sealed Root B anchor, and the closure obligations are
`Global.closure_obligations`.
-/

public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Provider

/-- [internal]
The exact frozen charged-main conclusion with the explicit closure premise.
All local-theory inputs are discharged by the sealed Root B anchor. Closure
constants have exactly the scope recorded in `Global.ClosureObligations`.
-/
theorem chargedMain_of_closure (h : Global.ClosureObligations)
    (ui e : ℝ) (hui : ui < 0) (S : Fields)
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
  exact Global.charged_main_of_closure h ui e hui S hS hgauge hmu hr hdata

/-- The exact frozen statement of `EmcsfAcExtension.charged_main`
(charged_SF_new_version.tex:L170–199),
with no premise beyond its own source hypotheses. -/
theorem chargedMain (ui e : ℝ) (hui : ui < 0) (S : Fields)
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
      (⨆ v ∈ Ioo ui 0, ∫⁻ u in Ico ui v, ENNReal.ofReal (positiveExpIntegrand S u v)) < ⊤) :=
  chargedMain_of_closure Global.closure_obligations ui e hui S hS hgauge hmu hr hdata

end EmcsfAcExtension.Provider
