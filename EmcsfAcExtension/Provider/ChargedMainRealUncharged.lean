module

public import Mathlib
public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Frozen.OrigDomain
public import EmcsfAcExtension.Frozen.Triangle
public import EmcsfAcExtension.Frozen.Fields.EqOn
public import EmcsfAcExtension.Frozen.SignedExpIntegrand
public import EmcsfAcExtension.Frozen.Fields.NormalizedOut
public import EmcsfAcExtension.Frozen.Fields.Mu
import EmcsfAcExtension.Global.Real.Assembly

/-! # Provider for the frozen anchor `EmcsfAcExtension.charged_main_real_uncharged`

The registered provider module of `EmcsfAcExtension/Frozen/ChargedMainRealUncharged.lean`
(`FROZEN_MANIFEST.json`). While the anchor is `DRAFT_SORRY` this module is quarantined: only
the frozen anchor may import it, and it must never import the anchor. It will export the proof
of the exact frozen statement. -/

public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Provider

/-- The exact frozen real uncharged continuation statement, proved by the joint
restart and gluing construction with scalar reality and vanishing Maxwell fields
on the whole union (internal project record R5–R6 and Assembly). -/
theorem chargedMainRealUncharged (ui : ℝ) (hui : ui < 0) (S : Fields)
    (hS : IsSolution 0 S (origDomain ui))
    (hgauge : ∀ t, ui ≤ t → t < 0 → S.A t t = 0)
    (hmu : ∀ p ∈ origDomain ui, 0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1)
    (hr : ∀ v ∈ Icc ui 0, S.r ui v = (v - ui) / 2)
    (hdata : AbsolutelyContinuousOnInterval (S.a ui) ui 0)
    (hreal : ∀ p ∈ origDomain ui, (S.phi p.1 p.2).im = 0)
    (hterm : BddAbove ((fun u => ∫ s in ui..u, signedExpIntegrand S s 0) '' Ioo ui 0)) :
    ∃ us vp : ℝ, ∃ S' : Fields, ui < us ∧ us < 0 ∧ 0 < vp ∧
      IsSolution 0 S' (origDomain ui ∪ triangle us vp) ∧
      (∀ t ∈ Icc us vp, S'.A t t = 0) ∧ S'.EqOn S (origDomain ui) ∧
      ∀ p ∈ origDomain ui ∪ triangle us vp,
        (S'.phi p.1 p.2).im = 0 ∧ (S'.theta p.1 p.2).im = 0 ∧ (S'.xi p.1 p.2).im = 0 ∧
        S'.Q p.1 p.2 = 0 ∧ S'.A p.1 p.2 = 0 := by
  let hold : Global.OriginalData ui 0 S := ⟨hui, hS, hgauge, hmu, hr, hdata⟩
  exact Global.Real.real_uncharged_continuation ui S hold hreal hterm

end EmcsfAcExtension.Provider
