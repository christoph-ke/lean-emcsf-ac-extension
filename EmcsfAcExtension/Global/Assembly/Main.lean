module

public import EmcsfAcExtension.Global.Assembly.Inputs
public import EmcsfAcExtension.Global.Defs.LocalStatement
public import EmcsfAcExtension.Frozen.Fields.EqOn
public import EmcsfAcExtension.Frozen.Triangle
import EmcsfAcExtension.Global.Restart.ConeSmallness
import EmcsfAcExtension.Global.Restart.Glue
import EmcsfAcExtension.Global.Terminal.Hypotheses
import EmcsfAcExtension.Global.Conclusion.TerminalTV
import EmcsfAcExtension.Global.Conclusion.PositiveExponent

/-! # Root A assembly against explicit closure obligations

Architecture §3.1, charged_SF_new_version.tex:L170–199. The conclusion is the frozen
charged-main statement, with the exact local theorem and the remaining
shrinking-construction obligations exposed as temporary internal premises.
The terminal equivalence is proved independently of those premises. One
continuation supplies every final TV and positive-exponent clause via internal project record;
the exponent clause uses the two-application variant
`Closure.uniform_positive_exponents_of_continuation` (late triangle and
proper earlier trapezoid). `charged_main_of_closure` discharges the local
premise by the sealed `restart_charged_local_BV`.
This conditional assembly does not seal either frozen anchor.
-/

public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global

/-- [internal]
The exact frozen conclusion of `thm:charged-main`, conditional on the local
theorem statement and the explicit upstream shrinking construction. The
closure constants may depend on the fixed development, but precede the
energy tolerance, entry row and stage family as recorded in
`ClosureObligations`; the continuation and all final estimates are derived,
not included in that proposition. Source: charged_SF_new_version.tex:L170–199,
internal project record and approved internal project record, using the adopted internal project
record route.
-/
theorem charged_main_of_local_statement_of_closure (hlocal : LocalTheoremStatement)
    (hclosure : ClosureObligations) (ui e : ℝ) (hui : ui < 0) (S : Fields)
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
  let h : OriginalData ui e S := ⟨hui, hS, hgauge, hmu, hr, hdata⟩
  refine ⟨(charged_terminal_equivalence ui e S h).1, ?_⟩
  intro hs
  obtain ⟨c, F, A, hc, hF, hA, C, εmax, D, M, hC, hεmax, hD, hM, hpaths⟩ :=
    hclosure ui e S h hs
  have hcone := Restart.complete_cone_smallness_of_closure c F A hc hF hA
    ui e S h hs C εmax hC hεmax D M hD hM hpaths
  have hcont := Closure.regular_center_continuation_of_cone hlocal ui e S h hcone
  obtain ⟨hphi, hb, hnu⟩ := Closure.terminal_variation_of_continuation ui e S hcont
  exact ⟨hcont, hphi, hb, hnu,
    Closure.uniform_positive_exponents_of_continuation ui e S hcont⟩

end EmcsfAcExtension.Global
