module

public import EmcsfAcExtension.Global.Assembly.Inputs
public import EmcsfAcExtension.Global.Defs.Relabel
public import EmcsfAcExtension.Global.Restart.Prolongation
public import EmcsfAcExtension.Frozen.Fields.EqOn
public import EmcsfAcExtension.Local.Defs.Params
import EmcsfAcExtension.Frozen.RestartChargedLocalBV
import EmcsfAcExtension.Global.Restart.ConeSmallness
import EmcsfAcExtension.Global.Restart.LocalApplication
import EmcsfAcExtension.Global.Restart.Overlap
import EmcsfAcExtension.Global.Restart.Placement
import EmcsfAcExtension.Global.Restart.Pullback
import EmcsfAcExtension.Global.Restart.Relabel
import EmcsfAcExtension.Global.Restart.Smallness

/-! # Restart and overlap with only the shrinking-construction obligation

The audited cone and threshold premises are discharged from `ClosureObligations`.
The local theorem is the sealed frozen export, as permitted by internal project record.
Source: charged_SF_new_version.tex:L4129–4205; approved internal project record.
These exports remain internal until the closure obligation is proved.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.Closure

/-- [internal]
The complete-cone input of the restart, derived from `ClosureObligations`.
The construction constants depend on the fixed development and precede the
requested tolerance; no local-theory constants or cone bounds are assumed.
Source: charged_SF_new_version.tex:L4129–4168. -/
theorem complete_cone_smallness_of_closure (h : ClosureObligations)
    (ui e : ℝ) (S : Fields) (hold : OriginalData ui e S)
    (hs : SignedTerminalBound ui S) :
    ∀ η : ℝ, 0 < η → ∃ us ∈ Ioo ui 0,
      AbsolutelyContinuousOnInterval (S.a us) us 0 ∧
      eVariationOn (S.a us) (Icc us 0) ≤ ENNReal.ofReal η ∧
      |e| * (2 * S.r us 0) *
        (1 + ‖S.phi us us‖ + 10 * (eVariationOn (S.a us) (Icc us 0)).toReal) ≤ η := by
  obtain ⟨c, F, A, hc, hF, hA, C, εmax, D, M, hC, hεmax, hD, hM, hpaths⟩ :=
    h ui e S hold hs
  exact Restart.complete_cone_smallness_of_closure c F A hc hF hA
    ui e S hold hs C εmax hC hεmax D M hD hM hpaths

/-- [internal]
Conditional export for `sec:charged-closure#local-restart`, including
uniqueness on every proper common triangle from the same local witness.
All universal local constants are fixed before selecting the cone.
Source: charged_SF_new_version.tex:L4168–4187; no extra smallness premise. -/
theorem local_restart_of_closure (h : ClosureObligations)
    (ui e : ℝ) (S : Fields) (hold : OriginalData ui e S)
    (hs : SignedTerminalBound ui S) :
    ∃ us ∈ Ioo ui 0, ∃ F : ℝ ≃o ℝ, IsNullRelabel F ∧ F us = 0 ∧ 0 < F 0 ∧
      (∀ t ∈ Ici 0, F t = selectedRelabel S us 0 + 2 * S.lam us 0 * t) ∧
      ∃ N : Fields, IsSolution e N (triangle 0 (2 * F 0)) ∧
        (∀ t ∈ Icc 0 (2 * F 0), N.A t t = 0) ∧
        (∀ T' ∈ Ioo 0 (F 0),
          (nullPullback S F.symm F.symm).EqOn N (triangle 0 T')) :=
  Restart.local_restart_of_cone EmcsfAcExtension.restart_charged_local_BV
    ui e S hold (complete_cone_smallness_of_closure h ui e S hold hs)

/-- [internal]
Conditional export for `sec:charged-closure#overlap-uniqueness`.
Both proper-triangle uniqueness and equality at every old overlap point,
including the old last cone, are derived. The pulled-back class and gauge
are supplied by the constructed witness, with no equality premise.
Source: charged_SF_new_version.tex:L4181–4205; the missing endpoint is never a competitor. -/
theorem overlap_uniqueness_of_closure (h : ClosureObligations)
    (ui e : ℝ) (S : Fields) (hold : OriginalData ui e S)
    (hs : SignedTerminalBound ui S) :
    ∃ us ∈ Ioo ui 0, ∃ F : ℝ ≃o ℝ, IsNullRelabel F ∧ F us = 0 ∧ 0 < F 0 ∧
      (∀ t ∈ Ici 0, F t = selectedRelabel S us 0 + 2 * S.lam us 0 * t) ∧
      ∃ vp > 0, ∃ N : Fields, IsSolution e N (triangle 0 (2 * F 0)) ∧
        (∀ t ∈ Icc 0 (2 * F 0), N.A t t = 0) ∧
        (∀ T' ∈ Ioo 0 (F 0),
          (nullPullback S F.symm F.symm).EqOn N (triangle 0 T')) ∧
        IsSolution e (nullPullback N F F) (triangle us vp) ∧
        (∀ t ∈ Icc us vp, (nullPullback N F F).A t t = 0) ∧
        (nullPullback N F F).EqOn S (origDomain ui ∩ triangle us vp) := by
  obtain ⟨us, hus, F, hF, hz, hL, hr, N, hN, hgN, heN⟩ :=
    local_restart_of_closure h ui e S hold hs
  obtain ⟨vp, hvp, hFvp⟩ := Restart.pullback_endpoint F hL
  obtain ⟨hP, hgP⟩ := Restart.pullback_restart hF hz hFvp (hus.2.trans hvp) hN hgN
  exact ⟨us, hus, F, hF, hz, hL, hr, vp, hvp, N, hN, hgN, heN, hP, hgP,
    Restart.overlap_uniqueness_of_restart hvp hold.solution hF hz hL hP heN⟩

end EmcsfAcExtension.Global.Closure
