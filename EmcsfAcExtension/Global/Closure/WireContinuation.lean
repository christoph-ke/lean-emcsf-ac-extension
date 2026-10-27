module

public import EmcsfAcExtension.Global.Assembly.Inputs
public import EmcsfAcExtension.Frozen.Fields.EqOn
public import EmcsfAcExtension.Frozen.Triangle
import EmcsfAcExtension.Frozen.RestartChargedLocalBV
import EmcsfAcExtension.Global.Closure.WireRestart
import EmcsfAcExtension.Global.Restart.Glue

/-! # Regular-center continuation conditional only on closure

The complete-cone input is discharged from the shrinking construction;
the local input is the sealed theorem, under the post-seal internal project record exception.
Source: charged_SF_new_version.tex:L4189–4190; approved internal project record.
-/

public section

open Set

namespace EmcsfAcExtension.Global.Closure

/-- [internal]
Conditional export for `sec:charged-closure#regular-center-continuation`.
The exact frozen union, axis gauge and all-nine-field equality at every old
point follow from the source data and signed terminal bound. The sole
additional premise is `ClosureObligations`; neither a cone conclusion nor
the local theorem is an assumption. Source: charged_SF_new_version.tex:L4189–4190. -/
theorem regular_center_continuation_of_closure (h : ClosureObligations)
    (ui e : ℝ) (S : Fields) (hold : OriginalData ui e S)
    (hs : SignedTerminalBound ui S) :
    ∃ us vp : ℝ, ∃ S' : Fields, ui < us ∧ us < 0 ∧ 0 < vp ∧
      IsSolution e S' (origDomain ui ∪ triangle us vp) ∧
      (∀ t ∈ Icc us vp, S'.A t t = 0) ∧ S'.EqOn S (origDomain ui) :=
  regular_center_continuation_of_cone EmcsfAcExtension.restart_charged_local_BV
    ui e S hold (complete_cone_smallness_of_closure h ui e S hold hs)

end EmcsfAcExtension.Global.Closure
