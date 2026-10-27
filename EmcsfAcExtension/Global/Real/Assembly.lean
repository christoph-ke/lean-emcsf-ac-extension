module

public import EmcsfAcExtension.Global.Real.ContinuationReality
import EmcsfAcExtension.Global.Closure.Final
import EmcsfAcExtension.Global.Closure.WireRestart
import EmcsfAcExtension.Frozen.RestartChargedLocalBV

/-! # Assembly of the real uncharged continuation

internal project record Assembly uses the complete-cone smallness of the unconditional closure
construction and the sealed local theorem. The reality argument retains the
restart witness and glued continuation from one joint construction throughout.
-/

public section

open Set

namespace EmcsfAcExtension.Global.Real

/-- [internal]
The real uncharged continuation follows from the signed terminal bound with
no additional cone, closure or local-theory premise (internal project record Assembly).
The cone construction is the same one used by `charged_main`, sourced at
`charged_SF_new_version.tex:L4129`–L4210; scalar reality follows internal project record R2–R6. -/
theorem real_uncharged_continuation (ui : ℝ) (S : Fields)
    (hold : OriginalData ui 0 S)
    (hreal : ∀ p ∈ origDomain ui, (S.phi p.1 p.2).im = 0)
    (hterm : SignedTerminalBound ui S) :
    ∃ us vp : ℝ, ∃ S' : Fields, ui < us ∧ us < 0 ∧ 0 < vp ∧
      IsSolution 0 S' (origDomain ui ∪ triangle us vp) ∧
      (∀ t ∈ Icc us vp, S'.A t t = 0) ∧ S'.EqOn S (origDomain ui) ∧
      ∀ p ∈ origDomain ui ∪ triangle us vp,
        (S'.phi p.1 p.2).im = 0 ∧ (S'.theta p.1 p.2).im = 0 ∧
        (S'.xi p.1 p.2).im = 0 ∧ S'.Q p.1 p.2 = 0 ∧ S'.A p.1 p.2 = 0 := by
  have hcone := Closure.complete_cone_smallness_of_closure closure_obligations
    ui 0 S hold hterm
  exact real_continuation_of_cone EmcsfAcExtension.restart_charged_local_BV
    ui S hold hcone hreal

end EmcsfAcExtension.Global.Real
