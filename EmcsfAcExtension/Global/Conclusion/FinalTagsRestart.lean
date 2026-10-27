module

public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Relabel
public import EmcsfAcExtension.Global.Restart.Prolongation
public import EmcsfAcExtension.Frozen.Fields.EqOn
public import EmcsfAcExtension.Frozen.Triangle
public import EmcsfAcExtension.Local.Defs.Params
import EmcsfAcExtension.Global.Closure.Final
import EmcsfAcExtension.Global.Closure.WireRestart
import EmcsfAcExtension.Global.Closure.WireContinuation

/-! # Unconditional restart and continuation node exports

The proved shrinking construction discharges the sole remaining premise of
the internal project record interfaces. The sealed local theorem is used through those
interfaces, under internal project record. Source: `charged_SF_new_version.tex:L4166–L4190`.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Global.Closure

/-- [node sec:charged-closure#local-restart]
Construct the regular-center AC solution on the entire enlarged closed
triangle, with axis gauge and equality on every proper common triangle.
The cone and both local thresholds are discharged from the original data.
Source: `charged_SF_new_version.tex:L4168–L4187`. -/
theorem local_restart (ui e : ℝ) (S : Fields) (hold : OriginalData ui e S)
    (hs : SignedTerminalBound ui S) :
    ∃ us ∈ Ioo ui 0, ∃ F : ℝ ≃o ℝ, IsNullRelabel F ∧ F us = 0 ∧ 0 < F 0 ∧
      (∀ t ∈ Ici 0, F t = selectedRelabel S us 0 + 2 * S.lam us 0 * t) ∧
      ∃ N : Fields, IsSolution e N (triangle 0 (2 * F 0)) ∧
        (∀ t ∈ Icc 0 (2 * F 0), N.A t t = 0) ∧
        (∀ T' ∈ Ioo 0 (F 0),
          (nullPullback S F.symm F.symm).EqOn N (triangle 0 T')) :=
  local_restart_of_closure closure_obligations ui e S hold hs

/-- [node sec:charged-closure#overlap-uniqueness]
The same restart agrees on every proper common triangle and, after
pullback, at every old overlap point including the old last cone. Its
solution class and axis gauge are derived with the witness. Uniqueness is
never applied at the missing endpoint. Source: `charged_SF_new_version.tex:L4181–L4205`. -/
theorem overlap_uniqueness (ui e : ℝ) (S : Fields) (hold : OriginalData ui e S)
    (hs : SignedTerminalBound ui S) :
    ∃ us ∈ Ioo ui 0, ∃ F : ℝ ≃o ℝ, IsNullRelabel F ∧ F us = 0 ∧ 0 < F 0 ∧
      (∀ t ∈ Ici 0, F t = selectedRelabel S us 0 + 2 * S.lam us 0 * t) ∧
      ∃ vp > 0, ∃ N : Fields, IsSolution e N (triangle 0 (2 * F 0)) ∧
        (∀ t ∈ Icc 0 (2 * F 0), N.A t t = 0) ∧
        (∀ T' ∈ Ioo 0 (F 0),
          (nullPullback S F.symm F.symm).EqOn N (triangle 0 T')) ∧
        IsSolution e (nullPullback N F F) (triangle us vp) ∧
        (∀ t ∈ Icc us vp, (nullPullback N F F).A t t = 0) ∧
        (nullPullback N F F).EqOn S (origDomain ui ∩ triangle us vp) :=
  overlap_uniqueness_of_closure closure_obligations ui e S hold hs

/-- [node sec:charged-closure#regular-center-continuation]
Continue through the missing endpoint on the exact frozen union, in the
regular-axis gauge, preserving all nine fields at every old point. Only
the original data and signed terminal bound are premises.
Source: `charged_SF_new_version.tex:L4189–L4190`. -/
theorem regular_center_continuation (ui e : ℝ) (S : Fields)
    (hold : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    ∃ us vp : ℝ, ∃ S' : Fields, ui < us ∧ us < 0 ∧ 0 < vp ∧
      IsSolution e S' (origDomain ui ∪ triangle us vp) ∧
      (∀ t ∈ Icc us vp, S'.A t t = 0) ∧ S'.EqOn S (origDomain ui) :=
  regular_center_continuation_of_closure closure_obligations ui e S hold hs

end EmcsfAcExtension.Global.Closure
