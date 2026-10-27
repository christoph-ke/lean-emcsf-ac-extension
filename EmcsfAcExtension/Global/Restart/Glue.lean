module

public import EmcsfAcExtension.Global.Defs.LocalStatement
public import EmcsfAcExtension.Global.Defs.Original
import EmcsfAcExtension.Global.Restart.LocalApplication
import EmcsfAcExtension.Global.Restart.Placement
import EmcsfAcExtension.Global.Restart.Overlap
import EmcsfAcExtension.Global.Restart.Pullback
import EmcsfAcExtension.Global.Glue.IsSolutionUnion
import EmcsfAcExtension.Local.Api.EqOn

/-! # Regular-center continuation on exactly the frozen union

internal project record supplies the explicit complete-cone conclusions. The exact local theorem
is applied once; proper-overlap uniqueness, endpoint continuity, canonical
pullback and the characteristic union construction then give the full frozen
continuation and its axis gauge. No theorem anchor or provider is imported.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.Closure

/-- [internal]
The full continuation, including the exact union domain, the unchanged gauge,
and equality of all nine primary fields at every old point
(`charged_SF_new_version.tex:L4189`–L4190; approved internal project record). The explicit cone
input is
internal project record's `Restart.complete_cone_smallness` conclusion, to be discharged
by internal project record in final assembly. The only local-theory input is its exact frozen
proposition. No additional smallness of coupling or original data is assumed. -/
theorem regular_center_continuation_of_cone (hlocal : LocalTheoremStatement)
    (ui e : ℝ) (S : Fields) (hold : OriginalData ui e S)
    (hcone : ∀ η : ℝ, 0 < η → ∃ us ∈ Ioo ui 0,
      AbsolutelyContinuousOnInterval (S.a us) us 0 ∧
      eVariationOn (S.a us) (Icc us 0) ≤ ENNReal.ofReal η ∧
      |e| * (2 * S.r us 0) *
        (1 + ‖S.phi us us‖ + 10 * (eVariationOn (S.a us) (Icc us 0)).toReal) ≤ η) :
    ∃ us vp : ℝ, ∃ S' : Fields, ui < us ∧ us < 0 ∧ 0 < vp ∧
      IsSolution e S' (origDomain ui ∪ triangle us vp) ∧
      (∀ t ∈ Icc us vp, S'.A t t = 0) ∧ S'.EqOn S (origDomain ui) := by
  obtain ⟨us, hus, F, hF, hz, hL, _hr, N, hN, hgN, heN⟩ :=
    Restart.local_restart_of_cone hlocal ui e S hold hcone
  obtain ⟨vp, hvp, hFvp⟩ := Restart.pullback_endpoint F hL
  have husvp : us < vp := hus.2.trans hvp
  obtain ⟨hP, hgP⟩ := Restart.pullback_restart hF hz hFvp husvp hN hgN
  have he := Restart.overlap_uniqueness_of_restart hvp hold.solution hF hz hL hP heN
  obtain ⟨G, hG, hGo, hGp⟩ := glue_original_triangle ui e us vp S
    (nullPullback N F F) hold.ui_neg hus hvp hold.solution hP he
  refine ⟨us, vp, G, hus.1, hus.2, hvp, hG, ?_, hGo⟩
  intro t ht
  rw [hGp.A (show (t, t) ∈ triangle us vp from ⟨ht.1, le_rfl, ht.2⟩)]
  exact hgP t ht

end EmcsfAcExtension.Global.Closure
