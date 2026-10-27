module

public import EmcsfAcExtension.Frozen.Triangle

/-! # Placement of the missing point inside the restarted axis

The proper old endpoint is `L`, and the enlarged axis ends at `2L`. An order
isomorphism supplies the canonical positive preimage of that new endpoint.
-/

public section

open Set

namespace EmcsfAcExtension.Global.Restart

/-- [node sec:charged-closure#missing-point-placement]
The image of the missing point is an axis point strictly before the new endpoint
(`charged_SF_new_version.tex:L4170`–L4172). No uniqueness statement at that point is used. -/
theorem missing_point_placement {L : ℝ} (hL : 0 < L) :
    (L, L) ∈ triangle 0 (2 * L) ∧ L < 2 * L := by
  exact ⟨⟨hL.le, le_rfl, by linarith only [hL]⟩, by linarith only [hL]⟩

/-- [internal] The canonical inverse places the new endpoint at a positive old label. -/
theorem pullback_endpoint (F : ℝ ≃o ℝ) (hL : 0 < F 0) :
    ∃ vp : ℝ, 0 < vp ∧ F vp = 2 * F 0 := by
  refine ⟨F.symm (2 * F 0), ?_, F.apply_symm_apply _⟩
  have h := F.symm.strictMono (missing_point_placement hL).2
  simpa only [F.symm_apply_apply] using h

end EmcsfAcExtension.Global.Restart
