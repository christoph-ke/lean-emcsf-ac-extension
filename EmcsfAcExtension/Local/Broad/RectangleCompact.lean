module

public import EmcsfAcExtension.Local.Broad.RectangleState

/-! # A compact convex container for a compact positive state range

Positive linear margins and a norm bound give a closed convex container.
This keeps every intermediate state away from all frozen source poles.
-/

public section

open Set

namespace EmcsfAcExtension.Local.Broad

/-- A compact state range in the positive region has a compact convex
container in that region. The container depends on the fixed range;
there is no uniform estimate constant or additional solution hypothesis. -/
theorem compact_convex_rectangle_state_container {L : Set RectangleState}
    (hL : IsCompact L) (hregion : L ⊆ rectangle_state_region) :
    ∃ K : Set RectangleState, IsCompact K ∧ Convex ℝ K ∧
      K ⊆ rectangle_state_region ∧ L ⊆ K := by
  let f := fun z : RectangleState => min z.2.1 (min z.1.1 (z.2.1 - 2 * z.2.2.2.1))
  have cf : Continuous f := by fun_prop
  obtain ⟨ρ, hρ, hρbound⟩ := hL.exists_forall_le' cf.continuousOn (fun z hz =>
    lt_min (hregion hz).1 (lt_min (hregion hz).2.1 (hregion hz).2.2))
  obtain ⟨B, hB⟩ := hL.bddAbove_image (continuous_id.norm.continuousOn)
  let H : Set RectangleState := {z | ρ ≤ z.2.1 ∧ ρ ≤ z.1.1 ∧ ρ ≤ z.2.1 - 2 * z.2.2.2.1}
  have hHclosed : IsClosed H := by
    have hr : IsClosed {z : RectangleState | ρ ≤ z.2.1} :=
      isClosed_le continuous_const (by fun_prop)
    have hl : IsClosed {z : RectangleState | ρ ≤ z.1.1} :=
      isClosed_le continuous_const (by fun_prop)
    have hg : IsClosed {z : RectangleState | ρ ≤ z.2.1 - 2 * z.2.2.2.1} :=
      isClosed_le continuous_const (by fun_prop)
    exact hr.inter (hl.inter hg)
  have hHconv : Convex ℝ H := by
    intro x hx y hy a b ha hb hab
    have hr := (convex_Ici ρ) hx.1 hy.1 ha hb hab
    have hl := (convex_Ici ρ) hx.2.1 hy.2.1 ha hb hab
    have hg := (convex_Ici ρ) hx.2.2 hy.2.2 ha hb hab
    change ρ ≤ a * x.2.1 + b * y.2.1 ∧ ρ ≤ a * x.1.1 + b * y.1.1 ∧
      ρ ≤ (a * x.2.1 + b * y.2.1) - 2 * (a * x.2.2.2.1 + b * y.2.2.2.1)
    refine ⟨hr, hl, ?_⟩
    change ρ ≤ a * (x.2.1 - 2 * x.2.2.2.1) + b * (y.2.1 - 2 * y.2.2.2.1) at hg
    convert hg using 1; ring
  refine ⟨Metric.closedBall 0 B ∩ H, (isCompact_closedBall _ _).inter_right hHclosed,
    (convex_closedBall (0 : RectangleState) B).inter hHconv, ?_, ?_⟩
  · intro z hz
    exact ⟨hρ.trans_le hz.2.1, hρ.trans_le hz.2.2.1, hρ.trans_le hz.2.2.2⟩
  · intro z hz
    have hh := hρbound z hz
    refine ⟨?_, hh.trans (min_le_left _ _),
      hh.trans ((min_le_right _ _).trans (min_le_left _ _)),
      hh.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hB (mem_image_of_mem _ hz)

end EmcsfAcExtension.Local.Broad
