module

public import EmcsfAcExtension.Local.Broad.RectangleState
public import EmcsfAcExtension.Local.Broad.Setup

/-! # Equality at a limiting characteristic apex

Clamping both coordinates to an earlier apex gives continuous points
inside earlier triangles, including when the limit point is on the axis.
-/

public section

open Set

namespace EmcsfAcExtension.Local

open Broad

/-- Equality on every earlier closed subtriangle extends to the limiting
closed triangle by continuity. This includes its entire top edge and apex.
The domain is a fixed complete characteristic triangle. -/
theorem triangle_equality_at_limit_of_below {e a b q : ℝ} {S₁ S₂ : Fields}
    (haq : a < q) (hqb : q ≤ b)
    (hS₁ : IsSolution e S₁ (triangle a b)) (hS₂ : IsSolution e S₂ (triangle a b))
    (heq : ∀ t ∈ Ico a q, S₁.EqOn S₂ (triangle a t)) :
    S₁.EqOn S₂ (triangle a q) := by
  intro p hp
  let f := fun t : ℝ => (min p.1 t, min p.2 t)
  have cf : Continuous f := (continuous_const.min continuous_id).prodMk
    (continuous_const.min continuous_id)
  have hmap : MapsTo f (Icc a q) (triangle a b) := by
    intro t ht
    exact ⟨le_min hp.1 ht.1, min_le_min hp.2.1 le_rfl, (min_le_right _ _).trans (ht.2.trans hqb)⟩
  have c₁ := (continuousOn_rectangle_state hS₁).comp cf.continuousOn hmap
  have c₂ := (continuousOn_rectangle_state hS₂).comp cf.continuousOn hmap
  have hclosed := isClosed_Icc.isClosed_eq c₁ c₂
  have hsub : Ico a q ⊆ {t ∈ Icc a q | rectangle_state S₁ (f t) = rectangle_state S₂ (f t)} := by
    intro t ht
    refine ⟨⟨ht.1, ht.2.le⟩, ?_⟩
    apply (rectangle_state_eq_iff S₁ S₂ (f t)).mpr
    exact heq t ht (f t) ⟨le_min hp.1 ht.1, min_le_min hp.2.1 le_rfl, min_le_right _ _⟩
  have hqmem : q ∈ closure (Ico a q) := by
    rw [closure_Ico haq.ne]
    exact ⟨haq.le, le_rfl⟩
  have hstate := ((closure_minimal hsub hclosed) hqmem).2
  have huq := hp.2.1.trans hp.2.2
  simpa only [f, min_eq_left huq, min_eq_left hp.2.2, Function.comp_apply] using
    (rectangle_state_eq_iff S₁ S₂ (f q)).mp hstate

end EmcsfAcExtension.Local
