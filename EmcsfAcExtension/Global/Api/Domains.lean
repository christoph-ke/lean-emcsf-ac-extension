/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Infra.Null.Segments

/-! # Proper sections of the original and extended developments

The frozen original domain omits precisely the terminal vertex. All segment
criteria, compactness and measurability results from `Infra.Null.Segments`
remain available through this import. No new domain object is introduced.
-/

public section

open Set

namespace EmcsfAcExtension.Global

/-- [internal] An existing original-axis point has a strictly negative label. -/
@[simp] theorem axis_mem_origDomain {ui t : ℝ} :
    (t, t) ∈ origDomain ui ↔ ui ≤ t ∧ t < 0 := by
  constructor
  · exact fun h => ⟨h.1, h.2.1⟩
  · exact fun h => ⟨h.1, h.2, le_rfl, h.2.le⟩

/-- [internal] The missing terminal vertex is never in the original domain. -/
@[simp] theorem terminal_vertex_not_mem_origDomain (ui : ℝ) :
    (0, 0) ∉ origDomain ui := by simp

/-- [internal] A triangle ending strictly before zero lies in the original domain. -/
theorem triangle_subset_origDomain {ui a b : ℝ} (hia : ui ≤ a) (hb : b < 0) :
    triangle a b ⊆ origDomain ui := by
  intro p hp
  exact ⟨hia.trans hp.1, (hp.2.1.trans hp.2.2).trans_lt hb, hp.2.1,
    hp.2.2.trans hb.le⟩

/-- [internal] Restrict an outgoing segment by moving both endpoints inward. -/
theorem outSeg_subset_outSeg {u a b c d : ℝ} (hac : a ≤ c) (hdb : d ≤ b) :
    outSeg u c d ⊆ outSeg u a b :=
  fun _ hp => ⟨hp.1, hac.trans hp.2.1, hp.2.2.trans hdb⟩

/-- [internal] Restrict an incoming segment by moving both endpoints inward. -/
theorem inSeg_subset_inSeg {a b c d v : ℝ} (hac : a ≤ c) (hdb : d ≤ b) :
    inSeg c d v ⊆ inSeg a b v :=
  fun _ hp => ⟨hac.trans hp.1, hp.2.1.trans hdb, hp.2.2⟩

/-- [internal] A closed outgoing segment includes its axis endpoint only at a
proper negative original label. -/
theorem outSeg_axis_subset_origDomain_iff {ui u b : ℝ} (hub : u ≤ b) :
    outSeg u u b ⊆ origDomain ui ↔ ui ≤ u ∧ u < 0 ∧ b ≤ 0 := by
  rw [outSeg_subset_origDomain_iff hub]
  simp

end EmcsfAcExtension.Global
