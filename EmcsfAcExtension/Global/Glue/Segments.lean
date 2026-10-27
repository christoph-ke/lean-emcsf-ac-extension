/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Infra.Null.Segments

/-! # Characteristic subdivision on the exact continuation domain

The old closed patch is `triangle ui 0 ∩ {p | p.1 ≤ us}`. It is a proper
subset of the original development when `us < 0`. Together with the new
triangle it covers precisely the required union. Every outgoing segment
stays in one patch. An incoming segment either stays in one patch or splits
at `us`, with both closed subsegments contained in the respective patches.
This is the geometry used in internal project record, regular-center-continuation.
-/

public section

namespace EmcsfAcExtension.Global

open Set

/-- The proper old patch is closed, so its intersection with any compact set is compact. -/
theorem isClosed_old_patch (ui us : ℝ) :
    IsClosed (triangle ui 0 ∩ {p : ℝ × ℝ | p.1 ≤ us}) :=
  (isClosed_triangle ui 0).inter (isClosed_le continuous_fst continuous_const)

/-- The closed old patch lies in the original half-open development. -/
theorem old_patch_subset_origDomain {ui us : ℝ} (hus : us < 0) :
    triangle ui 0 ∩ {p : ℝ × ℝ | p.1 ≤ us} ⊆ origDomain ui := by
  intro p hp
  exact ⟨hp.1.1, hp.2.trans_lt hus, hp.1.2.1, hp.1.2.2⟩

/-- These two closed patches cover the exact union, including its missing vertex. -/
theorem old_patch_union_triangle {ui us vp : ℝ} (hus : us < 0) (hvp : 0 ≤ vp) :
    (triangle ui 0 ∩ {p : ℝ × ℝ | p.1 ≤ us}) ∪ triangle us vp =
      origDomain ui ∪ triangle us vp := by
  apply Subset.antisymm
  · exact union_subset_union (old_patch_subset_origDomain hus) Subset.rfl
  · intro p hp
    rcases hp with hp | hp
    · by_cases hu : p.1 ≤ us
      · exact Or.inl ⟨⟨hp.1, hp.2.2.1, hp.2.2.2⟩, hu⟩
      · exact Or.inr ⟨(le_of_not_ge hu), hp.2.2.1, hp.2.2.2.trans hvp⟩
    · exact Or.inr hp

private theorem mem_new_patch {ui us vp : ℝ} (hvp : 0 ≤ vp) {p : ℝ × ℝ}
    (hp : p ∈ origDomain ui ∪ triangle us vp) (hu : us ≤ p.1) :
    p ∈ triangle us vp := by
  rcases hp with hp | hp
  · exact ⟨hu, hp.2.2.1, hp.2.2.2.trans hvp⟩
  · exact hp

private theorem mem_old_patch {ui us vp : ℝ} (hui : ui ≤ us) {p : ℝ × ℝ}
    (hp : p ∈ origDomain ui ∪ triangle us vp) (hu : p.1 ≤ us) (hv : p.2 ≤ 0) :
    p ∈ triangle ui 0 ∩ {q : ℝ × ℝ | q.1 ≤ us} := by
  rcases hp with hp | hp
  · exact ⟨⟨hp.1, hp.2.2.1, hv⟩, hu⟩
  · exact ⟨⟨hui.trans hp.1, hp.2.1, hv⟩, hu⟩

/-- Every outgoing segment in the exact union lies in one of its two closed patches.
No convexity of the full union is asserted. -/
theorem outSeg_subset_old_or_new {ui us vp u a b : ℝ} (hvp : 0 ≤ vp)
    (hs : outSeg u a b ⊆ origDomain ui ∪ triangle us vp) :
    outSeg u a b ⊆ triangle ui 0 ∩ {p : ℝ × ℝ | p.1 ≤ us} ∨
      outSeg u a b ⊆ triangle us vp := by
  by_cases hu : u < us
  · left
    intro p hp
    have h := hs hp
    rcases h with h | h
    · refine ⟨⟨h.1, h.2.2.1, h.2.2.2⟩, ?_⟩
      change p.1 ≤ us
      exact hp.1 ▸ hu.le
    · exact False.elim ((not_le_of_gt hu) (hp.1 ▸ h.1))
  · right
    intro p hp
    exact mem_new_patch hvp (hs hp) (hp.1 ▸ le_of_not_gt hu)

/-- Every ordered incoming segment either lies in one closed patch or splits once at
the characteristic seam. The split point belongs to both closed subsegments. -/
theorem inSeg_subset_old_or_new_or_split {ui us vp a b v : ℝ}
    (hui : ui ≤ us) (hvp : 0 ≤ vp) (hab : a ≤ b)
    (hs : inSeg a b v ⊆ origDomain ui ∪ triangle us vp) :
    inSeg a b v ⊆ triangle ui 0 ∩ {p : ℝ × ℝ | p.1 ≤ us} ∨
      inSeg a b v ⊆ triangle us vp ∨
      ∃ c, a ≤ c ∧ c ≤ b ∧
        inSeg a c v ⊆ triangle ui 0 ∩ {p : ℝ × ℝ | p.1 ≤ us} ∧
        inSeg c b v ⊆ triangle us vp := by
  by_cases ha : us ≤ a
  · exact Or.inr (Or.inl (fun p hp => mem_new_patch hvp (hs hp) (ha.trans hp.1)))
  have ha' : a < us := lt_of_not_ge ha
  have hv : v ≤ 0 := by
    rcases hs (show (a, v) ∈ inSeg a b v from ⟨le_rfl, hab, rfl⟩) with h | h
    · exact h.2.2.2
    · exact False.elim ((not_le_of_gt ha') h.1)
  by_cases hb : b ≤ us
  · exact Or.inl (fun p hp =>
      mem_old_patch hui (hs hp) (hp.2.1.trans hb) (hp.2.2 ▸ hv))
  · right; right
    have hb' : us ≤ b := (lt_of_not_ge hb).le
    refine ⟨us, ha'.le, hb', ?_, ?_⟩
    · intro p hp
      exact mem_old_patch hui (hs ⟨hp.1, hp.2.1.trans hb', hp.2.2⟩)
        hp.2.1 (hp.2.2 ▸ hv)
    · intro p hp
      exact mem_new_patch hvp (hs ⟨ha'.le.trans hp.1, hp.2.1, hp.2.2⟩) hp.1

/-- Smaller centered triangles are contained in larger ones. -/
theorem centered_triangle_mono {t δ ε : ℝ} (h : δ ≤ ε) :
    triangle (t - δ) (t + δ) ⊆ triangle (t - ε) (t + ε) := by
  intro p hp
  exact ⟨(sub_le_sub_left h t).trans hp.1, hp.2.1,
    hp.2.2.trans (add_le_add le_rfl h)⟩

end EmcsfAcExtension.Global
