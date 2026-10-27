/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Frozen.Triangle

/-! # Geometry and unique differentiation on characteristic domains

Infrastructure for internal project record. All ambient uniqueness statements use the
nondegeneracy hypotheses fixed in the packet. No graph node is closed here.
-/

public section

namespace EmcsfAcExtension

open Set

/-- The frozen closed triangle is convex. -/
theorem convex_triangle (a b : ℝ) : Convex ℝ (triangle a b) := by
  intro p hp q hq s t hs ht hst
  change a ≤ s * p.1 + t * q.1 ∧
    s * p.1 + t * q.1 ≤ s * p.2 + t * q.2 ∧ s * p.2 + t * q.2 ≤ b
  refine ⟨?_, add_le_add (mul_le_mul_of_nonneg_left hp.2.1 hs)
    (mul_le_mul_of_nonneg_left hq.2.1 ht), ?_⟩
  · calc
      a = s * a + t * a := by rw [← add_mul, hst, one_mul]
      _ ≤ s * p.1 + t * q.1 := add_le_add
        (mul_le_mul_of_nonneg_left hp.1 hs) (mul_le_mul_of_nonneg_left hq.1 ht)
  · calc
      s * p.2 + t * q.2 ≤ s * b + t * b := add_le_add
        (mul_le_mul_of_nonneg_left hp.2.2 hs) (mul_le_mul_of_nonneg_left hq.2.2 ht)
      _ = b := by rw [← add_mul, hst, one_mul]

/-- The frozen triangle is closed. -/
theorem isClosed_triangle (a b : ℝ) : IsClosed (triangle a b) :=
  (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_fst continuous_snd).inter
      (isClosed_le continuous_snd continuous_const))

/-- Strict triangle inequalities give an ambient interior point. -/
theorem mem_interior_triangle_of_lt {a b : ℝ} {p : ℝ × ℝ}
    (ha : a < p.1) (huv : p.1 < p.2) (hb : p.2 < b) :
    p ∈ interior (triangle a b) := by
  let U : Set (ℝ × ℝ) := {q | a < q.1 ∧ q.1 < q.2 ∧ q.2 < b}
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_fst continuous_snd).inter
      (isOpen_lt continuous_snd continuous_const))
  exact mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (hU.mem_nhds ⟨ha, huv, hb⟩)
      (fun _ h => ⟨h.1.le, h.2.1.le, h.2.2.le⟩))

/-- A nondegenerate triangle has nonempty ambient interior. -/
theorem interior_triangle_nonempty {a b : ℝ} (hab : a < b) :
    (interior (triangle a b)).Nonempty := by
  refine ⟨((2 * a + b) / 3, (a + 2 * b) / 3),
    mem_interior_triangle_of_lt ?_ ?_ ?_⟩ <;> dsimp <;> linarith

/-- Ambient derivatives are unique on a nondegenerate closed triangle. -/
theorem uniqueDiffOn_triangle {a b : ℝ} (hab : a < b) :
    UniqueDiffOn ℝ (triangle a b) :=
  uniqueDiffOn_convex (convex_triangle a b) (interior_triangle_nonempty hab)

/-- A nondegenerate triangle is the closure of its interior. -/
theorem closure_interior_triangle {a b : ℝ} (hab : a < b) :
    closure (interior (triangle a b)) = triangle a b := by
  rw [(convex_triangle a b).closure_interior_eq_closure_of_nonempty_interior
    (interior_triangle_nonempty hab), (isClosed_triangle a b).closure_eq]

/-- A closed triangle is compact. -/
theorem isCompact_triangle (a b : ℝ) : IsCompact (triangle a b) := by
  refine ((isCompact_Icc : IsCompact (Icc a b)).prod
    (isCompact_Icc : IsCompact (Icc a b))).of_isClosed_subset (isClosed_triangle a b) ?_
  intro p hp
  exact ⟨⟨hp.1, hp.2.1.trans hp.2.2⟩, ⟨hp.1.trans hp.2.1, hp.2.2⟩⟩

/-- Ambient derivatives are unique on a nondegenerate incoming trapezoid.
The cutoff satisfies `a < c ≤ b`, as fixed in internal project record. -/
theorem uniqueDiffOn_triangle_inter_fst_le {a b c : ℝ} (hac : a < c) (hcb : c ≤ b) :
    UniqueDiffOn ℝ (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) := by
  apply uniqueDiffOn_convex
  · apply (convex_triangle a b).inter
    intro p hp q hq s t hs ht hst
    change s * p.1 + t * q.1 ≤ c
    calc
      s * p.1 + t * q.1 ≤ s * c + t * c := add_le_add
        (mul_le_mul_of_nonneg_left hp hs) (mul_le_mul_of_nonneg_left hq ht)
      _ = c := by rw [← add_mul, hst, one_mul]
  · let U : Set (ℝ × ℝ) := {p | a < p.1 ∧ p.1 < p.2 ∧ p.2 < b ∧ p.1 < c}
    have hU : IsOpen U := (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_snd).inter
        ((isOpen_lt continuous_snd continuous_const).inter
          (isOpen_lt continuous_fst continuous_const)))
    refine ⟨((2 * a + c) / 3, (a + 2 * c) / 3),
      mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hU.mem_nhds ?_) ?_)⟩
    · change a < (2 * a + c) / 3 ∧ (2 * a + c) / 3 < (a + 2 * c) / 3 ∧
        (a + 2 * c) / 3 < b ∧ (2 * a + c) / 3 < c
      constructor
      · linarith
      constructor
      · linarith
      constructor <;> linarith
    · exact fun p hp => ⟨⟨hp.1.le, hp.2.1.le, hp.2.2.1.le⟩, hp.2.2.2.le⟩

/-- Ambient derivatives are unique on a closed rectangle with positive side lengths. -/
theorem uniqueDiffOn_rectangle {a₁ b₁ a₂ b₂ : ℝ} (h₁ : a₁ < b₁) (h₂ : a₂ < b₂) :
    UniqueDiffOn ℝ (Icc a₁ b₁ ×ˢ Icc a₂ b₂) :=
  (uniqueDiffOn_Icc h₁).prod (uniqueDiffOn_Icc h₂)

end EmcsfAcExtension
