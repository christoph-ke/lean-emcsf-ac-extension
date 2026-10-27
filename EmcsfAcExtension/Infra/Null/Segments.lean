/- Copyright (c) 2026. All rights reserved. -/

module

public import EmcsfAcExtension.Infra.Triangle
public import EmcsfAcExtension.Frozen.OrigDomain
public import EmcsfAcExtension.Frozen.OutSeg
public import EmcsfAcExtension.Frozen.InSeg

/-! # Frozen characteristic geometry

Membership, ordered characteristic segments, convexity, and density of the interior.
The original domain is half open; closedness and compactness are asserted for its
union with a triangle only when that triangle contains its missing vertex.
-/

public section

open Set

namespace EmcsfAcExtension

/-- Membership in the frozen closed triangle. -/
@[simp] theorem mem_triangle {a b : ℝ} {p : ℝ × ℝ} :
    p ∈ triangle a b ↔ a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := Iff.rfl

/-- Membership in the original half-open development. -/
@[simp] theorem mem_origDomain {ui : ℝ} {p : ℝ × ℝ} :
    p ∈ origDomain ui ↔ ui ≤ p.1 ∧ p.1 < 0 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 0 := Iff.rfl

/-- Membership in an outgoing segment. -/
@[simp] theorem mem_outSeg {u v₁ v₂ : ℝ} {p : ℝ × ℝ} :
    p ∈ outSeg u v₁ v₂ ↔ p.1 = u ∧ v₁ ≤ p.2 ∧ p.2 ≤ v₂ := Iff.rfl

/-- Membership in an incoming segment. -/
@[simp] theorem mem_inSeg {u₁ u₂ v : ℝ} {p : ℝ × ℝ} :
    p ∈ inSeg u₁ u₂ v ↔ u₁ ≤ p.1 ∧ p.1 ≤ u₂ ∧ p.2 = v := Iff.rfl

/-- Membership in the extended development. -/
@[simp] theorem mem_origDomain_union_triangle {ui us vp : ℝ} {p : ℝ × ℝ} :
    p ∈ origDomain ui ∪ triangle us vp ↔
      (ui ≤ p.1 ∧ p.1 < 0 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 0) ∨
      (us ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ vp) := Iff.rfl

/-- An ordered outgoing segment lies in the triangle precisely at these endpoints. -/
theorem outSeg_subset_triangle_iff {a b u v₁ v₂ : ℝ} (h : v₁ ≤ v₂) :
    outSeg u v₁ v₂ ⊆ triangle a b ↔ a ≤ u ∧ u ≤ v₁ ∧ v₂ ≤ b := by
  constructor
  · intro hs
    have hl := hs (show (u, v₁) ∈ outSeg u v₁ v₂ from ⟨rfl, le_rfl, h⟩)
    have hr := hs (show (u, v₂) ∈ outSeg u v₁ v₂ from ⟨rfl, h, le_rfl⟩)
    exact ⟨hl.1, hl.2.1, hr.2.2⟩
  · rintro ⟨hau, huv, hvb⟩ p ⟨hpu, hvl, hvr⟩
    exact ⟨hpu ▸ hau, hpu ▸ huv.trans hvl, hvr.trans hvb⟩

/-- An ordered incoming segment lies in the triangle precisely at these endpoints. -/
theorem inSeg_subset_triangle_iff {a b u₁ u₂ v : ℝ} (h : u₁ ≤ u₂) :
    inSeg u₁ u₂ v ⊆ triangle a b ↔ a ≤ u₁ ∧ u₂ ≤ v ∧ v ≤ b := by
  constructor
  · intro hs
    have hl := hs (show (u₁, v) ∈ inSeg u₁ u₂ v from ⟨le_rfl, h, rfl⟩)
    have hr := hs (show (u₂, v) ∈ inSeg u₁ u₂ v from ⟨h, le_rfl, rfl⟩)
    exact ⟨hl.1, hr.2.1, hr.2.2⟩
  · rintro ⟨hau, huv, hvb⟩ p ⟨hul, hur, hpv⟩
    exact ⟨hau.trans hul, hpv ▸ hur.trans huv, hpv ▸ hvb⟩

/-- Endpoint criterion for an outgoing segment in the original domain. -/
theorem outSeg_subset_origDomain_iff {ui u v₁ v₂ : ℝ} (h : v₁ ≤ v₂) :
    outSeg u v₁ v₂ ⊆ origDomain ui ↔ ui ≤ u ∧ u < 0 ∧ u ≤ v₁ ∧ v₂ ≤ 0 := by
  constructor
  · intro hs
    have hl := hs (show (u, v₁) ∈ outSeg u v₁ v₂ from ⟨rfl, le_rfl, h⟩)
    have hr := hs (show (u, v₂) ∈ outSeg u v₁ v₂ from ⟨rfl, h, le_rfl⟩)
    exact ⟨hl.1, hl.2.1, hl.2.2.1, hr.2.2.2⟩
  · rintro ⟨hau, hu0, huv, hv0⟩ p ⟨rfl, hvl, hvr⟩
    exact ⟨hau, hu0, huv.trans hvl, hvr.trans hv0⟩

/-- Endpoint criterion for an incoming segment in the original domain. -/
theorem inSeg_subset_origDomain_iff {ui u₁ u₂ v : ℝ} (h : u₁ ≤ u₂) :
    inSeg u₁ u₂ v ⊆ origDomain ui ↔ ui ≤ u₁ ∧ u₂ < 0 ∧ u₂ ≤ v ∧ v ≤ 0 := by
  constructor
  · intro hs
    have hl := hs (show (u₁, v) ∈ inSeg u₁ u₂ v from ⟨le_rfl, h, rfl⟩)
    have hr := hs (show (u₂, v) ∈ inSeg u₁ u₂ v from ⟨h, le_rfl, rfl⟩)
    exact ⟨hl.1, hr.2.1, hr.2.2.1, hr.2.2.2⟩
  · rintro ⟨hau, hu0, huv, hv0⟩ p ⟨hul, hur, rfl⟩
    exact ⟨hau.trans hul, hur.trans_lt hu0, hur.trans huv, hv0⟩

/-- Incoming segments are products of a closed interval and a singleton. -/
theorem inSeg_eq_prod (u₁ u₂ v : ℝ) :
    inSeg u₁ u₂ v = Icc u₁ u₂ ×ˢ {v} := by
  ext p
  exact and_assoc.symm

/-- Outgoing characteristic segments are compact, including empty segments. -/
theorem isCompact_outSeg (u v₁ v₂ : ℝ) : IsCompact (outSeg u v₁ v₂) :=
  isCompact_singleton.prod isCompact_Icc

/-- Incoming characteristic segments are compact, including empty segments. -/
theorem isCompact_inSeg (u₁ u₂ v : ℝ) : IsCompact (inSeg u₁ u₂ v) := by
  rw [inSeg_eq_prod]
  exact isCompact_Icc.prod isCompact_singleton

/-- The triangle is convex. -/
theorem convex_triangle (a b : ℝ) : Convex ℝ (triangle a b) := by
  rintro x hx y hy c d hc hd hcd
  change a ≤ c * x.1 + d * y.1 ∧
    c * x.1 + d * y.1 ≤ c * x.2 + d * y.2 ∧ c * x.2 + d * y.2 ≤ b
  refine ⟨?_, add_le_add (mul_le_mul_of_nonneg_left hx.2.1 hc)
    (mul_le_mul_of_nonneg_left hy.2.1 hd), ?_⟩
  · calc
      a = c * a + d * a := by rw [← add_mul, hcd, one_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hx.1 hc)
        (mul_le_mul_of_nonneg_left hy.1 hd)
  · calc
      _ ≤ c * b + d * b := add_le_add (mul_le_mul_of_nonneg_left hx.2.2 hc)
        (mul_le_mul_of_nonneg_left hy.2.2 hd)
      _ = b := by rw [← add_mul, hcd, one_mul]

/-- Strictly ordered points lie in the interior of the triangle. -/
theorem mem_interior_triangle_of_lt {a b : ℝ} {p : ℝ × ℝ}
    (ha : a < p.1) (huv : p.1 < p.2) (hb : p.2 < b) :
    p ∈ interior (triangle a b) := by
  apply mem_interior.mpr
  refine ⟨{q : ℝ × ℝ | a < q.1 ∧ q.1 < q.2 ∧ q.2 < b}, ?_, ?_, ⟨ha, huv, hb⟩⟩
  · intro q hq
    exact ⟨hq.1.le, hq.2.1.le, hq.2.2.le⟩
  · exact (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_snd).inter
        (isOpen_lt continuous_snd continuous_const))

/-- A nondegenerate triangle is the closure of its interior. -/
theorem closure_interior_triangle {a b : ℝ} (hab : a < b) :
    closure (interior (triangle a b)) = triangle a b := by
  have hn : (interior (triangle a b)).Nonempty := by
    refine ⟨((2 * a + b) / 3, (a + 2 * b) / 3), ?_⟩
    apply mem_interior_triangle_of_lt <;> dsimp <;> linarith only [hab]
  rw [(convex_triangle a b).closure_interior_eq_closure_of_nonempty_interior hn,
    (isClosed_triangle a b).closure_eq]

end EmcsfAcExtension
