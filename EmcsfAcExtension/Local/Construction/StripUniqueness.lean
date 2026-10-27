module

public import EmcsfAcExtension.Local.Broad.Rectangle

/-! # Characteristic-block comparison for appended strips

The first-order Goursat system prescribes only `(λ,θ)` on the left
and `(r,ν,m,Q,A,φ,ξ)` on the lower side. The landed compact source
comparison applies to exactly these entering components, including a
collapsed incoming width used to identify the original entering cone.
-/

public section

open Set

namespace EmcsfAcExtension.Local

open Broad

/-- Broad uniqueness from the two prescribed entering blocks on a
positive-radius rectangle. The source Lipschitz constant follows the
compact solution ranges and precedes every section. No smallness,
C¹ regularity or positive incoming width is required. -/
theorem broad_rectangle_uniqueness_of_entering_blocks {e u₁ u₂ v₁ v₂ : ℝ} {S₁ S₂ : Fields}
    (h12 : u₁ ≤ u₂) (hv : v₁ ≤ v₂) (hpos : u₂ < v₁)
    (hS₁ : IsSolution e S₁ (Icc u₁ u₂ ×ˢ Icc v₁ v₂))
    (hS₂ : IsSolution e S₂ (Icc u₁ u₂ ×ˢ Icc v₁ v₂))
    (hYi : ∀ v ∈ Icc v₁ v₂,
      (rectangle_state S₁ (u₁, v)).1 = (rectangle_state S₂ (u₁, v)).1)
    (hXb : ∀ u ∈ Icc u₁ u₂,
      (rectangle_state S₁ (u, v₁)).2 = (rectangle_state S₂ (u, v₁)).2) :
    S₁.EqOn S₂ (Icc u₁ u₂ ×ˢ Icc v₁ v₂) := by
  let R := Icc u₁ u₂ ×ˢ Icc v₁ v₂
  have hR : IsCompact R := isCompact_Icc.prod isCompact_Icc
  let L := rectangle_state S₁ '' R ∪ rectangle_state S₂ '' R
  have hL : IsCompact L := (hR.image_of_continuousOn (continuousOn_rectangle_state hS₁)).union
    (hR.image_of_continuousOn (continuousOn_rectangle_state hS₂))
  have hregion : L ⊆ rectangle_state_region := by
    intro z hz
    rcases hz with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · exact rectangle_state_mem_region hS₁ hp (hp.1.2.trans_lt (hpos.trans_le hp.2.1))
    · exact rectangle_state_mem_region hS₂ hp (hp.1.2.trans_lt (hpos.trans_le hp.2.1))
  obtain ⟨K, hK, hconv, hKU, hLK⟩ := compact_convex_rectangle_state_container hL hregion
  obtain ⟨C, _hC, hCi, hCo⟩ := rectangle_sources_lipschitz e hK hconv hKU
  have hm₁ p (hp : p ∈ R) : rectangle_state S₁ p ∈ K := hLK (Or.inl ⟨p, hp, rfl⟩)
  have hm₂ p (hp : p ∈ R) : rectangle_state S₂ p ∈ K := hLK (Or.inr ⟨p, hp, rfl⟩)
  have hi₁ := fun (u : ℝ) (hu : u ∈ Icc u₁ u₂) (v : ℝ) (hv : v ∈ Icc v₁ v₂) =>
    rectangle_in_integralForm hpos hS₁ hu hv
  have hi₂ := fun (u : ℝ) (hu : u ∈ Icc u₁ u₂) (v : ℝ) (hv : v ∈ Icc v₁ v₂) =>
    rectangle_in_integralForm hpos hS₂ hu hv
  have ho₁ := fun (u : ℝ) (hu : u ∈ Icc u₁ u₂) (v : ℝ) (hv : v ∈ Icc v₁ v₂) =>
    rectangle_out_integralForm hpos hS₁ hu hv
  have ho₂ := fun (u : ℝ) (hu : u ∈ Icc u₁ u₂) (v : ℝ) (hv : v ∈ Icc v₁ v₂) =>
    rectangle_out_integralForm hpos hS₂ hu hv
  have heq := rectangle_integral_uniqueness_of_source_bound h12 hv C.coe_nonneg
    (continuousOn_rectangle_state hS₁) (continuousOn_rectangle_state hS₂)
    hi₁ hi₂ ho₁ ho₂
    (fun p hp => by
      simpa only [dist_eq_norm] using hCi.dist_le_mul _ (hm₁ p hp) _ (hm₂ p hp))
    (fun p hp => by
      simpa only [dist_eq_norm] using hCo.dist_le_mul _ (hm₁ p hp) _ (hm₂ p hp))
    hYi hXb
  intro p hp
  exact (rectangle_state_eq_iff S₁ S₂ p).mp (heq hp)


end EmcsfAcExtension.Local
