module

public import EmcsfAcExtension.Local.Broad.RectangleVolterra
public import EmcsfAcExtension.Local.Broad.RectangleEquations
public import EmcsfAcExtension.Local.Broad.RectangleLipschitz
public import EmcsfAcExtension.Local.Broad.RectangleCompact

/-! # Full broad uniqueness on a positive-radius characteristic rectangle

The frozen nine-field system is locally Lipschitz on a compact convex
state container. The ordinary characteristic Volterra comparison then
propagates both entering-edge data across the entire rectangle.
-/

public section

open Set

namespace EmcsfAcExtension.Local

open Broad

/-- [node restart-stab-broad-uniqueness#positive-radius-rectangle-uniqueness]
Broad solutions agreeing on both entering edges agree on the complete
positive-radius rectangle, charged_SF_new_version.tex:L5905–5905 and internal project record.
All nine fields, including charge and potential, are compared. There are
no smallness, smoothness, envelope or auxiliary coefficient hypotheses. -/
theorem broad_rectangle_uniqueness {e u₁ u₂ v₁ v₂ : ℝ} {S₁ S₂ : Fields}
    (h12 : u₁ ≤ u₂) (hv : v₁ ≤ v₂) (hpos : u₂ < v₁)
    (hS₁ : IsSolution e S₁ (Icc u₁ u₂ ×ˢ Icc v₁ v₂))
    (hS₂ : IsSolution e S₂ (Icc u₁ u₂ ×ˢ Icc v₁ v₂))
    (hedge : S₁.EqOn S₂ (({u₁} ×ˢ Icc v₁ v₂) ∪ (Icc u₁ u₂ ×ˢ {v₁}))) :
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
    (fun v hv => congrArg Prod.fst ((rectangle_state_eq_iff S₁ S₂ (u₁, v)).mpr
      (hedge (u₁, v) (Or.inl ⟨rfl, hv⟩))))
    (fun u hu => congrArg Prod.snd ((rectangle_state_eq_iff S₁ S₂ (u, v₁)).mpr
      (hedge (u, v₁) (Or.inr ⟨hu, rfl⟩))))
  intro p hp
  exact (rectangle_state_eq_iff S₁ S₂ p).mp (heq hp)

end EmcsfAcExtension.Local
