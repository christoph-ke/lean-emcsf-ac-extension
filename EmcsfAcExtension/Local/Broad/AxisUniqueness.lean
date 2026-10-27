module

public import EmcsfAcExtension.Local.Broad.AxisUniquenessCompact

/-! # Local uniqueness at an existing regular axis point

A compact comparison parent is selected before choosing the contraction
threshold. The final statement is relative to the original domain and
assumes no neighborhood of that domain beyond the compared triangle.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- [node restart-stab-broad-uniqueness#local-axis-uniqueness]
Two frozen broad solutions with common entering radius and normalized
scalar and the same zero-axis gauge agree on sufficiently small axis
triangles, as in charged_SF_new_version.tex:L5904–5905 and internal project record. The neighborhood
may depend on their fixed finite local BV budget and geometric box.
The initial expansion agreement follows from the radius constraint. -/
theorem broad_local_axis_uniqueness {e : ℝ} {S₁ S₂ : Fields} {q : ℝ}
    {D : Set (ℝ × ℝ)} (hS₁ : IsSolution e S₁ D) (hS₂ : IsSolution e S₂ D)
    (_hq : (q, q) ∈ D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, q - δ ≤ s → s ≤ q → triangle s (q + δ) ⊆ D →
      (∀ v ∈ Icc s (q + δ), S₁.r s v = S₂.r s v ∧ S₁.a s v = S₂.a s v) →
      (∀ u ∈ Icc s (q + δ), S₁.A u u = 0 ∧ S₂.A u u = 0) →
      S₁.EqOn S₂ (triangle s (q + δ)) := by
  by_cases hleft : ∃ a b : ℝ, a < q ∧ q < b ∧ triangle a b ⊆ D
  · obtain ⟨a, b, haq, hqb, hparent⟩ := hleft
    have hp₁ := isSolution_mono hS₁ hparent
    have hp₂ := isSolution_mono hS₂ hparent
    obtain ⟨δ₀, hδ₀, hunique⟩ := broad_local_axis_uniqueness_of_compact hp₁ hp₂
      (isCompact_triangle a b) ⟨haq.le, le_rfl, hqb.le⟩
    let δ := min δ₀ (min ((q - a) / 2) ((b - q) / 2))
    have hδ : 0 < δ := lt_min hδ₀ (lt_min (by linarith) (by linarith))
    have hδ₀' : δ ≤ δ₀ := min_le_left _ _
    have hδa : δ ≤ (q - a) / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hδb : δ ≤ (b - q) / 2 := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨δ, hδ, ?_⟩
    intro s hs hsq _hsub hdata haxis
    apply hunique δ hδ hδ₀' s hs hsq _ hdata haxis
    apply triangle_mono (by linarith : a ≤ s) (by linarith : q + δ ≤ b)
  · by_cases hright : ∃ b : ℝ, q < b ∧ triangle q b ⊆ D
    · obtain ⟨b, hqb, hparent⟩ := hright
      have hp₁ := isSolution_mono hS₁ hparent
      have hp₂ := isSolution_mono hS₂ hparent
      obtain ⟨δ₀, hδ₀, hunique⟩ := broad_local_axis_uniqueness_of_compact hp₁ hp₂
        (isCompact_triangle q b) ⟨le_rfl, le_rfl, hqb.le⟩
      let δ := min δ₀ ((b - q) / 2)
      have hδ : 0 < δ := lt_min hδ₀ (by linarith)
      have hδ₀' : δ ≤ δ₀ := min_le_left _ _
      have hδb : δ ≤ (b - q) / 2 := min_le_right _ _
      refine ⟨δ, hδ, ?_⟩
      intro s hs hsq hsub hdata haxis
      have he : s = q := by
        apply le_antisymm hsq
        by_contra hn
        have hsq' : s < q := lt_of_not_ge hn
        exact hleft ⟨s, q + δ, hsq', by linarith, hsub⟩
      subst s
      apply hunique δ hδ hδ₀' q (by linarith) le_rfl _ hdata haxis
      exact triangle_mono le_rfl (by linarith)
    · refine ⟨1, zero_lt_one, ?_⟩
      intro s _hs hsq hsub _hdata _haxis
      exact False.elim (hright ⟨q + 1, by linarith,
        (triangle_mono hsq le_rfl).trans hsub⟩)

end EmcsfAcExtension.Local
