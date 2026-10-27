/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Global.Glue.Segments
import EmcsfAcExtension.Infra.BV.Basic

/-! # The two axis limits across a characteristic seam

Closedness lets a centered triangle avoid any piece not containing the axis
point. On pieces containing it, use the frozen modulus with error `η / 2`.
The characteristic cover splits an incoming segment into at most two pieces;
exact variation additivity then gives the required uniform modulus on the union.
No coordinate change or additional regularity of the fields is used.
-/

public section

namespace EmcsfAcExtension.Global

open Set Filter Topology

private theorem centered_triangle_avoids_closed {D : Set (ℝ × ℝ)}
    (hD : IsClosed D) {t : ℝ} (ht : (t, t) ∉ D) :
    ∃ δ : ℝ, 0 < δ ∧ triangle (t - δ) (t + δ) ⊆ Dᶜ := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hD.isOpen_compl.mem_nhds ht)
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro p hp
  apply hball
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
  constructor
  · rw [abs_lt]
    constructor <;> linarith only [hp.1, hp.2.1, hp.2.2, hε]
  · rw [abs_lt]
    constructor <;> linarith only [hp.1, hp.2.1, hp.2.2, hε]

private theorem small_var_on_closed_piece {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hD : IsClosed D) (t η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ u a b, outSeg u a b ⊆ D ∩ triangle (t - δ) (t + δ) →
        eVariationOn (S.phi u) (Icc a b) ≤ ENNReal.ofReal η) ∧
      (∀ a b v, inSeg a b v ⊆ D ∩ triangle (t - δ) (t + δ) →
        eVariationOn (fun u => S.phi u v) (Icc a b) ≤ ENNReal.ofReal η) := by
  by_cases ht : (t, t) ∈ D
  · exact hS.axis_small_var t ht η hη
  obtain ⟨δ, hδ, hd⟩ := centered_triangle_avoids_closed hD ht
  refine ⟨δ, hδ, ?_, ?_⟩
  · intro u a b hs
    have hba : b ≤ a := by
      by_contra hn
      have hab := (lt_of_not_ge hn).le
      have hp := hs (show (u, a) ∈ outSeg u a b from ⟨rfl, le_rfl, hab⟩)
      exact hd hp.2 hp.1
    rw [eVariationOn.subsingleton _ (subsingleton_Icc_of_ge hba)]
    exact zero_le
  · intro a b v hs
    have hba : b ≤ a := by
      by_contra hn
      have hab := (lt_of_not_ge hn).le
      have hp := hs (show (a, v) ∈ inSeg a b v from ⟨le_rfl, hab, rfl⟩)
      exact hd hp.2 hp.1
    rw [eVariationOn.subsingleton _ (subsingleton_Icc_of_ge hba)]
    exact zero_le

/-- Shrinking characteristic variations glue using the two moduli with error `η / 2`.
The cover hypotheses concern segments, including their endpoints. In particular they
ensure that a crossing segment has an actual split point in both pieces. -/
theorem axis_small_var_union_of_segment_cover {e : ℝ} {S : Fields}
    {D₁ D₂ : Set (ℝ × ℝ)} (h₁ : IsSolution e S D₁) (h₂ : IsSolution e S D₂)
    (hc₁ : IsClosed D₁) (hc₂ : IsClosed D₂)
    (hout : ∀ u a b, a ≤ b → outSeg u a b ⊆ D₁ ∪ D₂ →
      outSeg u a b ⊆ D₁ ∨ outSeg u a b ⊆ D₂)
    (hin : ∀ a b v, a ≤ b → inSeg a b v ⊆ D₁ ∪ D₂ →
      inSeg a b v ⊆ D₁ ∨ inSeg a b v ⊆ D₂ ∨
      ∃ c, a ≤ c ∧ c ≤ b ∧ inSeg a c v ⊆ D₁ ∧ inSeg c b v ⊆ D₂)
    (t η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ u a b, outSeg u a b ⊆ (D₁ ∪ D₂) ∩ triangle (t - δ) (t + δ) →
        eVariationOn (S.phi u) (Icc a b) ≤ ENNReal.ofReal η) ∧
      (∀ a b v, inSeg a b v ⊆ (D₁ ∪ D₂) ∩ triangle (t - δ) (t + δ) →
        eVariationOn (fun u => S.phi u v) (Icc a b) ≤ ENNReal.ofReal η) := by
  obtain ⟨δ₁, hd₁, ho₁, hi₁⟩ := small_var_on_closed_piece h₁ hc₁ t (η / 2) (half_pos hη)
  obtain ⟨δ₂, hd₂, ho₂, hi₂⟩ := small_var_on_closed_piece h₂ hc₂ t (η / 2) (half_pos hη)
  have hm₁ := centered_triangle_mono (t := t) (min_le_left δ₁ δ₂)
  have hm₂ := centered_triangle_mono (t := t) (min_le_right δ₁ δ₂)
  have hhalf : ENNReal.ofReal (η / 2) ≤ ENNReal.ofReal η :=
    ENNReal.ofReal_le_ofReal (by linarith only [hη])
  have hsum : ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) = ENNReal.ofReal η := by
    rw [← ENNReal.ofReal_add (half_pos hη).le (half_pos hη).le]
    congr 1
    ring
  refine ⟨min δ₁ δ₂, lt_min hd₁ hd₂, ?_, ?_⟩
  · intro u a b hs
    by_cases hab : a ≤ b
    · rcases hout u a b hab (hs.trans inter_subset_left) with h | h
      · exact (ho₁ u a b (fun p hp => ⟨h hp, hm₁ (hs hp).2⟩)).trans hhalf
      · exact (ho₂ u a b (fun p hp => ⟨h hp, hm₂ (hs hp).2⟩)).trans hhalf
    · rw [eVariationOn.subsingleton _ (subsingleton_Icc_of_ge (le_of_not_ge hab))]
      exact zero_le
  · intro a b v hs
    by_cases hab : a ≤ b
    · rcases hin a b v hab (hs.trans inter_subset_left) with h | h | ⟨c, hac, hcb, hl, hr⟩
      · exact (hi₁ a b v (fun p hp => ⟨h hp, hm₁ (hs hp).2⟩)).trans hhalf
      · exact (hi₂ a b v (fun p hp => ⟨h hp, hm₂ (hs hp).2⟩)).trans hhalf
      · have hs₁ : inSeg a c v ⊆ (D₁ ∪ D₂) ∩ triangle (t - min δ₁ δ₂) (t + min δ₁ δ₂) :=
          fun p hp => hs ⟨hp.1, hp.2.1.trans hcb, hp.2.2⟩
        have hs₂ : inSeg c b v ⊆ (D₁ ∪ D₂) ∩ triangle (t - min δ₁ δ₂) (t + min δ₁ δ₂) :=
          fun p hp => hs ⟨hac.trans hp.1, hp.2.1, hp.2.2⟩
        rw [eVariationOn.Icc_eq_add _ hac hcb, ← hsum]
        exact add_le_add (hi₁ a c v (fun p hp => ⟨hl hp, hm₁ (hs₁ hp).2⟩))
          (hi₂ c b v (fun p hp => ⟨hr hp, hm₂ (hs₂ hp).2⟩))
    · rw [eVariationOn.subsingleton _ (subsingleton_Icc_of_ge (le_of_not_ge hab))]
      exact zero_le

/-- The zero mass-ratio limit glues over two closed pieces. A piece missing the
axis point contributes the bottom neighborhood filter, by closedness. -/
theorem axis_mu_union {e : ℝ} {S : Fields} {D₁ D₂ : Set (ℝ × ℝ)}
    (h₁ : IsSolution e S D₁) (h₂ : IsSolution e S D₂)
    (hc₁ : IsClosed D₁) (hc₂ : IsClosed D₂) (t : ℝ) :
    Tendsto (Function.uncurry S.mu)
      (𝓝[(D₁ ∪ D₂) ∩ {p | p.1 < p.2}] (t, t)) (𝓝 0) := by
  rw [union_inter_distrib_right, nhdsWithin_union]
  apply tendsto_sup.mpr
  constructor
  · by_cases ht : (t, t) ∈ D₁
    · exact h₁.axis_mu t ht
    · have hn : (t, t) ∉ closure (D₁ ∩ {p | p.1 < p.2}) :=
        fun hp => ht (closure_minimal inter_subset_left hc₁ hp)
      rw [notMem_closure_iff_nhdsWithin_eq_bot.mp hn]
      exact tendsto_bot
  · by_cases ht : (t, t) ∈ D₂
    · exact h₂.axis_mu t ht
    · have hn : (t, t) ∉ closure (D₂ ∩ {p | p.1 < p.2}) :=
        fun hp => ht (closure_minimal inter_subset_left hc₂ hp)
      rw [notMem_closure_iff_nhdsWithin_eq_bot.mp hn]
      exact tendsto_bot

end EmcsfAcExtension.Global
