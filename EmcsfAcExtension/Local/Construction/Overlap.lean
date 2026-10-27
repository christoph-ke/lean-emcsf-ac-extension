module

public import EmcsfAcExtension.Local.Defs.C1Class
public import EmcsfAcExtension.Local.Construction.ContinuationBridge
public import EmcsfAcExtension.Local.Defs.Params
public import EmcsfAcExtension.Frozen.Fields.EqOn
import EmcsfAcExtension.Local.Calculus.C1ToSolution2
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Local.Broad.Propagation
import EmcsfAcExtension.Local.Broad.Rectangle
import EmcsfAcExtension.Local.Api.Mono
import EmcsfAcExtension.Infra.Null.IntegralForm
import EmcsfAcExtension.Local.Construction.ConeComparison
import EmcsfAcExtension.Local.Construction.Corner

import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Overlap comparison in the classical construction route

Complete outgoing-axis overlaps use the landed broad uniqueness theorem
after the C¹-to-frozen bridge. Positive-radius overlaps use the landed
two-entering-edge rectangle theorem. No invariant-ball membership or
quantitative smallness is required for either comparison.
-/

public section

open scoped NNReal ENNReal

open Set MeasureTheory

namespace EmcsfAcExtension.Local

/-- A classical solution on a compact unique-differentiation domain
strictly away from the axis belongs to the frozen broad class. The
finite variation bound may depend on the compact configuration. -/
theorem IsC1Solution.toIsSolution_offAxis {e : ℝ} {F : Fields} {D : Set (ℝ × ℝ)}
    (hF : IsC1Solution e F D) (hcompact : IsCompact D)
    (hunique : UniqueDiffOn ℝ D) (hoff : ∀ p ∈ D, p.1 < p.2) :
    IsSolution e F D := by
  apply hF.toIsSolution_of_axis_mu hcompact hunique
  intro t ht
  exact False.elim ((lt_irrefl t) (hoff (t,t) ht))


/-- [node restart-sec-independent-null-construction#smooth-overlap-uniqueness]
In the C¹ reading, the completed old/strip construction and the restarted
axis corner agree on their full closed overlap. The inherited `(λ,h)`
cone pair determines radius by its primitive, and broad initial
constraint uniqueness determines the other entering fields. The axis
gauges belong to the two already constructed configurations. -/
theorem c1_corner_union_overlap
    {e c d s b : ℝ} {F G : Fields}
    (hc : 0 ≤ c) (hcd : c < d) (hds : d < s) (hsb : s < b)
    (hF : IsC1Solution e F (triangle 0 s ∪ (Icc 0 d ×ˢ Icc s b)))
    (hG : IsC1Solution e G (triangle c b))
    (hpair : ∀ v ∈ Icc c b, F.lam c v = G.lam c v ∧ F.a c v = G.a c v)
    (hgaugeF : ∀ t ∈ Icc 0 s, F.A t t = 0)
    (hgaugeG : ∀ t ∈ Icc c b, G.A t t = 0) :
    F.EqOn G ((triangle 0 s ∪ (Icc 0 d ×ˢ Icc s b)) ∩ triangle c b) := by
  have hs : 0 < s := hc.trans_lt (hcd.trans hds)
  have hd : 0 < d := hc.trans_lt hcd
  have hcs : c < s := hcd.trans hds
  have hcb : c < b := hcs.trans hsb
  have hFS := hF.toIsSolution_triangle_strip hs hd hds hsb
  have hGS := hG.toIsSolution hcb
  have hconeF : outSeg c c b ⊆ triangle 0 s ∪ (Icc 0 d ×ˢ Icc s b) := by
    rintro p ⟨rfl, hp⟩
    by_cases hps : p.2 ≤ s
    · exact Or.inl ⟨hc, hp.1, hps⟩
    · exact Or.inr ⟨⟨hc, hcd.le⟩, (lt_of_not_ge hps).le, hp.2⟩
  have hconeG : outSeg c c b ⊆ triangle c b := by
    rintro p ⟨rfl, hp⟩
    exact ⟨le_rfl, hp⟩
  have hdata : ∀ v ∈ Icc c b, F.r c v = G.r c v ∧ F.a c v = G.a c v := by
    intro v hv
    refine ⟨?_, (hpair v hv).2⟩
    have hf : outSeg c c v ⊆ triangle 0 s ∪ (Icc 0 d ×ˢ Icc s b) :=
      fun p hp => hconeF ⟨hp.1, hp.2.1, hp.2.2.trans hv.2⟩
    have hg : outSeg c c v ⊆ triangle c b :=
      fun p hp => hconeG ⟨hp.1, hp.2.1, hp.2.2.trans hv.2⟩
    rw [c1_radius_primitive_on_cone hF hv.1 hf,
      c1_radius_primitive_on_cone hG hv.1 hg]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hv.1] at hx
    exact (hpair x ⟨hx.1, hx.2.trans hv.2⟩).1
  have hcone := Broad.common_data_initial_constraint_agreement hFS hGS hcb
    hconeF hconeG hdata (hgaugeF c ⟨hc, hcs.le⟩)
    (hgaugeG c ⟨le_rfl, hcb.le⟩)
  have hold : F.EqOn G (triangle c s) := by
    apply broad_uniqueness hcs
      (isSolution_mono hFS (fun p hp => Or.inl ⟨hc.trans hp.1, hp.2⟩))
      (isSolution_mono hGS (triangle_mono le_rfl hsb.le))
    · intro v hv
      exact hdata v ⟨hv.1, hv.2.trans hsb.le⟩
    · intro t ht
      exact ⟨hgaugeF t ⟨hc.trans ht.1, ht.2⟩,
        hgaugeG t ⟨ht.1, ht.2.trans hsb.le⟩⟩
  have hstrip : F.EqOn G (Icc c d ×ˢ Icc s b) := by
    apply broad_rectangle_uniqueness hcd.le hsb.le hds
      (isSolution_mono hFS (fun p hp =>
        Or.inr ⟨⟨hc.trans hp.1.1, hp.1.2⟩, hp.2⟩))
      (isSolution_mono hGS (fun p hp =>
        ⟨hp.1.1, hp.1.2.trans (hds.le.trans hp.2.1), hp.2.2⟩))
    intro p hp
    rcases hp with hp | hp
    · exact hcone p ⟨hp.1, hcs.le.trans hp.2.1, hp.2.2⟩
    · have hp' : p.2 = s := hp.2
      exact hold p ⟨hp.1.1, hp.1.2.trans (hds.le.trans hp'.ge), hp'.le⟩
  rw [continuation_axis_overlap_geometry hc hds.le hsb.le]
  intro p hp
  exact hp.elim (hold p) (hstrip p)

end EmcsfAcExtension.Local
