module

public import EmcsfAcExtension.Local.Construction.PicardBall
public import EmcsfAcExtension.Frozen.DatumVar

/-! # Initial variation and the canonical Picard gap

The datum's finite total variation bounds every initial oscillation. C1 data
on a closed interval have finite variation. These facts discharge the explicit
oscillation premise of the canonical ball-gap estimate; they do not prove ball
invariance under the incoming map.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- C1 cone data on a nonnegative-length compact interval have finite variation.
No higher derivative or quantitative derivative bound is required. -/
theorem picardDatum_boundedVariationOn {L : ℝ} {h : ℝ → ℂ}
    (hc : ContDiffOn ℝ 1 h (Icc 0 L)) (hL : 0 ≤ L) :
    BoundedVariationOn h (Icc 0 L) := by
  obtain ⟨K, hK⟩ := hc.exists_lipschitzOnWith (by norm_num) (convex_Icc 0 L) isCompact_Icc
  simpa only [inter_self] using
    hK.locallyBoundedVariationOn 0 L ⟨le_rfl, hL⟩ ⟨hL, le_rfl⟩

/-- The initial oscillation is bounded by `datumVar` with universal constant one.
Finite variation is explicit, so the real conversion never discards infinity. -/
theorem picardDatum_oscillation_le {L ε : ℝ} {h : ℝ → ℂ}
    (hb : BoundedVariationOn h (Icc 0 L)) (hv : datumVar h L ≤ ε)
    {s t : ℝ} (hs : s ∈ Icc 0 L) (ht : t ∈ Icc 0 L) : ‖h s - h t‖ ≤ ε := by
  have hd : ‖h s - h t‖ ≤ datumVar h L := by
    simpa only [dist_eq_norm, datumVar] using hb.dist_le hs ht
  exact hd.trans hv

/-- C1 initial data of variation at most `ε` have oscillation at most `ε`,
with universal constant one, uniformly in the interval length and datum. -/
theorem picardDatum_oscillation_le_of_contDiffOn {L ε : ℝ} {h : ℝ → ℂ}
    (hc : ContDiffOn ℝ 1 h (Icc 0 L)) (hv : datumVar h L ≤ ε)
    {s t : ℝ} (hs : s ∈ Icc 0 L) (ht : t ∈ Icc 0 L) : ‖h s - h t‖ ≤ ε :=
  picardDatum_oscillation_le (picardDatum_boundedVariationOn hc (hs.1.trans hs.2)) hv hs ht

/-- The canonical radius-`1/128` ball has gap at least `3/4` for C1 initial data
with the displayed small variation and charged scale. All numerical constants
are universal, and the background is exactly S2's `1 + norm(h(0)) + 10*ε`. -/
theorem picardBall_gap_of_datumVar {a L ε e : ℝ} (ha : 0 ≤ a) (haL : a ≤ L)
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 64) (h : ℝ → ℂ)
    (hc : ContDiffOn ℝ 1 h (Icc 0 L)) (hv : datumVar h L ≤ ε)
    (center : PicardCarrier 0 a L (ℝ × ℂ))
    (hcenter : ∀ q : PicardDomain 0 a L, center.1.1 q = (1 / 2, h q.1.2))
    (hscale : |e| * (1 + ‖h 0‖ + 10 * ε) * L ≤ 1 / 16)
    (z : PicardBall (fun v => ((1 / 2 : ℝ), h v)) center (1 / 128))
    (p : PicardDomain 0 a L) :
    3 / 4 ≤ 1 - Recon.mu e (picardCandidateLam ha haL z.1)
      (picardCandidateH ha haL z.1) p.1.1 p.1.2 :=
  picardBall_gap_of_center_values ha haL hε hεsmall h center hcenter
    (fun _ hs _ ht => picardDatum_oscillation_le_of_contDiffOn hc hv hs ht) hscale z p

/-- C1 data on a nondegenerate compact cone interval define the constant-in-u
center with their canonical within derivative as outgoing jet. No extension
outside the initial interval or future axis datum is required. -/
@[expose] noncomputable def picardConeCenterOfContDiff {c a L : ℝ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (datum : ℝ → E) (hL : 0 < L) (hc : ContDiffOn ℝ 1 datum (Icc c (c + L))) :
    PicardCarrier c a L E := by
  refine picardConeCenter datum (derivWithin datum (Icc c (c + L))) hc.continuousOn
    (hc.continuousOn_derivWithin (uniqueDiffOn_Icc (by linarith)) (by norm_num)) ?_
  intro v hv
  exact ((hc.differentiableOn (by norm_num)) v (Ioo_subset_Icc_self hv)).hasDerivWithinAt.hasDerivAt
    (Icc_mem_nhds hv.1 hv.2)

/-- The C1 cone center has exactly the original datum values. -/
@[simp] theorem picardConeCenterOfContDiff_value {c a L : ℝ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (datum : ℝ → E) (hL : 0 < L) (hc : ContDiffOn ℝ 1 datum (Icc c (c + L)))
    (p : PicardDomain c a L) :
    (picardConeCenterOfContDiff datum hL hc).1.1 p = datum p.1.2 := rfl

/-- The C1 cone center stores the canonical within derivative on the closed interval. -/
@[simp] theorem picardConeCenterOfContDiff_jet {c a L : ℝ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (datum : ℝ → E) (hL : 0 < L) (hc : ContDiffOn ℝ 1 datum (Icc c (c + L)))
    (p : PicardDomain c a L) :
    (picardConeCenterOfContDiff datum hL hc).1.2 p = derivWithin datum (Icc c (c + L)) p.1.2 := rfl

/-- The C1 cone center belongs to the prescribed initial affine set. -/
theorem picardConeCenterOfContDiff_mem_initialSet {c a L : ℝ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (datum : ℝ → E) (hL : 0 < L) (hc : ContDiffOn ℝ 1 datum (Icc c (c + L))) :
    picardConeCenterOfContDiff (a := a) datum hL hc ∈ picardInitialSet datum := by
  apply (mem_picardInitialSet_iff _ _).mpr
  intro p _
  exact picardConeCenterOfContDiff_value datum hL hc p

end EmcsfAcExtension.Local
