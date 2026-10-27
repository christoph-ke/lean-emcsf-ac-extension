module

public import EmcsfAcExtension.Local.Construction.ContinuationInputs
public import EmcsfAcExtension.Local.Construction.ContinuationBridge
public import EmcsfAcExtension.Local.Broad.RectangleState
import EmcsfAcExtension.Local.Calculus.C1ToSolution2
import EmcsfAcExtension.Local.Construction.CornerGlue
import EmcsfAcExtension.Local.Broad.GeometryInitial
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Fixed original-cone representatives for continuation

A local wedge already contains the entire original cone. Its entering
block provides fixed C¹ data and a fixed global Lipschitz representative
before the old apex and strip/corner parameters are chosen.
-/

public section

open Set Filter Topology
open scoped NNReal

namespace EmcsfAcExtension.Local

/-- Enlarging a positive full continuation bound retains every margin
and all nine primary and normalized first-jet estimates. -/
theorem continuation_c1BoundOn_weaken {F : Fields} {D : Set (ℝ × ℝ)} {B C : ℝ}
    (hB : 0 < B) (hBC : B ≤ C) (h : C1BoundOn F D B) : C1BoundOn F D C := by
  have hinv : C⁻¹ ≤ B⁻¹ := inv_anti₀ hB hBC
  intro p hp
  obtain ⟨hl, hn, hg, hr, hc⟩ := h p hp
  exact ⟨hinv.trans hl, hinv.trans hn, hinv.trans hg,
    fun f hf => ⟨(hr f hf).1.trans hBC, (hr f hf).2.trans hBC⟩,
    fun f hf => ⟨(hc f hf).1.trans hBC, (hc f hf).2.trans hBC⟩⟩

/-- C¹ interval data have one finite common value/first-derivative bound.
The bound follows the fixed datum and precedes all subintervals. -/
theorem continuation_c1_trace_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ} {f : ℝ → E}
    (hab : a < b) (hf : ContDiffOn ℝ 1 f (Icc a b)) :
    ∃ B : ℝ, 0 < B ∧ ∀ v ∈ Icc a b,
      ‖f v‖ ≤ B ∧ ‖derivWithin f (Icc a b) v‖ ≤ B := by
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.bddAbove_image hf.continuousOn.norm
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.bddAbove_image
    (hf.continuousOn_derivWithin (uniqueDiffOn_Icc hab) (by norm_num)).norm
  refine ⟨1+max 0 (max C₀ C₁), by positivity, ?_⟩
  intro v hv
  constructor
  · exact (hC₀ (mem_image_of_mem _ hv)).trans (by
      have := (le_max_left C₀ C₁).trans (le_max_right 0 (max C₀ C₁))
      linarith)
  · exact (hC₁ (mem_image_of_mem _ hv)).trans (by
      have := (le_max_right C₀ C₁).trans (le_max_right 0 (max C₀ C₁))
      linarith)

/-- The entering cone of a classical local wedge is a frozen broad
solution on that cone. Ambient unique differentiation is used on the
wedge; no transverse derivative is assigned to the one-dimensional cone. -/
theorem IsC1Solution.toIsSolution_initialCone {T a e : ℝ} {F : Fields}
    (ha : 0 < a) (haT : a ≤ T)
    (hF : IsC1Solution e F (continuationWedge 0 a T)) :
    IsSolution e F (outSeg 0 0 T) := by
  have hcompact : IsCompact (continuationWedge 0 a T) := by
    simpa only [continuationWedge, zero_add] using
      (isCompact_triangle 0 T).inter_right
        (isClosed_le continuous_fst continuous_const : IsClosed {p : ℝ×ℝ | p.1 ≤ a})
  have hU : UniqueDiffOn ℝ (continuationWedge 0 a T) := by
    simpa only [continuationWedge, zero_add] using
      uniqueDiffOn_triangle_inter_fst_le ha haT
  have hcone : outSeg 0 0 T ⊆ continuationWedge 0 a T := by
    rintro ⟨u,v⟩ ⟨rfl, hp⟩
    exact ⟨⟨le_rfl, hp.1, by simpa only [zero_add] using hp.2⟩, by simpa using ha.le⟩
  apply hF.toIsSolution_on_of_axis_mu hcompact hU hcone
  intro t ht
  have ht0 : t = 0 := ht.1
  subst t
  have htriangle : triangle 0 a ⊆ continuationWedge 0 a T := by
    intro p hp
    exact ⟨⟨hp.1, hp.2.1, by simpa only [zero_add] using hp.2.2.trans haT⟩,
      by change p.1 ≤ 0+a; simpa only [zero_add] using hp.2.1.trans hp.2.2⟩
  have hOld := (hF.mono htriangle (uniqueDiffOn_triangle ha)).toIsSolution ha
  have hN : {p : ℝ×ℝ | p.2 < a} ∈ 𝓝 ((0,0) : ℝ×ℝ) :=
    (isOpen_lt continuous_snd continuous_const).mem_nhds ha
  apply (hOld.axis_mu 0 ⟨le_rfl, le_rfl, ha.le⟩).mono_left
  apply le_inf inf_le_left
  rw [Filter.le_principal_iff]
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hN] with p hp hn
  refine ⟨⟨?_, hp.2.le, hn.le⟩, hp.2⟩
  have hp0 : p.1 = 0 := hp.1.1
  exact hp0.ge

/-- Every original-cone field is fixed by the datum, even when one
construction is a short wedge and the other a larger complete triangle.
This supplies the original entering block in every appended strip. -/
theorem c1_initial_cone_fields_agree {T a s e : ℝ} {h : ℝ → ℂ} {F G : Fields}
    (ha : 0 < a) (haT : a ≤ T) (hs : 0 < s) (hsT : s ≤ T)
    (hF : IsC1Solution e F (continuationWedge 0 a T))
    (hG : IsC1Solution e G (triangle 0 s))
    (hdataF : IsRestartData F h T) (hdataG : IsRestartData G h s) :
    F.EqOn G (outSeg 0 0 s) := by
  have hconeF : outSeg 0 0 s ⊆ outSeg 0 0 T :=
    fun p hp => ⟨hp.1, hp.2.1, hp.2.2.trans hsT⟩
  have hconeG : outSeg 0 0 s ⊆ triangle 0 s := by
    rintro ⟨u,v⟩ ⟨rfl, hp⟩
    exact ⟨le_rfl, hp⟩
  apply Broad.common_data_initial_constraint_agreement
    (hF.toIsSolution_initialCone ha haT) (hG.toIsSolution hs) hs hconeF hconeG
  · intro v hv
    exact ⟨(hdataF.1 v ⟨hv.1, hv.2.trans hsT⟩).1.trans (hdataG.1 v hv).1.symm,
      (hdataF.1 v ⟨hv.1, hv.2.trans hsT⟩).2.trans (hdataG.1 v hv).2.symm⟩
  · exact hdataF.2 0 ⟨le_rfl, hs.le.trans hsT⟩
  · exact hdataG.2 0 ⟨le_rfl, hs.le⟩

/-- Fix one globally Lipschitz entering-block representative before all
strip apex coordinates. Its restriction to the complete original cone
is C¹ and equals the already constructed local solution exactly. -/
theorem continuation_original_block_extension {T a e : ℝ} {F : Fields}
    (ha : 0 < a) (_haT : a ≤ T)
    (hF : IsC1Solution e F (continuationWedge 0 a T)) :
    ∃ (J : ℝ≥0) (yi : ℝ → Broad.RectangleIncoming),
      0 < J ∧ LipschitzWith J yi ∧ ContDiffOn ℝ 1 yi (Icc 0 T) ∧
      EqOn yi (fun v => (F.lam 0 v, F.theta 0 v)) (Icc 0 T) := by
  have hmap : MapsTo (fun v : ℝ => (0,v)) (Icc 0 T) (continuationWedge 0 a T) := by
    intro v hv
    exact ⟨⟨le_rfl, hv.1, by simpa using hv.2⟩, by simpa using ha.le⟩
  have hc : ContDiffOn ℝ 1 (fun v => (F.lam 0 v, F.theta 0 v)) (Icc 0 T) := by
    have hh := (hF.c1_lam.prodMk hF.c1_theta).comp
      (show ContDiffOn ℝ 1 (fun v : ℝ => (0,v)) (Icc 0 T) by fun_prop) hmap
    simpa only [Function.comp_def, Function.uncurry_def] using! hh
  obtain ⟨K, hK⟩ := hc.exists_lipschitzOnWith (by norm_num) (convex_Icc 0 T) isCompact_Icc
  obtain ⟨yi, hLip, hEq⟩ := hK.extend_finite_dimension
  let J := lipschitzExtensionConstant Broad.RectangleIncoming*K+1
  have hJ : 0 < J := by positivity
  refine ⟨J, yi, hJ, hLip.weaken (by dsimp only [J]; exact le_add_of_nonneg_right bot_le),
    hc.congr (fun _ hv => (hEq hv).symm), fun _ hv => (hEq hv).symm⟩

end EmcsfAcExtension.Local
