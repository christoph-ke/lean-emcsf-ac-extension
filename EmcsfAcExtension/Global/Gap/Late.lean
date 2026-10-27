module

public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Stages
import EmcsfAcExtension.Global.Gap.Apex
import EmcsfAcExtension.Global.Gap.Conditional
import EmcsfAcExtension.Local.Api.Mono

/-! # The late gap from the terminal-size limit

The stopping parameter is the apex label of a complete proper triangle.
The fixed numerical gap is halved in the conclusion, as required by A-δ0.
Source: charged_SF_new_version.tex:L1765–1816; approved internal project record.
-/

public section

open Set Filter Topology MeasureTheory

namespace EmcsfAcExtension.Global

namespace LateGap

/-- [node prop:charged-late-gap#outgoing-scalar-oscillation]
The full weighted Cauchy–Schwarz chain on a positive-radius outgoing
segment, with the radial Jacobian `dr = λ dv`. The fixed finite optical
bound is uniform on the row; every numerical coefficient is universal.
No interior lower gap or scalar translation is assumed. -/
theorem outgoing_scalar_oscillation {e u v Λ : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (huv : u < v) (hv : v ≤ 0) (hs : outSeg u v 0 ⊆ D)
    (hm : 0 ≤ S.m u v)
    (hopt : ∀ w ∈ Icc v 0, S.lam u w / (1 - S.mu u w) ≤ Λ) :
    let E := ∫ w in v..0, S.lam u w * (1 - S.mu u w) *
      ‖S.theta u w / (S.lam u w : ℂ)‖ ^ 2
    let W := ∫ w in v..0, S.lam u w / (1 - S.mu u w) * (S.r u v / S.r u w) ^ 2
    S.r u v ^ 2 * ‖S.phi u v - S.phi u 0‖ ^ 2 ≤ E * W ∧
      E * W ≤ 2 * Λ * S.m u 0 * (-v) ∧
      2 * Λ * S.m u 0 * (-v) ≤ 2 * Λ * S.m u 0 * (-u) := by
  dsimp only
  have hp (w : ℝ) (hw : w ∈ Icc v 0) : (u, w) ∈ D := hs ⟨rfl, hw⟩
  have hr (w : ℝ) (hw : w ∈ Icc v 0) := hS.r_pos (u, w) (hp w hw) (huv.trans_le hw.1)
  have hl (w : ℝ) (hw : w ∈ Icc v 0) := hS.lam_pos (u, w) (hp w hw)
  have hg (w : ℝ) (hw : w ∈ Icc v 0) := hS.one_sub_mu_pos (u, w) (hp w hw)
  have hΛ : 0 ≤ Λ := (div_nonneg (hl v ⟨le_rfl, hv⟩).le
    (hg v ⟨le_rfl, hv⟩).le).trans (hopt v ⟨le_rfl, hv⟩)
  have hm0 : 0 ≤ S.m u 0 := hm.trans (Gap.mass_out_le hS huv.le hv hs)
  have hE := (Annulus.annular_masses hS huv hv hs).2.1
  have hE' : (∫ w in v..0, S.lam u w * (1 - S.mu u w) *
      ‖S.theta u w / (S.lam u w : ℂ)‖ ^ 2) ≤ 2 * S.m u 0 := by
    linarith only [hE, hm]
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have cg : ContinuousOn (fun w => 1 - S.mu u w) (Icc v 0) :=
    continuousOn_const.sub (Calculus.continuousOn_out_section (Gap.continuousOn_mu hS) hs)
  have cW : ContinuousOn (fun w => S.lam u w / (1 - S.mu u w) *
      (S.r u v / S.r u w) ^ 2) (Icc v 0) :=
    (cl.div cg (fun w hw => (hg w hw).ne')).mul
      (((continuousOn_const (c := S.r u v)).div cr (fun w hw => (hr w hw).ne')).pow 2)
  have hW0 : 0 ≤ ∫ w in v..0, S.lam u w / (1 - S.mu u w) *
      (S.r u v / S.r u w) ^ 2 := intervalIntegral.integral_nonneg hv
    (fun w hw => mul_nonneg (div_nonneg (hl w hw).le (hg w hw).le) (sq_nonneg _))
  have hW : (∫ w in v..0, S.lam u w / (1 - S.mu u w) *
      (S.r u v / S.r u w) ^ 2) ≤ Λ * (-v) := by
    have hi := intervalIntegral.integral_mono_on (μ := volume) hv (cW.intervalIntegrable_of_Icc hv)
      (intervalIntegrable_const (c := Λ)) (fun w hw => by
        have hrad := Gap.radius_out_le hS huv.le hw.1
          (show outSeg u v w ⊆ D from fun p hp => hs ⟨hp.1, hp.2.1, hp.2.2.trans hw.2⟩)
        have hratio := (div_le_one (hr w hw)).mpr hrad
        have hn := div_nonneg (hr v ⟨le_rfl, hv⟩).le (hr w hw).le
        have hsquare : (S.r u v / S.r u w) ^ 2 ≤ 1 := by nlinarith only [hratio, hn]
        exact (mul_le_of_le_one_right (div_nonneg (hl w hw).le (hg w hw).le) hsquare).trans
          (hopt w hw))
    simpa only [intervalIntegral.integral_const, smul_eq_mul, zero_sub, mul_comm] using hi
  refine ⟨Gap.scalar_oscillation_cauchy_schwarz hS huv hv hs, ?_, ?_⟩
  · have hi := (mul_le_mul_of_nonneg_right hE' hW0).trans
      (mul_le_mul_of_nonneg_left hW (mul_nonneg (by norm_num) hm0))
    convert hi using 1
    ring
  · exact mul_le_mul_of_nonneg_left (neg_le_neg huv.le)
      (mul_nonneg (mul_nonneg (by norm_num) hΛ) hm0)

/-- [internal] The universal geometric constant is positive and less than one. -/
theorem gapConstant_bounds : 0 < gapConstant ∧ gapConstant < 1 := by
  have hp := Real.exp_pos (-32 : ℝ)
  have he : Real.exp (-32 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  unfold gapConstant
  constructor <;> linarith only [hp, he]

/-- [node prop:charged-late-gap#late-time-choice]
For the fixed coupling, one entry label controls every later complete row.
The label may depend on the development, the finite optical bound and the
size convergence. The coefficient `1/128` is universal. -/
theorem late_time_choice {ui e Λ : ℝ} {S : Fields} (hui : ui < 0)
    (hS : IsSolution e S (origDomain ui))
    (hopt : ∀ p ∈ origDomain ui, S.lam p.1 p.2 / (1 - S.mu p.1 p.2) ≤ Λ)
    (hsize : Tendsto (fun u => S.r u 0 * ‖S.phi u 0‖ +
      Real.sqrt (2 * Λ * S.m u 0 * (-u))) (𝓝[<] 0) (𝓝 0)) :
    ∃ a ∈ Ioo ui 0, ∀ p ∈ origDomain ui, a ≤ p.1 →
      |e| * S.r p.1 p.2 * ‖S.phi p.1 p.2‖ ≤ gapConstant / 128 := by
  have ht := hsize.const_mul |e|
  simp only [mul_zero] at ht
  have hev := ht.eventually (Iio_mem_nhds (show 0 < gapConstant / 128 by
    exact div_pos gapConstant_bounds.1 (by norm_num)))
  obtain ⟨b, hb, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hev
  obtain ⟨a, ha, ha0⟩ := exists_between (max_lt hui hb)
  refine ⟨a, ⟨(le_max_left _ _).trans_lt ha, ha0⟩, ?_⟩
  intro p hp hap
  have hs : outSeg p.1 p.1 0 ⊆ origDomain ui :=
    (outSeg_axis_subset_origDomain_iff hp.2.1.le).2 ⟨hp.1, hp.2.1, le_rfl⟩
  have hrow := Gap.global_scaled_scalar hS hp.2.1 hs
    (fun w hw => hopt (p.1, w) (hs ⟨rfl, hw⟩)) ⟨hp.2.2.1, hp.2.2.2⟩
  have hsmall := hsub (show p.1 ∈ Ioo b 0 from
    ⟨(le_max_right _ _).trans_lt (ha.trans_le hap), hp.2.1⟩)
  exact (show |e| * S.r p.1 p.2 * ‖S.phi p.1 p.2‖ ≤
      |e| * (S.r p.1 0 * ‖S.phi p.1 0‖ +
        Real.sqrt (2 * Λ * S.m p.1 0 * (-p.1))) by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hrow (abs_nonneg e)).trans hsmall.le

/-- [node prop:charged-late-gap#first-apex-gap-contradiction]
The smallness delivered by `late_time_choice` excludes an apex minimum at
half the geometric gap. Every conditional-gap invocation is on a complete
proper triangle. All numerical constants are universal. -/
theorem first_apex_gap_contradiction_of_smallness {ui e a : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (hia : ui ≤ a) (_ha : a < 0)
    (hmu : ∀ p ∈ origDomain ui, 0 ≤ S.mu p.1 p.2)
    (hsmall : ∀ p ∈ origDomain ui, a ≤ p.1 →
      |e| * S.r p.1 p.2 * ‖S.phi p.1 p.2‖ ≤ gapConstant / 128) :
    ∀ p ∈ origDomain ui, a ≤ p.1 → p.2 < 0 →
      gapConstant / 2 ≤ 1 - S.mu p.1 p.2 := by
  intro p hp hap hp0
  let g := fun q : ℝ × ℝ => 1 - S.mu q.1 q.2
  let H := apexMinimum g a
  have hab : a ≤ p.2 := hap.trans hp.2.2.1
  have hh := apex_minimum_compact_interval hS hia hab hp0
  have cg := ((continuousOn_const (c := (1 : ℝ))).sub (Gap.continuousOn_mu hS)).mono
    (triangle_subset_origDomain hia hp0)
  by_contra hfail
  have hlow : H p.2 < gapConstant / 2 :=
    (apexMinimum_le cg (show p ∈ triangle a p.2 from ⟨hap, hp.2.2.1, le_rfl⟩)).trans_lt
      (lt_of_not_ge hfail)
  have hlevel : gapConstant / 2 ∈ Icc (H p.2) (H a) := by
    refine ⟨hlow.le, ?_⟩
    change gapConstant / 2 ≤ apexMinimum g a a
    rw [hh.2.2.1]
    linarith only [gapConstant_bounds.2]
  obtain ⟨b, hb, he⟩ := intermediate_value_Icc' hab hh.1 hlevel
  change H b = gapConstant / 2 at he
  have hab' : a < b := by
    apply lt_of_le_of_ne hb.1
    intro hba
    have : H a = gapConstant / 2 := hba ▸ he
    rw [show H a = 1 from hh.2.2.1] at this
    linarith only [this, gapConstant_bounds.2]
  have hb0 := hb.2.trans_lt hp0
  have hs := triangle_subset_origDomain hia hb0
  have cb := ((continuousOn_const (c := (1 : ℝ))).sub (Gap.continuousOn_mu hS)).mono hs
  have hd : 0 < gapConstant / 2 ∧ gapConstant / 2 ≤ 1 := by
    constructor <;> linarith only [gapConstant_bounds.1, gapConstant_bounds.2]
  have himprove := Gap.conditional e a b (gapConstant / 2) S hab'
    (Local.isSolution_mono hS hs) hd (fun q hq => hmu q (hs hq))
    (fun q hq => by
      rw [← he]
      exact apexMinimum_le cb hq)
    (fun q hq => by
      simpa only [div_div, show (2 : ℝ) * 64 = 128 by norm_num] using hsmall q (hs hq) hq.1)
  have hmin : gapConstant ≤ H b := le_apexMinimum hb.1 cb himprove
  rw [he] at hmin
  linarith only [hmin, gapConstant_bounds.1]

/-- [internal]
The proved interior gap passes to the positive-radius terminal point by
continuity on its proper outgoing row. Nothing is asserted at `(0,0)`.
The supplied lower bound is uniform in the terminal label. -/
theorem terminal_cone_gap_extension_of_interior {ui e a δ : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui))
    (hgap : ∀ p ∈ origDomain ui, a ≤ p.1 → p.2 < 0 → δ ≤ 1 - S.mu p.1 p.2)
    {u : ℝ} (hui : ui ≤ u) (hu : u < 0) (hau : a ≤ u) :
    δ ≤ 1 - S.mu u 0 := by
  have hs : outSeg u u 0 ⊆ origDomain ui :=
    (outSeg_axis_subset_origDomain_iff hu.le).2 ⟨hui, hu, le_rfl⟩
  have cg : ContinuousOn (fun v => 1 - S.mu u v) (Icc u 0) :=
    continuousOn_const.sub (Calculus.continuousOn_out_section (Gap.continuousOn_mu hS) hs)
  apply le_on_closure (s := Ioo u 0)
    (fun v hv => hgap (u, v) (hs ⟨rfl, hv.1.le, hv.2.le⟩) hau hv.2)
  · exact continuousOn_const
  · simpa only [closure_Ioo hu.ne] using cg
  · rw [closure_Ioo hu.ne]
    exact ⟨hu.le, le_rfl⟩

/-- [node prop:charged-late-gap#terminal-cone-gap-extension]
The optical bound and terminal-size convergence give one late entry for
every proper terminal-cone point (charged_SF_new_version.tex:L1779). The gap constant
is universal; the entry may depend on the fixed development, coupling,
optical bound and size convergence, uniformly in every later entry. -/
theorem terminal_cone_gap_extension {ui e Λ : ℝ} {S : Fields} (hui : ui < 0)
    (hS : IsSolution e S (origDomain ui))
    (hmu : ∀ p ∈ origDomain ui, 0 ≤ S.mu p.1 p.2)
    (hopt : ∀ p ∈ origDomain ui, S.lam p.1 p.2 / (1 - S.mu p.1 p.2) ≤ Λ)
    (hsize : Tendsto (fun u => S.r u 0 * ‖S.phi u 0‖ +
      Real.sqrt (2 * Λ * S.m u 0 * (-u))) (𝓝[<] 0) (𝓝 0)) :
    ∃ a ∈ Ioo ui 0, ∀ a' ∈ Ico a 0, ∀ u ∈ Ico a' 0,
      gapConstant / 2 ≤ 1 - S.mu u 0 := by
  obtain ⟨a, ha, hsmall⟩ := late_time_choice hui hS hopt hsize
  have hg := first_apex_gap_contradiction_of_smallness hS ha.1.le ha.2 hmu hsmall
  refine ⟨a, ha, ?_⟩
  intro a' ha' u hu
  exact terminal_cone_gap_extension_of_interior hS hg
    (ha.1.le.trans (ha'.1.trans hu.1)) hu.2 (ha'.1.trans hu.1)

end LateGap

/-- [node prop:charged-late-gap]
The source proposition with its finite optical and terminal-size premises.
One entry label works for every later entry and every original point,
including proper terminal-cone points. The literal gap is universal; the
entry label may depend on the development, coupling and size convergence. -/
theorem charged_late_gap (ui e Λ : ℝ) (S : Fields) (hui : ui < 0)
    (hS : IsSolution e S (origDomain ui))
    (hmu : ∀ p ∈ origDomain ui, 0 ≤ S.mu p.1 p.2)
    (hopt : ∀ p ∈ origDomain ui, S.lam p.1 p.2 / (1 - S.mu p.1 p.2) ≤ Λ)
    (hsize : Tendsto (fun u => S.r u 0 * ‖S.phi u 0‖ +
      Real.sqrt (2 * Λ * S.m u 0 * (-u))) (𝓝[<] 0) (𝓝 0)) :
    ∃ a ∈ Ioo ui 0, ∀ p ∈ origDomain ui, a ≤ p.1 →
      gapConstant / 2 ≤ 1 - S.mu p.1 p.2 := by
  obtain ⟨a, ha, hsmall⟩ := LateGap.late_time_choice hui hS hopt hsize
  have hgap := LateGap.first_apex_gap_contradiction_of_smallness hS ha.1.le ha.2 hmu hsmall
  refine ⟨a, ha, ?_⟩
  intro p hp hap
  rcases hp.2.2.2.eq_or_lt with hp0 | hp0
  · have he : p.2 = 0 := hp0
    simpa only [he] using LateGap.terminal_cone_gap_extension_of_interior hS hgap hp.1 hp.2.1 hap
  · exact hgap p hp hap hp0

end EmcsfAcExtension.Global
