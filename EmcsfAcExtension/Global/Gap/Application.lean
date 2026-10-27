module

public import EmcsfAcExtension.Global.Gap.Late
import EmcsfAcExtension.Global.Gap.Radial
import EmcsfAcExtension.Global.Api.Domains

/-! # Applying the late gap to terminal-proposition outputs

The `_of_terminal` helpers expose the pending terminal estimates explicitly.
Their unconditional wrappers are supplied after internal project record lands. The geometric
late-gap proposition itself is proved in `Late`, with its source premises.
Source: charged_SF_new_version.tex:L1818–1829; approved internal project record.
-/

public section

open Set Filter Topology

namespace EmcsfAcExtension.Global.Gap

private theorem terminal_mass_bounds {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) {u : ℝ} (hu : u ∈ Ico ui 0) :
    0 ≤ S.m u 0 ∧ S.m u 0 ≤ S.r u 0 / 2 := by
  have hp : (u, 0) ∈ origDomain ui := ⟨hu.1, hu.2, hu.2.le, le_rfl⟩
  have hr := h.solution.r_pos (u, 0) hp hu.2
  have hμ := h.mu (u, 0) hp
  change 0 ≤ 2 * S.m u 0 / S.r u 0 ∧ 2 * S.m u 0 / S.r u 0 < 1 at hμ
  have hlo := (le_div_iff₀ hr).mp hμ.1
  have hhi := (div_lt_iff₀ hr).mp hμ.2
  constructor <;> linarith only [hlo, hhi]

/-- [internal]
Supports `sec:charged-gap#terminal-hypothesis-estimates` from internal project record outputs.
The terminal proposition's radius limit and logarithmic scalar estimate,
together with the original nontrapped mass bound, give the exact inputs to
the size bridge. The scalar constant and positive reference radius depend
on the fixed development and terminal bound, uniformly in the label.
This helper's terminal premises are discharged by the pending internal project record wrapper. -/
theorem terminal_hypothesis_estimates_of_terminal (ui e : ℝ) (S : Fields)
    (h : OriginalData ui e S)
    (hR : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hlog : ∃ C : ℝ, 0 < C ∧ ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) :
    Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0) ∧
      (∀ u ∈ Ico ui 0, 0 ≤ S.m u 0 ∧ S.m u 0 ≤ S.r u 0 / 2) ∧
      ∃ Rstar C : ℝ, 0 < Rstar ∧ 0 < C ∧
        ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
          C * (1 + Real.sqrt (Real.log (Rstar / S.r u 0))) := by
  obtain ⟨C, hC, hClog⟩ := hlog
  have hp : (ui, 0) ∈ origDomain ui := ⟨le_rfl, h.ui_neg, h.ui_neg.le, le_rfl⟩
  exact ⟨hR, fun _ hu => terminal_mass_bounds h hu,
    S.r ui 0, C, h.solution.r_pos _ hp h.ui_neg, hC, hClog⟩

private theorem sqrt_le_one_add_abs (t : ℝ) : Real.sqrt t ≤ 1 + |t| := by
  have hs := Real.sq_sqrt (abs_nonneg t)
  have hn := sq_nonneg (Real.sqrt |t| - 1)
  have hb : Real.sqrt |t| ≤ 1 + |t| := by nlinarith only [hs, hn, abs_nonneg t]
  exact (Real.sqrt_le_sqrt (le_abs_self t)).trans hb

/-- [internal] A shrinking positive radius times a scalar with the terminal
logarithmic bound tends to zero. The positive reference radius and scalar
constant are fixed before taking the limit; no uniform convergence rate is
claimed over developments. -/
theorem terminal_scalar_size_of_log_bound {ui e Rstar C : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hRstar : 0 < Rstar) (hC : 0 < C)
    (hR : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hlog : ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (Rstar / S.r u 0)))) :
    Tendsto (fun u => S.r u 0 * ‖S.phi u 0‖) (𝓝[<] 0) (𝓝 0) := by
  have hlabel : ∀ᶠ u : ℝ in 𝓝[<] 0, u ∈ Ico ui 0 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds h.ui_neg)]
      with u hu hui
    exact ⟨hui.le, hu⟩
  have hmulLog : Tendsto (fun u => S.r u 0 * Real.log (S.r u 0)) (𝓝[<] 0) (𝓝 0) := by
    simpa only [Function.comp_def, zero_mul] using (Real.continuous_mul_log.tendsto 0).comp hR
  have hratioLog : Tendsto (fun u => S.r u 0 * Real.log (Rstar / S.r u 0))
      (𝓝[<] 0) (𝓝 0) := by
    have ht := (hR.mul_const (Real.log Rstar)).sub hmulLog
    simp only [zero_mul, sub_zero] at ht
    apply ht.congr'
    filter_upwards [hlabel] with u hu
    have hr := h.solution.r_pos (u, 0) ⟨hu.1, hu.2, hu.2.le, le_rfl⟩ hu.2
    rw [Real.log_div hRstar.ne' hr.ne', mul_sub]
  have hupper : Tendsto (fun u => C *
      (2 * S.r u 0 + |S.r u 0 * Real.log (Rstar / S.r u 0)|)) (𝓝[<] 0) (𝓝 0) := by
    simpa only [mul_zero, abs_zero, add_zero] using
      ((hR.const_mul 2).add hratioLog.abs).const_mul C
  apply squeeze_zero' ?_ ?_ hupper
  · filter_upwards [hlabel] with u hu
    exact mul_nonneg (h.solution.r_pos (u, 0) ⟨hu.1, hu.2, hu.2.le, le_rfl⟩ hu.2).le
      (norm_nonneg _)
  · filter_upwards [hlabel] with u hu
    have hr := h.solution.r_pos (u, 0) ⟨hu.1, hu.2, hu.2.le, le_rfl⟩ hu.2
    calc
      _ ≤ S.r u 0 * (C * (1 + Real.sqrt (Real.log (Rstar / S.r u 0)))) :=
        mul_le_mul_of_nonneg_left (hlog u hu) hr.le
      _ ≤ S.r u 0 * (C * (1 + (1 + |Real.log (Rstar / S.r u 0)|))) := by
        gcongr
        exact sqrt_le_one_add_abs _
      _ = _ := by rw [abs_mul, abs_of_pos hr]; ring

/-- [internal]
Supports `sec:charged-gap#terminal-estimates-imply-size` from internal project record outputs.
The terminal radius and logarithmic scalar outputs imply the full source
size limit, retaining its mass and label factors. The real optical constant
is fixed before the limit; no uniform convergence rate is asserted.
The explicit terminal outputs are awaiting their internal project record consumer. -/
theorem terminal_estimates_imply_size_of_terminal (ui e Λ : ℝ) (S : Fields)
    (h : OriginalData ui e S)
    (hR : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hlog : ∃ C : ℝ, 0 < C ∧ ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) :
    Tendsto (fun u => S.r u 0 * ‖S.phi u 0‖ +
      Real.sqrt (2 * Λ * S.m u 0 * (-u))) (𝓝[<] 0) (𝓝 0) := by
  obtain ⟨_, hmass, Rstar, C, hRstar, hC, hClog⟩ :=
    terminal_hypothesis_estimates_of_terminal ui e S h hR hlog
  have hlabel : ∀ᶠ u : ℝ in 𝓝[<] 0, u ∈ Ico ui 0 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds h.ui_neg)]
      with u hu hui
    exact ⟨hui.le, hu⟩
  have hM : Tendsto (fun u => S.m u 0) (𝓝[<] 0) (𝓝 0) := by
    apply squeeze_zero' (hlabel.mono (fun u hu => (hmass u hu).1))
      (hlabel.mono (fun u hu => (hmass u hu).2))
    simpa only [zero_div] using hR.div_const 2
  have ht : Tendsto (fun u : ℝ => -u) (𝓝[<] 0) (𝓝 0) := by
    have hid : Tendsto (fun u : ℝ => u) (𝓝[<] 0) (𝓝 0) :=
      (continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    simpa only [neg_zero] using hid.neg
  have hsqrt := ((hM.const_mul (2 * Λ)).mul ht).sqrt
  simpa only [mul_zero, Real.sqrt_zero, add_zero] using
    (terminal_scalar_size_of_log_bound h hRstar hC hR hClog).add hsqrt

/-- [internal] An optical bound at off-axis points passes to the existing
axis by outgoing continuity. The supplied bound remains uniform on the
whole original development; no terminal assumption is used. -/
theorem optical_upper_of_off_axis {ui e Λ : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui))
    (hopt : ∀ p ∈ origDomain ui, p.1 < p.2 →
      S.lam p.1 p.2 / (1 - S.mu p.1 p.2) ≤ Λ) :
    ∀ p ∈ origDomain ui, S.lam p.1 p.2 / (1 - S.mu p.1 p.2) ≤ Λ := by
  intro p hp
  have hs : outSeg p.1 p.1 0 ⊆ origDomain ui :=
    (outSeg_axis_subset_origDomain_iff hp.2.1.le).2 ⟨hp.1, hp.2.1, le_rfl⟩
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have cg : ContinuousOn (fun v => 1 - S.mu p.1 v) (Icc p.1 0) :=
    continuousOn_const.sub (Calculus.continuousOn_out_section (continuousOn_mu hS) hs)
  have cc : ContinuousOn (fun v => S.lam p.1 v / (1 - S.mu p.1 v)) (Icc p.1 0) :=
    cl.div cg (fun v hv => (hS.one_sub_mu_pos (p.1, v) (hs ⟨rfl, hv⟩)).ne')
  apply le_on_closure (s := Ioo p.1 0)
    (fun v hv => hopt (p.1, v) (hs ⟨rfl, hv.1.le, hv.2.le⟩) hv.1)
  · simpa only [closure_Ioo hp.2.1.ne] using cc
  · exact continuousOn_const
  · rw [closure_Ioo hp.2.1.ne]
    exact ⟨hp.2.2.1, hp.2.2.2⟩

/-- [internal]
Supports `sec:charged-gap#late-gap-application` from internal project record outputs.
The terminal outputs discharge both quantitative premises of the late-gap
proposition. The same late entry also gives the charge bound needed by the
architecture. The literal gap is universal; the entry and optical/scalar
constants may depend on the fixed development and terminal bound, uniformly
in both point labels. The pending internal project record wrapper supplies `hR`, `hlog`, `hopt`. -/
theorem late_gap_application_of_terminal (ui e Λ : ℝ) (S : Fields)
    (h : OriginalData ui e S)
    (hR : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hlog : ∃ C : ℝ, 0 < C ∧ ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0))))
    (hopt : ∀ p ∈ origDomain ui, p.1 < p.2 →
      S.lam p.1 p.2 / (1 - S.mu p.1 p.2) ≤ Λ) :
    ∃ a ∈ Ioo ui 0, ∀ p ∈ origDomain ui, a ≤ p.1 →
      gapConstant / 2 ≤ 1 - S.mu p.1 p.2 ∧
        S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 ≤ S.mu p.1 p.2 / 2 := by
  have hsize := terminal_estimates_imply_size_of_terminal ui e Λ S h hR hlog
  have hopt' := optical_upper_of_off_axis h.solution hopt
  obtain ⟨a, ha, hgap⟩ := charged_late_gap ui e Λ S h.ui_neg h.solution
    (fun p hp => (h.mu p hp).1) hopt' hsize
  obtain ⟨b, hb, hsmall⟩ := LateGap.late_time_choice h.ui_neg h.solution hopt' hsize
  let c := max a b
  have hc : c ∈ Ioo ui 0 := ⟨ha.1.trans_le (le_max_left _ _), max_lt ha.2 hb.2⟩
  refine ⟨c, hc, ?_⟩
  intro p hp hcp
  have hap := (le_max_left a b).trans hcp
  have hbp := (le_max_right a b).trans hcp
  refine ⟨hgap p hp hap, ?_⟩
  rcases hp.2.2.1.eq_or_lt with huv | huv
  · rw [← huv]
    have haxis := h.solution.axis p.1
      (show (p.1, p.1) ∈ origDomain ui from ⟨hp.1, hp.2.1, le_rfl, hp.2.1.le⟩)
    simp [Fields.mu, haxis.1]
  · have hs : outSeg p.1 p.1 p.2 ⊆ origDomain ui :=
      (outSeg_axis_subset_origDomain_iff hp.2.2.1).2 ⟨hp.1, hp.2.1, hp.2.2.2⟩
    have hd : 0 < gapConstant / 2 ∧ gapConstant / 2 ≤ 1 := by
      constructor <;> linarith only [LateGap.gapConstant_bounds.1, LateGap.gapConstant_bounds.2]
    have hcharge := (relative_charge h.solution huv hs hd (h.mu p hp).1
      (fun v hv => hgap (p.1, v) (hs ⟨rfl, hv⟩) hap)
      (fun v hv => by
        simpa only [div_div, show (2 : ℝ) * 64 = 128 by norm_num] using
          hsmall (p.1, v) (hs ⟨rfl, hv⟩) hbp)).1
    exact hcharge.trans (by
      have hc' := mul_le_mul_of_nonneg_right (show (gapConstant / 2) / 4096 ≤ 1 / 2 by
        linarith only [LateGap.gapConstant_bounds.2]) (h.mu p hp).1
      simpa only [one_div, inv_mul_eq_div] using hc')

/-- [internal] Architecture §3's late-gap and relative-charge interface with
the pending terminal outputs explicit. Its consumer supplies them from
`Terminal.hypotheses` and the global optical bound after internal project record lands. -/
theorem late_from_terminal_of_terminal (ui e Λ : ℝ) (S : Fields)
    (h : OriginalData ui e S)
    (hR : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hlog : ∃ C : ℝ, 0 < C ∧ ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0))))
    (hopt : ∀ p ∈ origDomain ui, p.1 < p.2 →
      S.lam p.1 p.2 / (1 - S.mu p.1 p.2) ≤ Λ) :
    ∃ a ∈ Ioo ui 0, ∀ p ∈ origDomain ui, a ≤ p.1 →
      gapConstant / 2 ≤ 1 - S.mu p.1 p.2 ∧
        S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 ≤ S.mu p.1 p.2 / 2 :=
  late_gap_application_of_terminal ui e Λ S h hR hlog hopt

end EmcsfAcExtension.Global.Gap
