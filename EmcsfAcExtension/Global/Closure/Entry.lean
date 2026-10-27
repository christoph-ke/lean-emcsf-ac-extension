module

public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Stages
public import EmcsfAcExtension.Global.Defs.Domains
public import EmcsfAcExtension.Global.Defs.Interaction
public import EmcsfAcExtension.Global.Defs.Curves
public import EmcsfAcExtension.Global.Defs.Observation
public import EmcsfAcExtension.Global.Closure.Parameters
import EmcsfAcExtension.Global.Exterior.Assembly
import EmcsfAcExtension.Global.Terminal.Hypotheses
import EmcsfAcExtension.Global.Terminal.OpticalUpper
import EmcsfAcExtension.Global.Gap.Application
import EmcsfAcExtension.Global.Gap.LateMain
import EmcsfAcExtension.Global.Exterior.ScalarEnergy
import EmcsfAcExtension.Global.Interaction.RadialY
import EmcsfAcExtension.Local.Calculus.Sections
import EmcsfAcExtension.Infra.Sequence.EnergyRecurrence

/-! # Late geometry and the charged entry scale

The terminal, gap and adaptive exterior results supply one eventual entry
family, its proper L¹ density, and all strict initialization margins. The
logarithmic coefficient also includes stopped radial reconstruction and is
fixed before the entry row. No future stage is assumed to exist.
Source: charged_SF_new_version.tex:L3847–L3898.
-/

public section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.Closure

/-- [def-node sec:charged-closure#entry-data]
The actual entry data, charged_SF_new_version.tex:L3872–L3877. The terminal and
adaptive radii are identified before the outgoing entry label; `D₀` is
the shared nonnegative interaction integral, without a `toReal` cast. -/
structure EntryData (S : Fields) (ell : ℝ → ℝ) (u₀ v₀ : ℝ) where
  /-- Terminal radius of the entry row. -/
  R₀ : ℝ
  /-- Adaptive cylinder radius. -/
  b₀ : ℝ
  /-- Initial interaction. -/
  D₀ : ℝ≥0∞
  /-- Source definition of the terminal radius. -/
  terminal_radius : R₀ = S.r u₀ 0
  /-- Source definition of the adaptive radius. -/
  adaptive_radius : b₀ = ell R₀
  /-- The outgoing label is the actual cylinder entry. -/
  entry_label : S.r u₀ v₀ = b₀
  /-- Source definition of the initial interaction. -/
  interaction : D₀ = initialInteraction S u₀ v₀

/-- [internal] Construct the canonical entry package from the actual
adaptive-frontier identity. No independent radius or interaction is chosen. -/
@[expose] noncomputable def entryData (S : Fields) (ell : ℝ → ℝ) (u₀ v₀ : ℝ)
    (hroot : S.r u₀ v₀ = ell (S.r u₀ 0)) : EntryData S ell u₀ v₀ :=
  ⟨S.r u₀ 0, ell (S.r u₀ 0), initialInteraction S u₀ v₀, rfl, rfl, hroot, rfl⟩

/-- [internal] Identify the shared nonnegative entry interaction with the
paper's real integral, charged_SF_new_version.tex:L3872–L3877. The proper-row consumer
must supply integrability of its actual weighted density. No finiteness of
a lintegral is assumed through an unguarded `toReal` conversion. -/
theorem initialInteraction_eq_of_integrable (S : Fields) (u₀ v₀ : ℝ) (hv : v₀ ≤ 0)
    (hi : IntervalIntegrable (weightedJ S u₀) volume v₀ 0) :
    initialInteraction S u₀ v₀ = ENNReal.ofReal (∫ v in v₀..0, ‖weightedJ S u₀ v‖) := by
  have hI : IntegrableOn (weightedJ S u₀) (Icc v₀ 0) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hv).mp hi
  unfold initialInteraction
  rw [intervalIntegral.integral_of_le hv, restrict_Ioc_eq_restrict_Icc]
  exact (ofReal_integral_norm_eq_lintegral_enorm hI).symm

/-- [internal] Bridge internal project record (internal project record). On a proper
outgoing row the normalized source is L¹; multiplication by the continuous,
nonzero expansion gives L¹ of the actual weighted density. -/
theorem weightedJ_intervalIntegrable {e u a : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hua : u < a) (ha : a ≤ 0)
    (hs : outSeg u a 0 ⊆ D) : IntervalIntegrable (weightedJ S u) volume a 0 := by
  have hi := Interaction.radial_y_source_integrable hS hua ha hs
  have hc : ContinuousOn (fun v => (S.lam u v : ℂ)) (uIcc a 0) := by
    rw [uIcc_of_le ha]
    exact Complex.continuous_ofReal.comp_continuousOn
      (Calculus.continuousOn_out_section hS.cont_lam hs)
  apply (hi.mul_continuousOn hc).congr
  intro v hv
  have hv' : v ∈ Icc a 0 := by
    simpa only [uIcc_of_le ha] using (uIoc_subset_uIcc hv)
  have hn := Complex.ofReal_ne_zero.mpr (hS.lam_pos (u, v) (hs ⟨rfl, hv'⟩)).ne'
  field_simp

/-- [internal] The entry integral has its real source formula on every
proper row, directly from the frozen solution class; no L¹ premise remains. -/
theorem initialInteraction_eq {e u a : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hua : u < a) (ha : a ≤ 0)
    (hs : outSeg u a 0 ⊆ D) :
    initialInteraction S u a = ENNReal.ofReal (∫ v in a..0, ‖weightedJ S u v‖) :=
  initialInteraction_eq_of_integrable S u a ha (weightedJ_intervalIntegrable hS hua ha hs)

/-- [internal] At the initial cutoff the source history has zero incoming
length, independently of any integrability or stopped-estimate hypothesis.
This is the `J = D₀` initialization in approved internal project record. -/
theorem interactionNorm_initial_cutoff (ui e u₀ v₀ : ℝ) (S : Fields) (vb : ℝ → ℝ) :
    interactionNorm e S (exteriorDomain ui u₀ u₀ vb) u₀ v₀ =
      initialInteraction S u₀ v₀ := by
  have hzero (v : ℝ) : volume {u | (u, v) ∈ exteriorDomain ui u₀ u₀ vb} = 0 := by
    apply measure_mono_null (t := {u₀}) _ (measure_singleton u₀)
    intro u hu
    exact Set.mem_singleton_iff.mpr (le_antisymm hu.2.2.1 hu.2.1)
  have heq (v : ℝ) : incomingEnvelope e S (exteriorDomain ui u₀ u₀ vb) u₀ v =
      ‖weightedJ S u₀ v‖ₑ := by
    simp only [incomingEnvelope, setLIntegral_measure_zero _ _ (hzero v), add_zero]
  simp only [interactionNorm, heq, initialInteraction]

/-- [node sec:charged-closure#late-geometry]
The late original triangle has the fixed universal half-gap and nonnegative
signed radial coefficient, charged_SF_new_version.tex:L3847–L3853. The entry label may
depend on the development and signed terminal bound; the gap does not. -/
theorem late_geometry (ui e : ℝ) (S : Fields) (h : OriginalData ui e S)
    (hs : SignedTerminalBound ui S) :
    0 < gapConstant / 2 ∧ ∃ u₀ ∈ Ioo ui 0, ∀ p ∈ origDomain ui, u₀ ≤ p.1 →
      0 ≤ S.mu p.1 p.2 - S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 ∧
      S.mu p.1 p.2 - S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 ≤ S.mu p.1 p.2 ∧
      gapConstant / 2 ≤ 1 - S.mu p.1 p.2 := by
  obtain ⟨δ, K, lam₀, _, hK, _, _, _, _, hR, _, _, hlog⟩ :=
    (Terminal.hypotheses ui e S h).2 hs
  obtain ⟨Λ, _, hopt, _⟩ := Terminal.lambda_gap_upper h.ui_neg h.solution h.mu
  obtain ⟨u₀, hu₀, hlate⟩ := Gap.late_from_terminal_of_terminal ui e Λ S h hR
    ⟨K, hK, hlog⟩ hopt
  refine ⟨half_pos LateGap.gapConstant_bounds.1, u₀, hu₀, ?_⟩
  intro p hp hu
  have hq := hlate p hp hu
  have hmu := (h.mu p hp).1
  have hnonneg : 0 ≤ S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 :=
    div_nonneg (sq_nonneg _) (sq_nonneg _)
  exact ⟨by linarith only [hq.2, hmu], sub_le_self _ hnonneg, hq.1⟩

/-- [internal] The logarithmic envelope on a radius-halving interval.
The coefficient depends only on the terminal scalar coefficient `K` and
the positive reference radius `Ri`, not on the entry radius `R₀`. -/
theorem logarithmic_envelope_on_halving {Ri R₀ R K : ℝ}
    (hi : 0 < Ri) (h₀ : 0 < R₀) (h₀i : R₀ ≤ Ri) (hR : R₀ / 2 ≤ R)
    (hK : 0 ≤ K) :
    K * (1 + Real.sqrt (Real.log (Ri / R))) ≤
      K * (2 + Real.sqrt (Real.log 2)) * (1 + Real.sqrt (Real.log (Ri / R₀))) := by
  have hr : 0 < R := (half_pos h₀).trans_le hR
  have hL : 0 ≤ Real.log (Ri / R₀) := Real.log_nonneg ((one_le_div h₀).2 h₀i)
  have h2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hratio : Ri / R ≤ 2 * (Ri / R₀) := by
    apply (div_le_iff₀ hr).2
    have hh := mul_le_mul_of_nonneg_left hR (div_nonneg hi.le h₀.le)
    have heq : (Ri / R₀) * (R₀ / 2) = Ri / 2 := by field_simp
    rw [heq] at hh
    nlinarith only [hh]
  have hlog : Real.log (Ri / R) ≤ Real.log (Ri / R₀) + Real.log 2 := by
    have hh := Real.log_le_log (div_pos hi hr) hratio
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (div_ne_zero hi.ne' h₀.ne')] at hh
    linarith only [hh]
  have hroot : Real.sqrt (Real.log (Ri / R)) ≤
      Real.sqrt (Real.log (Ri / R₀)) + Real.sqrt (Real.log 2) := by
    have hh := sqrt_le_of_le_quadratic (q := 1) (C := Real.log 2)
      (a := Real.log (Ri / R₀)) (s := 1) (by norm_num) h2 hL (by norm_num)
      (by simpa only [one_mul, one_pow, mul_one] using hlog)
    simpa only [Real.sqrt_one, one_mul, mul_one] using hh
  have hproduct : 1 + Real.sqrt (Real.log (Ri / R₀)) + Real.sqrt (Real.log 2) ≤
      (2 + Real.sqrt (Real.log 2)) * (1 + Real.sqrt (Real.log (Ri / R₀))) := by
    have hp := mul_nonneg (Real.sqrt_nonneg (Real.log 2))
      (Real.sqrt_nonneg (Real.log (Ri / R₀)))
    nlinarith only [hp, Real.sqrt_nonneg (Real.log (Ri / R₀))]
  calc
    _ ≤ K * (1 + Real.sqrt (Real.log (Ri / R₀)) + Real.sqrt (Real.log 2)) := by
      exact mul_le_mul_of_nonneg_left (by linarith only [hroot]) hK
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hproduct hK

/-- [internal] The terminal part of the amplitude-scale node at
charged_SF_new_version.tex:L3888–L3895. `C` is chosen after the fixed development and a
fixed enlargement `A`, before every entry row and radius-halving interval.
The stopped exterior radial-reconstruction part of that node is still a
separate obligation; it is not assumed here. -/
theorem terminal_amplitude_scale (ui e A : ℝ) (S : Fields) (h : OriginalData ui e S)
    (hs : SignedTerminalBound ui S) :
    ∃ C : ℝ, 0 < C ∧ A ≤ C ∧ ∀ u₀ ∈ Ico ui 0,
      1 ≤ C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u₀ 0))) ∧
      ∀ u ∈ Ico ui 0, S.r u₀ 0 / 2 ≤ S.r u 0 →
        ‖S.phi u 0‖ ≤ C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u₀ 0))) := by
  obtain ⟨δ, K, lam₀, _, hK, _, _, _, _, _, _, _, hlog⟩ :=
    (Terminal.hypotheses ui e S h).2 hs
  let C := max A (1 + K * (2 + Real.sqrt (Real.log 2)))
  have hterm : 0 ≤ K * (2 + Real.sqrt (Real.log 2)) := by positivity
  have hC1 : 1 ≤ C := (by linarith only [hterm] : 1 ≤
    1 + K * (2 + Real.sqrt (Real.log 2))).trans (le_max_right _ _)
  refine ⟨C, zero_lt_one.trans_le hC1, le_max_left _ _, ?_⟩
  intro u₀ hu₀
  have hfac : 1 ≤ 1 + Real.sqrt (Real.log (S.r ui 0 / S.r u₀ 0)) :=
    le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hM : 1 ≤ C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u₀ 0))) := by
    simpa only [one_mul] using mul_le_mul hC1 hfac (by norm_num : (0 : ℝ) ≤ 1)
      (zero_lt_one.trans_le hC1).le
  refine ⟨hM, ?_⟩
  intro u hu hhalf
  have hi := h.solution.r_pos (ui, 0) ⟨le_rfl, h.ui_neg, h.ui_neg.le, le_rfl⟩ h.ui_neg
  have h₀ := h.solution.r_pos (u₀, 0) ⟨hu₀.1, hu₀.2, hu₀.2.le, le_rfl⟩ hu₀.2
  have h₀i := (Terminal.terminal_radius_strictAntiOn h.solution).antitoneOn
    ⟨le_rfl, h.ui_neg⟩ hu₀ hu₀.1
  calc
    _ ≤ K * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0))) := hlog u hu
    _ ≤ K * (2 + Real.sqrt (Real.log 2)) *
        (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u₀ 0))) :=
      logarithmic_envelope_on_halving hi h₀ h₀i hhalf hK.le
    _ ≤ _ := mul_le_mul_of_nonneg_right
      ((by linarith only [hterm] : K * (2 + Real.sqrt (Real.log 2)) ≤
        1 + K * (2 + Real.sqrt (Real.log 2))).trans (le_max_right _ _)) (by positivity)

/-- [node eq:cc-entry]
One adaptive entry family supplies the energy limit, the real initial
interaction limit, and the radius-to-energy ratio limit. The positive
expansion margin and global upper bound depend on the fixed development;
the profile is fixed before every entry tolerance and row. All weak scalar
and mass tolerances may then be imposed simultaneously on that same row.
Source: charged_SF_new_version.tex:L3872–L3886. -/
theorem _root_.EmcsfAcExtension.Global.cc_entry (ui e : ℝ) (S : Fields) (h : OriginalData ui e S)
    (hs : SignedTerminalBound ui S) :
    ∃ ell V : ℝ → ℝ, ∃ a ∈ Ioo ui 0, ∃ c > 0, ∃ Λ > 0,
      c ≤ Λ ∧ (∀ p ∈ origDomain ui, S.lam p.1 p.2 ≤ Λ) ∧
      (∀ u ∈ Ico a 0, u < V u ∧ V u < 0 ∧
        S.r u (V u) = ell (S.r u 0)) ∧
      Tendsto (fun u => ∫ v in V u..0, ‖weightedJ S u v‖) (𝓝[<] 0) (𝓝 0) ∧
      (∀ εentry > 0, Tendsto (fun u => ell (S.r u 0) / (εentry * S.r u 0))
        (𝓝[<] 0) (𝓝 0)) ∧
      Tendsto (fun u => cylinderEnergy S (ell (S.r u 0)) u (V u) / ell (S.r u 0))
        (𝓝[<] 0) (𝓝 0) ∧
      ∀ F > 0, ∀ ε > 0, ∀ᶠ u in 𝓝[<] (0 : ℝ), ∀ v ∈ Icc (V u) 0,
        2 * c < S.lam u v ∧ S.lam u v ≤ Λ ∧
        ‖S.theta u v / (S.lam u v : ℂ)‖ < F ∧
        S.mu u v / (1 - S.mu u v) < ε := by
  obtain ⟨M, _, _, _, lam₀, hlam₀, hlimit, hext⟩ := Exterior.main h hs
  obtain ⟨ell, Ri, _, _, _, _, _, hellsmall, _, _, a, ha, V, _, _, hroot,
    _, _, _, _, _, _, _, _, hfield, hopt, hmu, htail⟩ := hext (1 / 16) (by norm_num)
  obtain ⟨Λ, hΛ, _, hupper⟩ := Terminal.lambda_gap_upper h.ui_neg h.solution h.mu
  have hlamΛ : lam₀ ≤ Λ := le_of_tendsto hlimit (by
    filter_upwards [Ioo_mem_nhdsLT h.ui_neg] with u hu
    exact hupper (u, 0) ⟨hu.1.le, hu.2, hu.2.le, le_rfl⟩)
  have hcΛ : lam₀ / 4 ≤ Λ := (show lam₀ / 4 ≤ lam₀ by linarith only [hlam₀]).trans hlamΛ
  have hlabel : ∀ᶠ u : ℝ in 𝓝[<] 0, u ∈ Ico a 0 := by
    have hi : ∀ᶠ u : ℝ in 𝓝[<] 0, u ∈ Ioo a 0 := Ioo_mem_nhdsLT ha.2
    exact hi.mono fun _ hu => ⟨hu.1.le, hu.2⟩
  have hmem (u : ℝ) (hu : u ∈ Ico a 0) (v : ℝ) (hv : v ∈ Icc (V u) 0) :
      (u, v) ∈ origDomain ui :=
    ⟨ha.1.le.trans hu.1, hu.2, (hroot u hu).1.le.trans hv.1, hv.2⟩
  have hextmem (u : ℝ) (hu : u ∈ Ico a 0) (v : ℝ) (hv : v ∈ Icc (V u) 0) :
      (u, v) ∈ adaptiveExterior S ui a ell := by
    refine ⟨hmem u hu v hv, hu.1, ?_⟩
    rw [← (hroot u hu).2.2]
    exact (Exterior.outgoing_radius_strictMono h ⟨ha.1.le.trans hu.1, hu.2⟩).monotoneOn
      ⟨(hroot u hu).1.le, (hroot u hu).2.1.le⟩
      ⟨(hroot u hu).1.le.trans hv.1, hv.2⟩ hv.1
  have hμlim : Tendsto (fun u => S.mu u (V u)) (𝓝[<] 0) (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    obtain ⟨d, hd, hsmall⟩ := hmu (η / 2) (half_pos hη)
    filter_upwards [hlabel, Ioo_mem_nhdsLT hd.2] with u hu hud
    have hp := hextmem u hu (V u) ⟨le_rfl, (hroot u hu).2.1.le⟩
    have hm := hsmall (u, V u) ⟨hp.1, hud.1.le, hp.2.2⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (h.mu _ hp.1).1]
    exact hm.trans_lt (half_lt_self hη)
  have hxlim : Tendsto (fun u => ‖S.theta u (V u) / (S.lam u (V u) : ℂ)‖)
      (𝓝[<] 0) (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    filter_upwards [hlabel, hfield η hη] with u hu hf
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] using
      hf (V u) ⟨le_rfl, (hroot u hu).2.1.le⟩
  have henergy := ((hxlim.pow 2).sub
    ((tendsto_const_nhds.sub hμlim).log (by norm_num : (1 : ℝ) - 0 ≠ 0))).div_const 2
  have henergy' : Tendsto
      (fun u => cylinderEnergy S (ell (S.r u 0)) u (V u) / ell (S.r u 0))
      (𝓝[<] 0) (𝓝 0) := by
    have hnormal : Tendsto (fun u =>
        (‖S.theta u (V u) / (S.lam u (V u) : ℂ)‖ ^ 2 - Real.log (1 - S.mu u (V u))) / 2)
        (𝓝[<] 0) (𝓝 0) := by simpa using henergy
    apply hnormal.congr'
    filter_upwards [hlabel] with u hu
    have hr : 0 < ell (S.r u 0) := by
      rw [← (hroot u hu).2.2]
      exact h.solution.r_pos _ (hmem u hu (V u) ⟨le_rfl, (hroot u hu).2.1.le⟩)
        (hroot u hu).1
    dsimp only [cylinderEnergy]
    field_simp [hr.ne']
  obtain ⟨_, _, _, _, _, _, _, _, _, hR, _⟩ := (Terminal.hypotheses ui e S h).2 hs
  have hRp : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hR, ?_⟩
    filter_upwards [hlabel] with u hu
    exact h.solution.r_pos (u, 0) (hmem u hu 0 ⟨(hroot u hu).2.1.le, le_rfl⟩) hu.2
  have hratio (εentry : ℝ) (_he : 0 < εentry) :
      Tendsto (fun u => ell (S.r u 0) / (εentry * S.r u 0)) (𝓝[<] 0) (𝓝 0) := by
    simpa only [Function.comp_def, div_mul_eq_div_div, div_right_comm, zero_div] using
      (hellsmall.comp hRp).div_const εentry
  obtain ⟨_, _, _, _, _, _, _, _, _, hDlim⟩ := htail
  refine ⟨ell, V, a, ha, lam₀ / 4, by positivity, Λ, hΛ, hcΛ, hupper, hroot,
    ?_, hratio, henergy', ?_⟩
  · exact hDlim
  · intro F hF ε hε
    obtain ⟨d, hd, hoptical⟩ := hopt (lam₀ / 2) (half_pos hlam₀)
    obtain ⟨b, hb, hsmall⟩ := hmu (ε / (2 * (1 + ε))) (by positivity)
    filter_upwards [hlabel, Ioo_mem_nhdsLT hd.2, Ioo_mem_nhdsLT hb.2,
      hfield F hF] with u hu hud hub hf
    intro v hv
    have hp := hextmem u hu v hv
    have hl := (abs_lt.mp (hoptical (u, v) ⟨hp.1, hud.1.le, hp.2.2⟩).1).1
    have hm := hsmall (u, v) ⟨hp.1, hub.1.le, hp.2.2⟩
    refine ⟨by linarith only [hl, hlam₀], hupper _ hp.1, hf v hv, ?_⟩
    apply (div_lt_iff₀ (h.solution.one_sub_mu_pos _ hp.1)).mpr
    have hm' := (le_div_iff₀ (by positivity : 0 < 2 * (1 + ε))).mp hm
    nlinarith only [hm', hε]


/-- [node sec:charged-closure#amplitude-scale]
The terminal logarithmic bound includes the full stopped exterior radial
reconstruction. The coefficient depends only on the development and fixed
`c,F,Jstop`; it precedes the entry row, every radius-halving row, outgoing
label, density majorant and interval. No amplitude assumption is imposed
on the core. Source: charged_SF_new_version.tex:L3888–L3894, L3964–L4008. -/
theorem amplitude_scale (ui e c F Jstop : ℝ) (S : Fields)
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S)
    (hc : 0 < c) (hF : 0 ≤ F) (hF1 : F < 1) (hJstop : 0 ≤ Jstop) :
    ∃ C > 0, 1 ≤ C ∧ ∀ u₀ ∈ Ico ui 0,
      let M₀ := C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u₀ 0)))
      1 ≤ M₀ ∧ ∀ u ∈ Ico ui 0, S.r u₀ 0 / 2 ≤ S.r u 0 →
      ‖S.phi u 0‖ ≤ M₀ ∧ ∀ a : ℝ, u < a → a ≤ 0 →
      (∀ v ∈ Icc a 0, c ≤ S.lam u v) →
      (∀ v ∈ Icc a 0, ‖S.theta u v / (S.lam u v : ℂ)‖ ≤ F) →
      ∀ g : ℝ → ℝ, IntervalIntegrable g volume a 0 →
      (∀ᵐ v ∂volume.restrict (Icc a 0), ‖weightedJ S u v‖ ≤ g v) →
      (∫ v in a..0, g v) ≤ Jstop →
      ∀ v ∈ Icc a 0, ‖S.phi u v‖ ≤ M₀ := by
  let A := 1 + (F + c⁻¹ * Jstop) / (1 - F ^ 2)
  have hden : 0 < 1 - F ^ 2 := by
    nlinarith only [hF, hF1, sq_nonneg (F - 1)]
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  obtain ⟨B, hB, hAB, hterm⟩ := terminal_amplitude_scale ui e 1 S h hs
  let C := B + A
  have hC : 0 < C := add_pos_of_pos_of_nonneg hB hA
  have hC1 : 1 ≤ C := hAB.trans (le_add_of_nonneg_right hA)
  refine ⟨C, hC, hC1, ?_⟩
  intro u₀ hu₀
  let L := 1 + Real.sqrt (Real.log (S.r ui 0 / S.r u₀ 0))
  have hL : 1 ≤ L := le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hM : 1 ≤ C * L := by
    calc
      1 ≤ C * 1 := by simpa only [mul_one] using hC1
      _ ≤ C * L := mul_le_mul_of_nonneg_left hL hC.le
  refine ⟨hM, ?_⟩
  intro u hu hhalf
  refine ⟨((hterm u₀ hu₀).2 u hu hhalf).trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hA) (zero_le_one.trans hL)), ?_⟩
  intro a hua ha hl hy g hg hmajor hJ v hv
  have hseg : outSeg u a 0 ⊆ origDomain ui := by
    rintro ⟨x, y⟩ ⟨rfl, hy₁, hy₂⟩
    exact ⟨hu.1, hu.2, hua.le.trans hy₁, hy₂⟩
  have hp := ct_m0_of_row_envelope h.solution hua ha hseg hc hF hF1 hl hy
    ((hterm u₀ hu₀).2 u hu hhalf) g hg hmajor hJ v hv
  have hAL := mul_le_mul_of_nonneg_left hL hA
  change A * 1 ≤ A * L at hAL
  calc
    ‖S.phi u v‖ ≤ 1 + B * L + (F + c⁻¹ * Jstop) / (1 - F ^ 2) := hp
    _ = B * L + A := by dsimp only [A]; ring
    _ ≤ B * L + A * L := by linarith only [hAL]
    _ = C * L := by dsimp only [C]; ring

/-- [internal] The actual zero-stage boundary at a proper entry sphere.
All stage-indexed fields are empty; the boundary at the single cutoff is
the given outgoing entry label. This initializes finite append induction. -/
@[expose] def initialBoundary (S : Fields) (ui u₀ v₀ ρ : ℝ)
    (hp : (u₀, v₀) ∈ origDomain ui) (hoff : u₀ < v₀) :
    FiniteBoundary S ui u₀ u₀ v₀ ρ (fun _ => v₀) 0 where
  cuts := fun _ => u₀
  cool := Fin.elim0
  radii := Fin.elim0
  first := rfl
  last := rfl
  ordered := fun _ _ _ => le_rfl
  split := by intro n; exact Fin.elim0 n
  entry_label := rfl
  mem := fun u hu => by have he : u = u₀ := le_antisymm hu.2 hu.1; simpa only [he] using hp
  off_axis := fun u hu => by have he : u = u₀ := le_antisymm hu.2 hu.1; simpa only [he] using hoff
  cont := continuousOn_const
  mono := fun _ _ _ _ _ => le_rfl
  radius_pos := by intro n; exact Fin.elim0 n
  cylinder := by intro n; exact Fin.elim0 n
  cylinder_c1 := by intro n; exact Fin.elim0 n
  cylinder_rate := by intro n; exact Fin.elim0 n
  connector := by intro n; exact Fin.elim0 n
  radius_range := by intro n; exact Fin.elim0 n

end EmcsfAcExtension.Global.Closure

namespace EmcsfAcExtension.Global

/-- [node eq:cc-zeta]
The charged logarithmic scale vanishes, charged_SF_new_version.tex:L3895–L3898. For
each development and arbitrary fixed coupling, every fixed coefficient `C`
is chosen before the entry row tends to the missing endpoint. -/
theorem cc_zeta (ui e : ℝ) (S : Fields) (h : OriginalData ui e S)
    (hs : SignedTerminalBound ui S) (C : ℝ) :
    Tendsto (fun u₀ => e ^ 2 *
      (C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u₀ 0)))) ^ 2 * S.r u₀ 0 ^ 2)
      (𝓝[<] 0) (𝓝 0) := by
  obtain ⟨δ, K, lam₀, _, _, _, _, _, _, hR, _, _, _⟩ :=
    (Terminal.hypotheses ui e S h).2 hs
  have hi := h.solution.r_pos (ui, 0) ⟨le_rfl, h.ui_neg, h.ui_neg.le, le_rfl⟩ h.ui_neg
  have hRp : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hR, ?_⟩
    filter_upwards [Ioo_mem_nhdsLT h.ui_neg] with u hu
    exact h.solution.r_pos (u, 0) ⟨hu.1.le, hu.2, hu.2.le, le_rfl⟩ hu.2
  exact (Exterior.logarithmic_scale_tendsto_zero (S.r ui 0) C e hi).comp hRp

end EmcsfAcExtension.Global

namespace EmcsfAcExtension.Global.Closure

/-- [node sec:charged-closure#entry-stop-initialization]
One final interval of entry rows satisfies every strict source stop, the
entry energy envelope, and any prescribed charged-error and clock margins.
The exterior family and positive expansion constants depend on the fixed
development. All tolerances, clock coefficients and logarithmic amplitude
coefficients are fixed before the entry row, uniformly in subsequent stages.
The initial interaction is the real function required by internal project record's closure
consumer, identified here with the nonnegative source integral.
Source: charged_SF_new_version.tex:L3854–L3898; internal project record entry initialization. -/
theorem entry_stop_initialization (ui e : ℝ) (S : Fields) (h : OriginalData ui e S)
    (hs : SignedTerminalBound ui S) :
    ∃ ell V : ℝ → ℝ, ∃ a ∈ Ioo ui 0, ∃ c > 0, ∃ Λ > 0,
      c ≤ Λ ∧ (∀ p ∈ origDomain ui, S.lam p.1 p.2 ≤ Λ) ∧
      (∀ u ∈ Ico a 0, u < V u ∧ V u < 0 ∧ S.r u (V u) = ell (S.r u 0)) ∧
      Tendsto (fun u => ∫ v in V u..0, ‖weightedJ S u v‖) (𝓝[<] 0) (𝓝 0) ∧
      ∀ (F ε εstop εentry H ρ χ C η : ℝ),
      0 < F → 0 < ε → 0 < εstop → 0 < εentry → εentry ≤ 1 →
      0 ≤ H → 0 < ρ → ρ < χ → 0 < η →
      ∀ᶠ u₀ in 𝓝[<] (0 : ℝ),
        u₀ ∈ Ioo ui 0 ∧
        (∃ E : EntryData S ell u₀ (V u₀),
          E.D₀ = ENNReal.ofReal (∫ v in V u₀..0, ‖weightedJ S u₀ v‖)) ∧
        StrictFiniteCutoffStops S ui u₀ (S.r u₀ 0) V
          (fun _ => ∫ v in V u₀..0, ‖weightedJ S u₀ v‖) (fun _ => 0)
          (gapConstant / 2) c Λ F ε εstop u₀ ∧
        (∀ v ∈ Icc (V u₀) 0, 2 * c ≤ S.lam u₀ v) ∧
        cylinderEnergy S (ell (S.r u₀ 0)) u₀ (V u₀) / ell (S.r u₀ 0) ≤ εentry ∧
        2 * (H * ell (S.r u₀ 0) / (εentry * (1 - ρ / χ)) + ell (S.r u₀ 0)) <
          S.r u₀ 0 / 4 ∧
        e ^ 2 * (C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u₀ 0)))) ^ 2 *
          S.r u₀ 0 ^ 2 < η := by
  obtain ⟨ell, V, a, ha, c, hc, Λ, hΛ, hcΛ, hupper, hroot, hD, hratio, henergy, hstops⟩ :=
    cc_entry ui e S h hs
  obtain ⟨b, hb, hgap⟩ := Gap.late_from_terminal ui e S h hs
  refine ⟨ell, V, a, ha, c, hc, Λ, hΛ, hcΛ, hupper, hroot, hD, ?_⟩
  intro F ε εstop εentry H ρ χ C η hF hε hstop he he1 hH hρ hρχ hη
  have hA : 0 < 1 / (16 * (H / (1 - ρ / χ) + 1)) := by
    have hχ : 0 < χ := hρ.trans hρχ
    have hg : 0 < 1 - ρ / χ := sub_pos.mpr ((div_lt_one hχ).mpr hρχ)
    positivity
  have hsmallD := hD.eventually (gt_mem_nhds hstop)
  have hsmallE := henergy.eventually (ge_mem_nhds he)
  have hsmallRatio := (hratio εentry he).eventually (gt_mem_nhds hA)
  have hsmallZ := (cc_zeta ui e S h hs C).eventually (gt_mem_nhds hη)
  filter_upwards [Ioo_mem_nhdsLT ha.2, Ioo_mem_nhdsLT hb.2, hstops F hF ε hε,
    hsmallD, hsmallE, hsmallRatio, hsmallZ] with u₀ hua hub hfields hD₀ hE hratio₀ hZ
  have hu₀ : u₀ ∈ Ioo ui 0 := ⟨ha.1.trans hua.1, hua.2⟩
  have hu : u₀ ∈ Ico a 0 := ⟨hua.1.le, hua.2⟩
  have hv := hroot u₀ hu
  have hp : (u₀, V u₀) ∈ origDomain ui := ⟨hu₀.1.le, hu₀.2, hv.1.le, hv.2.1.le⟩
  have hR : 0 < S.r u₀ 0 := h.solution.r_pos (u₀, 0)
    ⟨hu₀.1.le, hu₀.2, hu₀.2.le, le_rfl⟩ hu₀.2
  have hB : 0 < ell (S.r u₀ 0) := hv.2.2 ▸ h.solution.r_pos _ hp hv.1
  have hrow : outSeg u₀ (V u₀) 0 ⊆ origDomain ui := by
    rintro ⟨u, v⟩ ⟨rfl, hvl, hvr⟩
    exact ⟨hu₀.1.le, hu₀.2, hv.1.le.trans hvl, hvr⟩
  have hDreal := initialInteraction_eq h.solution hv.1 hv.2.1.le hrow
  have hbox : ExteriorStops S (exteriorDomain ui u₀ u₀ V) (gapConstant / 2) c Λ F ε := by
    intro p hp'
    have heq : p.1 = u₀ := le_antisymm hp'.2.2.1 hp'.2.1
    have hfv : p.2 ∈ Icc (V u₀) 0 := ⟨by simpa only [heq] using hp'.2.2.2, hp'.1.2.2.2⟩
    obtain ⟨hl, hlU, hx, hm⟩ := hfields p.2 hfv
    have hlc : c < S.lam u₀ p.2 := by linarith only [hl, hc]
    have hg := hgap p hp'.1 (by simpa only [heq] using hub.1.le)
    simpa only [heq] using
      And.intro ((h.mu p hp'.1).1) ⟨by simpa only [heq] using hg.1,
        hlc.le, hlU, hx.le, hm.le, by simpa only [heq] using hg.2⟩
  refine ⟨hu₀, ⟨entryData S ell u₀ (V u₀) hv.2.2, hDreal⟩, ?_,
    (fun v hv => (hfields v hv).1.le), hE, ?_, hZ⟩
  · refine ⟨hbox, ?_, ?_, by simpa only [add_zero] using hD₀⟩
    · intro p hp'
      have heq : p.1 = u₀ := le_antisymm hp'.2.2.1 hp'.2.1
      have hh := hfields p.2 ⟨by simpa only [heq] using hp'.2.2.2, hp'.1.2.2.2⟩
      have hlc : c < S.lam u₀ p.2 := by linarith only [hh.1, hc]
      simpa only [heq] using And.intro hlc ⟨hh.2.2.1, hh.2.2.2⟩
    · intro u hu'
      have heq : u = u₀ := le_antisymm hu'.2 hu'.1
      simpa only [heq] using half_lt_self hR
  · exact clock_loss_lt_of_entry_ratio hH ⟨hρ, hρχ⟩ ⟨he, he1⟩ hB.le hR hratio₀

end EmcsfAcExtension.Global.Closure
