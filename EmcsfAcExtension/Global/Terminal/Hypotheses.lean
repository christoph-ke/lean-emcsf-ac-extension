module

public import EmcsfAcExtension.Global.Terminal.Correction
import EmcsfAcExtension.Local.Calculus.Reconstruction

/-! # Terminal equivalence and endpoint asymptotics

The iff is assembled before taking any signed terminal premise. All endpoint
limits follow from proved absolute integrability on the half-open interval;
no field value is assigned to the missing vertex. Source:
`charged_SF_new_version.tex:L914–1031` and approved internal project record.
-/

public section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace EmcsfAcExtension.Global.Terminal

/-- [internal] The mass-tail density is absolutely integrable under the
positive terminal condition. Its comparison coefficient is universal. -/
theorem terminal_mass_density_integrable_of_positive {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hp : PositiveTerminalFinite ui S) :
    IntegrableOn (fun u => (-S.nu u 0) * S.m u 0 / S.r u 0 ^ 2) (Ico ui 0) := by
  have hpoint (u : ℝ) (hu : u ∈ Ico ui 0) : (u, 0) ∈ origDomain ui :=
    ⟨hu.1, hu.2, hu.2.le, le_rfl⟩
  have cr : ContinuousOn (fun u => S.r u 0) (Ico ui 0) :=
    h.solution.cont_r.comp (continuous_id.prodMk continuous_const).continuousOn hpoint
  have cn : ContinuousOn (fun u => S.nu u 0) (Ico ui 0) :=
    h.solution.cont_nu.comp (continuous_id.prodMk continuous_const).continuousOn hpoint
  have cm : ContinuousOn (fun u => S.m u 0) (Ico ui 0) :=
    h.solution.cont_m.comp (continuous_id.prodMk continuous_const).continuousOn hpoint
  have cf := (cn.neg.mul cm).div (cr.pow 2)
    (fun u hu => pow_ne_zero _ (h.solution.r_pos _ (hpoint u hu) hu.2).ne')
  apply Integrable.mono' (terminal_positive_integrable_of_finite h hp)
    (cf.aestronglyMeasurable measurableSet_Ico)
  filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
  have hR := h.solution.r_pos _ (hpoint u hu) hu.2
  have hn := neg_pos.mpr (h.solution.nu_neg _ (hpoint u hu))
  have hm := (mass_monotonicity h.solution (u, 0) (hpoint u hu)).1
  have hg := h.solution.one_sub_mu_pos _ (hpoint u hu)
  have hg1 : 1 - S.mu u 0 ≤ 1 := by linarith only [(h.mu _ (hpoint u hu)).1]
  have hmn : 0 ≤ (-S.nu u 0) * S.m u 0 / S.r u 0 ^ 2 := by positivity
  change ‖(-S.nu u 0) * S.m u 0 / S.r u 0 ^ 2‖ ≤ positiveExpIntegrand S u 0
  rw [Real.norm_eq_abs, abs_of_nonneg hmn]
  have he : positiveExpIntegrand S u 0 =
      2 * ((-S.nu u 0) * S.m u 0 / S.r u 0 ^ 2) / (1 - S.mu u 0) := by
    unfold positiveExpIntegrand Fields.mu
    field_simp
  rw [he]
  apply (le_div_iff₀ hg).2
  have hh := mul_le_mul_of_nonneg_left hg1 hmn
  linarith only [hh, hmn]

private theorem terminal_mass_ratio_zero_of_integrable {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S)
    (hi : IntegrableOn (fun u => (-S.nu u 0) * S.m u 0 / S.r u 0 ^ 2) (Ico ui 0)) :
    Tendsto (fun u => S.m u 0 / S.r u 0) (𝓝[<] 0) (𝓝 0) := by
  let f := fun u => (-S.nu u 0) * S.m u 0 / S.r u 0 ^ 2
  have hn (u : ℝ) (hu : u ∈ Ico ui 0) : 0 ≤ f u := by
    have hp : (u, 0) ∈ origDomain ui := ⟨hu.1, hu.2, hu.2.le, le_rfl⟩
    exact div_nonneg (mul_nonneg (neg_pos.mpr (h.solution.nu_neg _ hp)).le
      (mass_monotonicity h.solution (u, 0) hp).1) (sq_nonneg _)
  have hi' : IntegrableOn f (uIcc ui 0) := by
    simpa only [uIcc_of_le h.ui_neg.le, IntegrableOn, restrict_Ico_eq_restrict_Icc] using hi
  have htail : Tendsto (fun a => ∫ u in a..0, f u) (𝓝[<] 0) (𝓝 0) := by
    have hc := intervalIntegral.continuousOn_primitive_interval_left hi'
    apply (show Tendsto (fun a => ∫ u in a..0, f u) (𝓝[uIcc ui 0] 0) (𝓝 0) from
      by simpa only [intervalIntegral.integral_same] using (hc 0 right_mem_uIcc).tendsto).comp
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨nhdsWithin_le_nhds, ?_⟩
    filter_upwards [Ioo_mem_nhdsLT h.ui_neg] with u hu
    simpa only [uIcc_of_le h.ui_neg.le] using ⟨hu.1.le, hu.2.le⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hlabel : ∀ᶠ a : ℝ in 𝓝[<] 0, a ∈ Ioo ui 0 := Ioo_mem_nhdsLT h.ui_neg
  obtain ⟨a, ha, hfa⟩ := (hlabel.and
    (htail.eventually (Iio_mem_nhds (half_pos hε)))).exists
  have hRa := h.solution.r_pos (a, 0) ⟨ha.1.le, ha.2, ha.2.le, le_rfl⟩ ha.2
  filter_upwards [Ioo_mem_nhdsLT ha.2,
    (terminal_radius_collapse h.ui_neg h.solution h.mu).eventually
      (Iio_mem_nhds (half_pos hRa))] with u hu hRu
  have hp : (u, 0) ∈ origDomain ui := ⟨ha.1.le.trans hu.1.le, hu.2, hu.2.le, le_rfl⟩
  have hR := h.solution.r_pos _ hp hu.2
  have hm := (mass_monotonicity h.solution (u, 0) hp).1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hm hR.le)]
  have hseg : inSeg a u 0 ⊆ origDomain ui :=
    (inSeg_subset_origDomain_iff hu.1.le).2 ⟨ha.1.le, hu.2, hu.2.le, le_rfl⟩
  obtain ⟨b, hb, hRb⟩ := intermediate_value_Icc' hu.1.le
    (Calculus.continuousOn_in_section h.solution.cont_r hseg)
    (show 2 * S.r u 0 ∈ Icc (S.r u 0) (S.r a 0) from
      ⟨by linarith only [hR], by linarith only [hRu]⟩)
  change S.r b 0 = 2 * S.r u 0 at hRb
  have hsegb : inSeg b u 0 ⊆ origDomain ui :=
    (inSeg_subset_origDomain_iff hb.2).2 ⟨ha.1.le.trans hb.1, hu.2, hu.2.le, le_rfl⟩
  have cr := Calculus.continuousOn_in_section h.solution.cont_r hsegb
  have cn := Calculus.continuousOn_in_section h.solution.cont_nu hsegb
  have hri : IntervalIntegrable (fun s => (-S.nu s 0) / S.r s 0 ^ 2) volume b u :=
    (cn.neg.div (cr.pow 2) (fun s hs => pow_ne_zero _
      (h.solution.r_pos (s, 0) (hsegb ⟨hs.1, hs.2, rfl⟩)
        (hs.2.trans_lt hu.2)).ne')).intervalIntegrable_of_Icc hb.2
  have hfi : IntervalIntegrable f volume b u := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hb.2]
    exact hi.mono_set (fun s hs => ⟨ha.1.le.trans (hb.1.trans hs.1), hs.2.trans_lt hu.2⟩)
  have hmono := intervalIntegral.integral_mono_on hb.2 (hri.mul_const (S.m u 0)) hfi
    (fun s hs => ?_)
  · rw [intervalIntegral.integral_mul_const,
      incoming_radius_inv h.solution (ha.1.le.trans hb.1) hb.2 hu.2, hRb] at hmono
    have he : ((S.r u 0)⁻¹ - (2 * S.r u 0)⁻¹) * S.m u 0 =
        (S.m u 0 / S.r u 0) / 2 := by rw [mul_inv_rev]; ring
    rw [he] at hmono
    have ht : (∫ s in b..u, f s) ≤ ∫ s in a..0, f s := by
      rw [intervalIntegral.integral_of_le hb.2, intervalIntegral.integral_of_le ha.2.le]
      simp only [restrict_Ioc_eq_restrict_Icc, ← restrict_Ico_eq_restrict_Icc]
      apply setIntegral_mono_set (hi.mono_set (Ico_subset_Ico_left ha.1.le))
        ((ae_restrict_iff' measurableSet_Ico).2 (Eventually.of_forall fun s hs =>
          hn s ⟨ha.1.le.trans hs.1, hs.2⟩))
      exact Eventually.of_forall fun s hs => ⟨hb.1.trans hs.1, hs.2.trans hu.2⟩
    linarith only [hmono, ht, hfa]
  have hps : (s, 0) ∈ origDomain ui := hsegb ⟨hs.1, hs.2, rfl⟩
  have hmass := mass_antitone_in h.solution hs.2 hu.2.le
    ((inSeg_subset_origDomain_iff hs.2).2 ⟨hps.1, hu.2, hu.2.le, le_rfl⟩)
  have hweight : 0 ≤ (-S.nu s 0) / S.r s 0 ^ 2 :=
    div_nonneg (neg_pos.mpr (h.solution.nu_neg _ hps)).le (sq_nonneg _)
  convert mul_le_mul_of_nonneg_left hmass hweight using 1
  dsimp only [f]
  ring

/-- [node prop:charged-terminal-equivalence#terminal-mass-tail]
The terminal mass density is integrable and `m/r` tends to zero
(charged_SF_new_version.tex:L1027–1028). Nonnegative mass and incoming monotonicity
convert small integral tails into the pointwise ratio limit. -/
theorem terminal_mass_tail {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    (∫⁻ u in Ico ui 0, ENNReal.ofReal ((-S.nu u 0) * S.m u 0 / S.r u 0 ^ 2)) < ⊤ ∧
      Tendsto (fun u => S.m u 0 / S.r u 0) (𝓝[<] 0) (𝓝 0) := by
  have hi := terminal_mass_density_integrable_of_positive h (signed_to_positive h hs)
  refine ⟨?_, terminal_mass_ratio_zero_of_integrable h hi⟩
  apply lt_of_le_of_lt (lintegral_mono_ae ?_) hi.2
  filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
  have hp : (u, 0) ∈ origDomain ui := ⟨hu.1, hu.2, hu.2.le, le_rfl⟩
  have hn : 0 ≤ (-S.nu u 0) * S.m u 0 / S.r u 0 ^ 2 :=
    div_nonneg (mul_nonneg (neg_pos.mpr (h.solution.nu_neg _ hp)).le
      (mass_monotonicity h.solution (u, 0) hp).1) (sq_nonneg _)
  rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hn]

/-- [internal]
The outgoing terminal expansion has a strictly positive finite limit
(charged_SF_new_version.tex:L1029–1031). Its logarithm is a primitive of the proved
integrable signed exponent. -/
theorem terminal_lambda_limit {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ Tendsto (fun u => S.lam u 0) (𝓝[<] 0) (𝓝 lam₀) := by
  have hi : IntegrableOn (fun u => signedExpIntegrand S u 0) (uIcc ui 0) := by
    simpa only [uIcc_of_le h.ui_neg.le, IntegrableOn, restrict_Ico_eq_restrict_Icc] using
      terminal_signed_integrable h hs
  have hc := intervalIntegral.continuousOn_primitive_interval hi
  have ht : Tendsto (fun a => ∫ u in ui..a, signedExpIntegrand S u 0) (𝓝[<] 0)
      (𝓝 (∫ u in ui..0, signedExpIntegrand S u 0)) := by
    apply (show Tendsto (fun a => ∫ u in ui..a, signedExpIntegrand S u 0)
      (𝓝[uIcc ui 0] 0) (𝓝 (∫ u in ui..0, signedExpIntegrand S u 0)) from hc 0 right_mem_uIcc).comp
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨nhdsWithin_le_nhds, ?_⟩
    filter_upwards [Ioo_mem_nhdsLT h.ui_neg] with u hu
    simpa only [uIcc_of_le h.ui_neg.le] using ⟨hu.1.le, hu.2.le⟩
  let L := Real.log (S.lam ui 0) - ∫ u in ui..0, signedExpIntegrand S u 0
  have hlog : Tendsto (fun u => Real.log (S.lam u 0)) (𝓝[<] 0) (𝓝 L) := by
    apply (tendsto_const_nhds.sub ht).congr'
    filter_upwards [Ioo_mem_nhdsLT h.ui_neg] with u hu
    have he := (incoming_log_lambda_integralForm h.solution hu.1.le hu.2
      ((inSeg_subset_origDomain_iff hu.1.le).2 ⟨le_rfl, hu.2, hu.2.le, le_rfl⟩)).2
    rw [intervalIntegral.integral_neg] at he
    linarith only [he]
  refine ⟨Real.exp L, Real.exp_pos L, ?_⟩
  apply (Real.continuous_exp.continuousAt.tendsto.comp hlog).congr'
  filter_upwards [Ioo_mem_nhdsLT h.ui_neg] with u hu
  exact Real.exp_log (h.solution.lam_pos (u, 0) ⟨hu.1.le, hu.2, hu.2.le, le_rfl⟩)

/-- [internal]
The signed terminal primitive has a finite limit, equal to its integral
over the full half-open terminal cone (charged_SF_new_version.tex:L1029–1030). -/
theorem terminal_gamma_limit {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    Tendsto (fun a => ∫ u in ui..a, signedExpIntegrand S u 0) (𝓝[<] 0)
      (𝓝 (∫ u in ui..0, signedExpIntegrand S u 0)) := by
  have hi : IntegrableOn (fun u => signedExpIntegrand S u 0) (uIcc ui 0) := by
    simpa only [uIcc_of_le h.ui_neg.le, IntegrableOn, restrict_Ico_eq_restrict_Icc] using
      terminal_signed_integrable h hs
  apply ((intervalIntegral.continuousOn_primitive_interval hi) 0 right_mem_uIcc).tendsto.comp
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨nhdsWithin_le_nhds, ?_⟩
  filter_upwards [Ioo_mem_nhdsLT h.ui_neg] with u hu
  simpa only [uIcc_of_le h.ui_neg.le] using ⟨hu.1.le, hu.2.le⟩

/-- [internal]
The initial radius gauge fixes the terminal outgoing expansion to `1/2`
on the initial row (charged_SF_new_version.tex:L896–912). -/
theorem initial_terminal_lambda {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) : S.lam ui 0 = 1 / 2 := by
  have hseg : outSeg ui ui 0 ⊆ origDomain ui :=
    (outSeg_subset_origDomain_iff h.ui_neg.le).2 ⟨le_rfl, h.ui_neg, le_rfl, le_rfl⟩
  have heq : ∀ v ∈ Ioo ui 0, S.lam ui v = 1 / 2 := by
    intro v hv
    have hd := Local.IsSolution.hasDerivAt_radius_out h.solution hseg hv
    have hn : HasDerivAt (fun v : ℝ => (v - ui) / 2) (1 / 2) v := by
      simpa only [id_eq] using ((hasDerivAt_id v).sub_const ui).div_const 2
    exact hd.unique (hn.congr_of_eventuallyEq (by
      filter_upwards [Ioo_mem_nhds hv.1 hv.2] with w hw
      exact h.radius w ⟨hw.1.le, hw.2.le⟩))
  have hc := Calculus.continuousOn_out_section h.solution.cont_lam hseg
  have hc' : ContinuousOn (S.lam ui) (closure (Ioo ui 0)) := by
    simpa only [closure_Ioo h.ui_neg.ne] using hc
  have hmem : (0:ℝ) ∈ closure (Ioo ui 0) := by
    rw [closure_Ioo h.ui_neg.ne]; exact ⟨h.ui_neg.le, le_rfl⟩
  exact le_antisymm
    (le_on_closure (fun v hv => (heq v hv).le) hc' continuousOn_const hmem)
    (le_on_closure (fun v hv => (heq v hv).ge) continuousOn_const hc' hmem)

/-- [internal]
Exact normalized exponential formula for the terminal expansion,
including the initial label (charged_SF_new_version.tex:L1029–1031). -/
theorem terminal_lambda_eq_exp {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) :
    ∀ u ∈ Ico ui 0, S.lam u 0 =
      (1 / 2) * Real.exp (-(∫ s in ui..u, signedExpIntegrand S s 0)) := by
  intro u hu
  have he := (incoming_log_lambda_integralForm h.solution hu.1 hu.2
    ((inSeg_subset_origDomain_iff hu.1).2 ⟨le_rfl, hu.2, hu.2.le, le_rfl⟩)).2
  dsimp only at he
  rw [intervalIntegral.integral_neg, initial_terminal_lambda h] at he
  have hl : Real.log (S.lam u 0) = Real.log (1 / 2) -
      ∫ s in ui..u, signedExpIntegrand S s 0 := by linarith only [he]
  rw [← Real.exp_log (h.solution.lam_pos (u, 0)
    ⟨hu.1, hu.2, hu.2.le, le_rfl⟩), hl, Real.exp_sub, Real.exp_log (by norm_num : (0:ℝ)<1/2),
    Real.exp_neg, div_eq_mul_inv]

/-- [node prop:charged-terminal-equivalence#terminal-lambda-limit]
The finite signed exponent, exact initial-gauge formula and positive
terminal expansion limit (charged_SF_new_version.tex:L1029–1031). The limiting expansion
depends on the fixed development and signed bound. -/
theorem terminal_lambda_asymptotics {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    Tendsto (fun a => ∫ u in ui..a, signedExpIntegrand S u 0) (𝓝[<] 0)
      (𝓝 (∫ u in ui..0, signedExpIntegrand S u 0)) ∧
    (∀ u ∈ Ico ui 0, S.lam u 0 =
      (1 / 2) * Real.exp (-(∫ s in ui..u, signedExpIntegrand S s 0))) ∧
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ Tendsto (fun u => S.lam u 0) (𝓝[<] 0) (𝓝 lam₀) :=
  ⟨terminal_gamma_limit h hs, terminal_lambda_eq_exp h, terminal_lambda_limit h hs⟩

/-- [internal]
The terminal iff and its asymptotics, charged_SF_new_version.tex:L914–1031. The iff is
outside the implication assuming the signed bound. The positive witnesses
may depend on the fixed development and its signed bound, uniformly in the
terminal label; no theorem of the local existence theory is assumed. -/
theorem hypotheses (ui e : ℝ) (S : Fields) (h : OriginalData ui e S) :
    (SignedTerminalBound ui S ↔ PositiveTerminalFinite ui S) ∧
    (SignedTerminalBound ui S →
      ∃ δ C lam₀ : ℝ, 0 < δ ∧ 0 < C ∧ 0 < lam₀ ∧
      (∀ u ∈ Ico ui 0, δ ≤ 1 - S.mu u 0) ∧
      (∫⁻ u in Ico ui 0, ENNReal.ofReal
        ((-S.nu u 0) * ‖S.xi u 0 / (S.nu u 0 : ℂ)‖ ^ 2 / S.r u 0)) < ⊤ ∧
      (∫⁻ u in Ico ui 0, ENNReal.ofReal ((-S.nu u 0) * S.m u 0 / S.r u 0 ^ 2)) < ⊤ ∧
      Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0) ∧
      Tendsto (fun u => S.m u 0 / S.r u 0) (𝓝[<] 0) (𝓝 0) ∧
      Tendsto (fun u => S.lam u 0) (𝓝[<] 0) (𝓝 lam₀) ∧
      (∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
        C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0))))) := by
  constructor
  · exact ⟨signed_to_positive h,
      positive_to_signed ui e S h.ui_neg h.solution h.gauge h.mu h.radius h.datumAC⟩
  intro hs
  obtain ⟨hgap, hflux⟩ := terminal_gap_and_flux ui e S h.ui_neg h.solution h.gauge
    h.mu h.radius h.datumAC hs
  obtain ⟨δ, hδ, hg⟩ := hgap
  obtain ⟨C, hC, hscalar⟩ := scalar_log_bound ui e S h.ui_neg h.solution h.gauge
    h.mu h.radius h.datumAC hs
  obtain ⟨lam₀, hlam₀, hlam⟩ := terminal_lambda_limit h hs
  have hmass := terminal_mass_tail h hs
  refine ⟨δ, C, lam₀, hδ, hC, hlam₀, hg, ?_, hmass.1,
    terminal_radius_collapse h.ui_neg h.solution h.mu, hmass.2, hlam, hscalar⟩
  convert hflux using 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
  rw [incoming_scalar_flux_eq h.solution
    (show (u, 0) ∈ origDomain ui from ⟨hu.1, hu.2, hu.2.le, le_rfl⟩)]

end EmcsfAcExtension.Global.Terminal

namespace EmcsfAcExtension.Global

/-- [internal]
Canonical terminal equivalence and asymptotics, charged_SF_new_version.tex:L914–1031.
The iff is outside the signed implication. Positive witnesses depend on the
fixed development and signed bound, uniformly in the terminal label. -/
theorem charged_terminal_equivalence (ui e : ℝ) (S : Fields) (h : OriginalData ui e S) :
    (SignedTerminalBound ui S ↔ PositiveTerminalFinite ui S) ∧
    (SignedTerminalBound ui S →
      ∃ δ C lam₀ : ℝ, 0 < δ ∧ 0 < C ∧ 0 < lam₀ ∧
      (∀ u ∈ Ico ui 0, δ ≤ 1 - S.mu u 0) ∧
      (∫⁻ u in Ico ui 0, ENNReal.ofReal
        ((-S.nu u 0) * ‖S.xi u 0 / (S.nu u 0 : ℂ)‖ ^ 2 / S.r u 0)) < ⊤ ∧
      (∫⁻ u in Ico ui 0, ENNReal.ofReal ((-S.nu u 0) * S.m u 0 / S.r u 0 ^ 2)) < ⊤ ∧
      Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0) ∧
      Tendsto (fun u => S.m u 0 / S.r u 0) (𝓝[<] 0) (𝓝 0) ∧
      Tendsto (fun u => S.lam u 0) (𝓝[<] 0) (𝓝 lam₀) ∧
      (∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
        C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0))))) := by
  exact Terminal.hypotheses ui e S h

/-- [node prop:charged-terminal-equivalence]
The full terminal bundle, including the quantitative charge tail
(charged_SF_new_version.tex:L916–950). One positive constant controls both scalar and
charge conclusions; it depends on the fixed development and signed bound,
uniformly in every terminal label. The coupling is arbitrary. -/
theorem charged_terminal_equivalence_with_charge (ui e : ℝ) (S : Fields) (h : OriginalData ui e S) :
    (SignedTerminalBound ui S ↔ PositiveTerminalFinite ui S) ∧
    (SignedTerminalBound ui S →
      ∃ δ C lam₀ : ℝ, 0 < δ ∧ 0 < C ∧ 0 < lam₀ ∧
      (∀ u ∈ Ico ui 0, δ ≤ 1 - S.mu u 0) ∧
      (∫⁻ u in Ico ui 0, ENNReal.ofReal
        ((-S.nu u 0) * ‖S.xi u 0 / (S.nu u 0 : ℂ)‖ ^ 2 / S.r u 0)) < ⊤ ∧
      (∫⁻ u in Ico ui 0, ENNReal.ofReal ((-S.nu u 0) * S.m u 0 / S.r u 0 ^ 2)) < ⊤ ∧
      Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0) ∧
      Tendsto (fun u => S.m u 0 / S.r u 0) (𝓝[<] 0) (𝓝 0) ∧
      Tendsto (fun u => S.lam u 0) (𝓝[<] 0) (𝓝 lam₀) ∧
      (∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
        C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) ∧
      (∀ a ∈ Ico ui 0, S.Q a 0 ^ 2 ≤
        C * e ^ 2 * S.r a 0 ^ 4 * (1 + Real.log (S.r ui 0 / S.r a 0)) *
          (∫ u in a..0, ‖S.xi u 0‖ ^ 2 / ((-S.nu u 0) * S.r u 0)))) := by
  refine ⟨(charged_terminal_equivalence ui e S h).1, ?_⟩
  intro hs
  obtain ⟨δ, C, lam₀, hδ, hC, hlam, hgap, hflux, hmass, hR, htail, hlimit, hlog⟩ :=
    (charged_terminal_equivalence ui e S h).2 hs
  obtain ⟨D, hD, hcharge⟩ := charged_terminal_charge h hs
  refine ⟨δ, max C D, lam₀, hδ, lt_of_lt_of_le hC (le_max_left _ _), hlam,
    hgap, hflux, hmass, hR, htail, hlimit, ?_, ?_⟩
  · intro u hu
    exact (hlog u hu).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (by positivity))
  · intro a ha
    have hp : (a, 0) ∈ origDomain ui := ⟨ha.1, ha.2, ha.2.le, le_rfl⟩
    have hRa := h.solution.r_pos _ hp ha.2
    have hlog0 : 0 ≤ Real.log (S.r ui 0 / S.r a 0) := Real.log_nonneg
      ((one_le_div hRa).2 ((Terminal.terminal_radius_strictAntiOn h.solution).antitoneOn
        ⟨le_rfl, h.ui_neg⟩ ha ha.1))
    have hf : 0 ≤ ∫ u in a..0, ‖S.xi u 0‖ ^ 2 / ((-S.nu u 0) * S.r u 0) := by
      apply intervalIntegral.integral_nonneg_of_ae_restrict ha.2.le
      rw [← restrict_Ico_eq_restrict_Icc]
      filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
      have hpu : (u, 0) ∈ origDomain ui :=
        ⟨ha.1.trans hu.1, hu.2, hu.2.le, le_rfl⟩
      exact div_nonneg (sq_nonneg _) (mul_nonneg
        (neg_pos.mpr (h.solution.nu_neg _ hpu)).le (h.solution.r_pos _ hpu hu.2).le)
    apply (hcharge a ha).trans
    gcongr
    exact le_max_right C D

end EmcsfAcExtension.Global
