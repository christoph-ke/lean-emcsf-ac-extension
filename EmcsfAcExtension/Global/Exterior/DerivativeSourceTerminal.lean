module

public import EmcsfAcExtension.Global.Exterior.DerivativeSourceBounds
public import EmcsfAcExtension.Global.Exterior.Variation

/-! # Terminal consumers of the exterior source estimates

All scalar, charge and gap inputs of the source helpers are discharged
from internal project record here. The terminal premises are exactly the approved
conditional handoff inputs; internal project record supplies them in Root A assembly.
The constants `2`, `4` and `32` are numerical, uniform in all solutions,
couplings, outgoing rows and labels. Only the late cutoff depends on
the fixed terminal inputs and adaptive profile.
-/

public section

open Set Filter Topology MeasureTheory

namespace EmcsfAcExtension.Global.Exterior

variable {ui e C : ℝ} {S : Fields}

/-- [internal]
The already proved terminal exterior estimates supply all inputs to the
four charged source bounds simultaneously. The late cutoff depends on
the fixed solution and profile; all displayed coefficients are numerical.
No source estimate or conclusion about an outgoing derivative is assumed. -/
theorem source_inputs_of_terminal (h : OriginalData ui e S) (M ell : ℝ → ℝ)
    {R₀ : ℝ} (hR : 0 < R₀) (hC : 0 < C)
    (hcollapse : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hphi : ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) :
    ∃ u₀ ∈ Ioo ui 0, ∀ u a, (u, a) ∈ adaptiveExterior S ui u₀ ell →
      u < a ∧ a ≤ 0 ∧ outSeg u a 0 ⊆ origDomain ui ∧
      (∀ v ∈ Icc a 0, 1 / 2 ≤ 1 - S.mu u v) ∧
      (∀ v ∈ Icc a 0, ‖S.phi u v‖ ≤
        (C + 2) * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) ∧
      (∀ v ∈ Icc a 0, S.Q u v ^ 2 / S.r u v ^ 2 ≤
        64 * (terminalMass S u / S.r u v)) := by
  obtain ⟨ug, hug, hgap⟩ := exterior_small_gap_of_terminal h M ell hR
    (by norm_num : (0 : ℝ) < 1 / 4) hcollapse hmass hell hsmall
  obtain ⟨up, hup, hscalar⟩ := (scalar_log_envelope_of_terminal h M ell hR hC
    hcollapse hmass hell hsmall hphi).2
  obtain ⟨uq, huq, hcharge⟩ := charged_exterior_charge_pointwise_of_terminal h M ell hR hC
    hcollapse hmass hell hellsmall hsmall hphi
  let u₀ := max ug (max up uq)
  have hu₀ : u₀ ∈ Ioo ui 0 := ⟨lt_max_of_lt_left hug.1, max_lt hug.2 (max_lt hup.2 huq.2)⟩
  refine ⟨u₀, hu₀, ?_⟩
  intro u a hp
  have hpg : (u, a) ∈ adaptiveExterior S ui ug ell :=
    ⟨hp.1, (le_max_left ug (max up uq)).trans hp.2.1, hp.2.2⟩
  have hinner := (hgap (u, a) hpg).1
  have hra : 0 < S.r u a := hinner.trans_le hp.2.2
  have hua : u < a := by
    rcases hp.1.2.2.1.eq_or_lt with he | he
    · change u = a at he
      subst a
      rw [(h.solution.axis u hp.1).1] at hra
      exact False.elim (lt_irrefl _ hra)
    · exact he
  have ha := hp.1.2.2.2
  have hs : outSeg u a 0 ⊆ origDomain ui :=
    (outSeg_subset_origDomain_iff ha).2 ⟨hp.1.1, hp.1.2.1, hua.le, le_rfl⟩
  have hrow (v : ℝ) (hv : v ∈ Icc a 0) : (u, v) ∈ adaptiveExterior S ui u₀ ell :=
    ⟨hs ⟨rfl, hv⟩, hp.2.1, hp.2.2.trans (outgoing_radius_mono h hua.le hv.1
      (fun _ hx => hs (outSeg_subset_outSeg le_rfl hv.2 hx)))⟩
  refine ⟨hua, ha, hs, ?_, ?_, ?_⟩
  · intro v hv
    have hvp := hrow v hv
    have hc := hgap (u, v) ⟨hvp.1, (le_max_left ug (max up uq)).trans hvp.2.1, hvp.2.2⟩
    have hm := hc.2.1.trans hc.2.2
    linarith only [hm]
  · intro v hv
    have hvp := hrow v hv
    exact hscalar (u, v) ⟨hvp.1,
      (le_max_left up uq).trans ((le_max_right ug (max up uq)).trans hvp.2.1), hvp.2.2⟩
  · intro v hv
    have hvp := hrow v hv
    exact (hcharge (u, v) ⟨hvp.1,
      (le_max_right up uq).trans ((le_max_right ug (max up uq)).trans hvp.2.1), hvp.2.2⟩).2

/-- [internal]
Terminal consumer discharging every premise of the four source subestimate
helpers. The estimates have coefficients `2`, `2`, `4`, `32`, respectively;
these are universal. The solution-dependent cutoff precedes all rows and
labels, so these estimates are uniform on every later outgoing exterior.
The four conjuncts close the quadratic-coupling, scalar-charge, linear-charge
and cubic-charge estimates of `charged_SF_new_version.tex:L1313–L1325`. -/
theorem source_charge_bounds_of_terminal (h : OriginalData ui e S) (M ell : ℝ → ℝ)
    {R₀ : ℝ} (hR : 0 < R₀) (hC : 0 < C)
    (hcollapse : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hphi : ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) :
    ∃ u₀ ∈ Ioo ui 0, ∀ u a, (u, a) ∈ adaptiveExterior S ui u₀ ell →
      let L := (C + 2) * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))
      (∫ v in a..0, e ^ 2 * ‖S.phi u v‖ ^ 2 *
        ‖S.theta u v / (S.lam u v : ℂ)‖ * S.lam u v) ≤
          2 * e ^ 2 * L ^ 2 * Real.sqrt (terminalMass S u * terminalRadius S u) ∧
      (∫ v in a..0, |e| * |S.Q u v| * ‖S.phi u v‖ / S.r u v ^ 2 * S.lam u v) ≤
          2 * |e| * L * Real.sqrt (terminalMass S u / S.r u a) ∧
      (∫ v in a..0, |e| * |S.Q u v| / S.r u v ^ 2 *
        ‖S.theta u v / (S.lam u v : ℂ)‖ * S.lam u v) ≤
          4 * |e| * (terminalMass S u / S.r u a) ∧
      (∫ v in a..0, |e| * |S.Q u v| * ‖S.phi u v‖ / S.r u v ^ 2 *
        ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v) ≤
          32 * |e| * L * (terminalMass S u / S.r u a) *
            Real.sqrt (terminalMass S u / S.r u a) := by
  obtain ⟨u₀, hu₀, hrow⟩ := source_inputs_of_terminal h M ell hR hC hcollapse hmass
    hell hellsmall hsmall hphi
  refine ⟨u₀, hu₀, ?_⟩
  intro u a hp
  obtain ⟨hua, ha, hs, hg, hp, hQ⟩ := hrow u a hp
  exact ⟨source_quadratic_coupling_bound_of_gap h hua ha hs hg hp,
    source_scalar_charge_bound_of_envelope h hua ha hs hp,
    source_linear_charge_bound_of_gap h hua ha hs hg,
    source_cubic_charge_bound_of_profiles h hua ha hs hg hp hQ⟩

/-- [internal]
The terminal consumer of the field-versus-variation comparison. The inner
endpoint is the actual adaptive radius. The numerical constant `4` is
uniform in all solutions, couplings and rows; the cutoff depends only on
the supplied terminal outputs and profile. In particular the late width
condition and gap are derived, not assumed. -/
theorem charged_exterior_FV_of_terminal (h : OriginalData ui e S) (M ell : ℝ → ℝ)
    {R₀ : ℝ} (hR : 0 < R₀)
    (hcollapse : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0)) :
    ∃ u₀ ∈ Ioo ui 0, ∀ u a, (u, a) ∈ adaptiveExterior S ui u₀ ell →
      S.r u a = ell (S.r u 0) → ∀ v ∈ Icc a 0,
        ‖S.theta u v / (S.lam u v : ℂ)‖ ≤
          (eVariationOn (S.a u) (Icc a 0)).toReal +
            4 * Real.sqrt (terminalMass S u / ell (S.r u 0)) := by
  obtain ⟨ug, hug, hgap⟩ := exterior_small_gap_of_terminal h M ell hR
    (by norm_num : (0 : ℝ) < 1 / 4) hcollapse hmass hell hsmall
  have hrpos : ∀ᶠ u in 𝓝[<] (0 : ℝ), 0 < S.r u 0 := by
    filter_upwards [Ioo_mem_nhdsLT h.ui_neg] with u hu
    exact h.solution.r_pos (u, 0) ⟨hu.1.le, hu.2, hu.2.le, le_rfl⟩ hu.2
  have hRt : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hcollapse, hrpos⟩
  have he : ∀ᶠ u in 𝓝[<] (0 : ℝ), 2 * ell (S.r u 0) ≤ S.r u 0 := by
    filter_upwards [hrpos, (hellsmall.comp hRt).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with u hr he
    have hh := (div_lt_iff₀ hr).mp he
    linarith only [hh]
  obtain ⟨d, hd, hcut⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp he
  let uc := max d ui / 2
  have huc : uc ∈ Ioo ui 0 := by
    have hm := max_lt hd h.ui_neg
    dsimp [uc]
    constructor <;> linarith [le_max_right d ui]
  let u₀ := max ug uc
  refine ⟨u₀, ⟨lt_max_of_lt_left hug.1, max_lt hug.2 huc.2⟩, ?_⟩
  intro u a hp hroot v hv
  have hpg : (u, a) ∈ adaptiveExterior S ui ug ell :=
    ⟨hp.1, (le_max_left ug uc).trans hp.2.1, hp.2.2⟩
  have hc := hgap (u, a) hpg
  have hr : 0 < S.r u a := hc.1.trans_le hp.2.2
  have hua : u < a := by
    rcases hp.1.2.2.1.eq_or_lt with hh | hh
    · change u = a at hh
      subst a
      rw [(h.solution.axis u hp.1).1] at hr
      exact False.elim (lt_irrefl _ hr)
    · exact hh
  have ha := hp.1.2.2.2
  have hs : outSeg u a 0 ⊆ origDomain ui :=
    (outSeg_subset_origDomain_iff ha).2 ⟨hp.1.1, hp.1.2.1, hua.le, le_rfl⟩
  have hg (w : ℝ) (hw : w ∈ Icc a 0) : 1 / 2 ≤ 1 - S.mu u w := by
    have hrw := outgoing_radius_mono h hua.le hw.1
      (fun _ hx => hs (outSeg_subset_outSeg le_rfl hw.2 hx))
    have hc := hgap (u, w) ⟨hs ⟨rfl, hw⟩, hpg.2.1, hp.2.2.trans hrw⟩
    have hμ := hc.2.1.trans hc.2.2
    linarith only [hμ]
  have hud : d < u := by
    have hcu := (le_max_right ug uc).trans hp.2.1
    dsimp [uc] at hcu
    have hm := max_lt hd h.ui_neg
    linarith [le_max_left d ui]
  have hw : 2 * S.r u a ≤ S.r u 0 := by rw [hroot]; exact hcut ⟨hud, hp.1.2.1⟩
  simpa only [hroot] using charged_exterior_FV_of_gap h hua ha hs hg hw v hv

end EmcsfAcExtension.Global.Exterior
