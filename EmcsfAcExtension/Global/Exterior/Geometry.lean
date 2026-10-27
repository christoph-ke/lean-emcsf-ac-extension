module

public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Domains
import EmcsfAcExtension.Global.Terminal.Hypotheses
import EmcsfAcExtension.Global.Exterior.Optics
import EmcsfAcExtension.Global.Exterior.Charge
import EmcsfAcExtension.Global.Exterior.Radii

/-! # Exterior geometry with terminal estimates discharged

For a fixed constructed adaptive profile, the terminal proposition supplies
radius collapse, the logarithmic scalar bound and the positive expansion
limit. The radial mass identity and profile hypotheses below describe that
construction, rather than additional terminal estimates. Source:
`charged_SF_new_version.tex:L1098–1223`; approved internal project record.
The full proposition `c:exterior` also requires density and variation work.
-/

public section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global

variable {ui e : ℝ} {S : Fields}

/-- [internal] Put the terminal mass in the radius coordinate, without
assuming an inverse or assigning a trace at the missing vertex
(charged_SF_new_version.tex:L931–937, L1027–1028). The mass profile depends on the fixed
development; its limit and integral are exactly the terminal proposition's
outputs after the proved nonnegative change of variables. -/
theorem Exterior.terminal_mass_profile (h : OriginalData ui e S)
    (hs : SignedTerminalBound ui S) :
    ∃ M : ℝ → ℝ,
      (∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0) ∧
      (∀ R ∈ Ioc 0 (S.r ui 0), 0 ≤ M R) ∧
      ContinuousOn M (Ioc 0 (S.r ui 0)) ∧
      Tendsto (fun R => M R / R) (𝓝[>] 0) (𝓝 0) ∧
      (∫⁻ R in Ioc 0 (S.r ui 0), ENNReal.ofReal (M R / R ^ 2)) < ⊤ := by
  classical
  have hanti := Terminal.terminal_radius_strictAntiOn h.solution
  let F : Ico ui 0 → (Ioc 0 (S.r ui 0))ᵒᵈ := fun u =>
    ⟨S.r u 0, h.solution.r_pos (u, 0)
      ⟨u.property.1, u.property.2, u.property.2.le, le_rfl⟩ u.property.2,
      hanti.antitoneOn ⟨le_rfl, h.ui_neg⟩ u.property u.property.1⟩
  have hF : StrictMono F := fun a b hab => hanti a.property b.property hab
  have hsurj : Function.Surjective F := by
    intro R
    rcases R.property.2.eq_or_lt with heq | hlt
    · refine ⟨⟨ui, le_rfl, h.ui_neg⟩, Subtype.ext heq.symm⟩
    · obtain ⟨u, hu, he⟩ := (Terminal.terminal_radius_image_Ioo h.ui_neg h.solution h.mu).symm ▸
        (show R.val ∈ Ioo 0 (S.r ui 0) from ⟨R.property.1, hlt⟩)
      exact ⟨⟨u, hu.1.le, hu.2⟩, Subtype.ext he⟩
  let iso := hF.orderIsoOfSurjective F hsurj
  let U : ℝ → ℝ := fun R => if hR : R ∈ Ioc 0 (S.r ui 0) then
    (iso.symm ⟨R, hR⟩).val else ui
  have hU (u : ℝ) (hu : u ∈ Ico ui 0) : U (S.r u 0) = u := by
    have hp := (F ⟨u, hu⟩).property
    dsimp only [U]
    rw [dite_eq_left hp]
    change (iso.symm (iso ⟨u, hu⟩)).val = u
    rw [iso.symm_apply_apply]
  have hUmem (R : ℝ) (hR : R ∈ Ioc 0 (S.r ui 0)) : U R ∈ Ico ui 0 := by
    simpa only [U, dite_eq_left hR] using (iso.symm ⟨R, hR⟩).property
  have hRU (R : ℝ) (hR : R ∈ Ioc 0 (S.r ui 0)) : S.r (U R) 0 = R := by
    dsimp only [U]
    rw [dite_eq_left hR]
    exact congrArg Subtype.val (iso.apply_symm_apply ⟨R, hR⟩)
  have hUc : ContinuousOn U (Ioc 0 (S.r ui 0)) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hc : Continuous (fun R : (Ioc 0 (S.r ui 0))ᵒᵈ => (iso.symm R).val) :=
      (continuous_subtype_val : Continuous (Subtype.val : Ico ui 0 → ℝ)).comp
        iso.symm.continuous
    apply hc.congr
    intro R
    dsimp only [Set.domRestrict, U]
    rw [dite_eq_left R.property]
    cases R
    rfl
  have hRi := h.solution.r_pos (ui, 0) ⟨le_rfl, h.ui_neg, h.ui_neg.le, le_rfl⟩ h.ui_neg
  have hUzero : Tendsto U (𝓝[>] 0) (𝓝[<] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · apply tendsto_order.mpr
      constructor
      · intro a ha
        let b := max a ui / 2
        have hb : b ∈ Ioo ui 0 := by
          dsimp [b]
          constructor <;> linarith [le_max_right a ui, max_lt ha h.ui_neg]
        have hab : a < b := by
          dsimp [b]
          linarith [le_max_left a ui, max_lt ha h.ui_neg]
        have hrb := h.solution.r_pos (b, 0) ⟨hb.1.le, hb.2, hb.2.le, le_rfl⟩ hb.2
        filter_upwards [Ioo_mem_nhdsGT (lt_min hRi hrb)] with R hR
        have hmem : R ∈ Ioc 0 (S.r ui 0) := ⟨hR.1, hR.2.le.trans (min_le_left _ _)⟩
        have hbU : b < U R := by
          by_contra hn
          have hh := hanti.antitoneOn (hUmem R hmem) ⟨hb.1.le, hb.2⟩ (le_of_not_gt hn)
          rw [hRU R hmem] at hh
          exact (not_lt_of_ge hh) (hR.2.trans_le (min_le_right _ _))
        exact hab.trans hbU
      · intro a ha
        filter_upwards [Ioo_mem_nhdsGT hRi] with R hR
        exact (hUmem R ⟨hR.1, hR.2.le⟩).2.trans ha
    · filter_upwards [Ioo_mem_nhdsGT hRi] with R hR
      exact (hUmem R ⟨hR.1, hR.2.le⟩).2
  let M := fun R => S.m (U R) 0
  have hmass (u : ℝ) (hu : u ∈ Ico ui 0) : M (S.r u 0) = S.m u 0 := by
    dsimp only [M]; rw [hU u hu]
  refine ⟨M, hmass, ?_, ?_, ?_, ?_⟩
  · intro R hR
    have hu := hUmem R hR
    exact (Terminal.mass_monotonicity h.solution (U R, 0)
      ⟨hu.1, hu.2, hu.2.le, le_rfl⟩).1
  · exact h.solution.cont_m.comp (hUc.prodMk continuousOn_const) (fun R hR =>
      ⟨(hUmem R hR).1, (hUmem R hR).2, (hUmem R hR).2.le, le_rfl⟩)
  · apply ((Terminal.terminal_mass_tail h hs).2.comp hUzero).congr'
    filter_upwards [Ioo_mem_nhdsGT hRi] with R hR
    dsimp only [M, Function.comp_def]
    rw [hRU R ⟨hR.1, hR.2.le⟩]
  · rw [Terminal.lintegral_terminal_radius h.ui_neg h.solution h.mu]
    convert (Terminal.terminal_mass_tail h hs).1 using 1
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
    rw [hmass u hu, ← ENNReal.ofReal_mul
      (neg_pos.mpr (h.solution.nu_neg (u, 0) ⟨hu.1, hu.2, hu.2.le, le_rfl⟩)).le]
    congr 1
    ring

/-- [node c:exterior#exterior-small-gap]
The constructed exterior has arbitrarily small mass ratio
(charged_SF_new_version.tex:L1140–1141). The coefficient `2` is universal; the cutoff
depends on the fixed development, signed bound, profile and tolerance,
uniformly in subsequent labels. -/
theorem Exterior.exterior_small_gap (h : OriginalData ui e S) (hs : SignedTerminalBound ui S)
    (M ell : ℝ → ℝ) {R₀ ε : ℝ} (hR : 0 < R₀) (hε : 0 < ε)
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0)) :
    ∃ u₀ ∈ Ioo ui 0, ∀ p ∈ adaptiveExterior S ui u₀ ell,
      0 < ell (terminalRadius S p.1) ∧
      S.mu p.1 p.2 ≤ 2 * terminalMass S p.1 / ell (terminalRadius S p.1) ∧
      2 * terminalMass S p.1 / ell (terminalRadius S p.1) ≤ ε := by
  obtain ⟨δ, C, lam₀, hδ, hC, hlam, hgap, hflux, hmassTail, hRlim, htail, hlimit, hlog⟩ :=
    (charged_terminal_equivalence ui e S h).2 hs
  exact Exterior.exterior_small_gap_of_terminal h M ell hR hε hRlim hmass hell hsmall

/-- [node eq:charged-exterior-scalar-energy]
Exterior scalar energy and variation, charged_SF_new_version.tex:L1141–1147. The
coefficients `4` and `2` are universal. The cutoff may depend on the fixed
development, signed bound and profile, uniformly in subsequent rows and
inner endpoints. -/
theorem charged_exterior_scalar_energy {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) (M ell : ℝ → ℝ) {R₀ : ℝ} (hR : 0 < R₀)
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0)) :
    ∃ u₀ ∈ Ioo ui 0, ∀ u a, (u, a) ∈ adaptiveExterior S ui u₀ ell →
      (∫ v in a..0, ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v) ≤
        4 * terminalMass S u ∧
      eVariationOn (S.phi u) (Icc a 0) ≤
        ENNReal.ofReal (2 * Real.sqrt (terminalMass S u / ell (terminalRadius S u))) := by
  obtain ⟨δ, C, lam₀, hδ, hC, hlam, hgap, hflux, hmassTail, hRlim, htail, hlimit, hlog⟩ :=
    (charged_terminal_equivalence ui e S h).2 hs
  exact charged_exterior_scalar_energy_of_terminal h M ell hR hRlim hmass hell hsmall

/-- [node c:exterior#scalar-log-envelope]
A logarithmic scalar envelope throughout the exterior
(charged_SF_new_version.tex:L1148–1154). The positive scalar coefficient and cutoff may
depend on the fixed development, signed bound and profile, uniformly in
both subsequent labels. -/
theorem Exterior.scalar_log_envelope {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) (M ell : ℝ → ℝ) {R₀ : ℝ} (hR : 0 < R₀)
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0)) :
    ∃ C : ℝ, 0 < C ∧
    0 < C + 2 ∧ ∃ u₀ ∈ Ioo ui 0, ∀ p ∈ adaptiveExterior S ui u₀ ell,
      ‖S.phi p.1 p.2‖ ≤ (C + 2) *
        (1 + Real.sqrt (Real.log (S.r ui 0 / S.r p.1 0))) := by
  obtain ⟨δ, C, lam₀, hδ, hC, hlam, hgap, hflux, hmassTail, hRlim, htail, hlimit, hlog⟩ :=
    (charged_terminal_equivalence ui e S h).2 hs
  exact ⟨C, hC, Exterior.scalar_log_envelope_of_terminal h M ell hR hC hRlim hmass hell hsmall hlog⟩

/-- [node eq:charged-exterior-charge-pointwise]
Both the unabsorbed and absorbed charge bounds, charged_SF_new_version.tex:L1156–1182.
The coefficients `32` and `64` are universal. The scalar coefficient and
cutoff may depend on the fixed development, signed bound and profile,
uniformly in both subsequent labels. -/
theorem charged_exterior_charge_pointwise {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) (M ell : ℝ → ℝ) {R₀ : ℝ} (hR : 0 < R₀)
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0)) :
    ∃ C : ℝ, 0 < C ∧
    ∃ u₀ ∈ Ioo ui 0, ∀ p ∈ adaptiveExterior S ui u₀ ell,
      let L := (C + 2) * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r p.1 0)))
      S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 ≤
          32 * (terminalMass S p.1 / S.r p.1 p.2) *
            (1 + e ^ 2 * L ^ 2 * S.r p.1 p.2 ^ 2) ∧
        S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 ≤
          64 * (terminalMass S p.1 / S.r p.1 p.2) := by
  obtain ⟨δ, C, lam₀, hδ, hC, hlam, hgap, hflux, hmassTail, hRlim, htail, hlimit, hlog⟩ :=
    (charged_terminal_equivalence ui e S h).2 hs
  exact ⟨C, hC, charged_exterior_charge_pointwise_of_terminal h M ell hR hC hRlim hmass hell
    hellsmall hsmall hlog⟩

/-- [node c:exterior#radial-optical-coefficient]
The radial optical coefficient is controlled in the exterior
(charged_SF_new_version.tex:L1183–1191). The coefficient `132` is universal; the cutoff
depends on the fixed development, signed bound and profile, uniformly in
both subsequent labels. -/
theorem Exterior.radial_optical_coefficient {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) (M ell : ℝ → ℝ) {R₀ : ℝ} (hR : 0 < R₀)
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0)) :
    ∃ u₀ ∈ Ioo ui 0, ∀ p ∈ adaptiveExterior S ui u₀ ell,
      0 < ell (terminalRadius S p.1) ∧ 1 / 2 ≤ 1 - S.mu p.1 p.2 ∧
      |(S.mu p.1 p.2 - S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2) / (1 - S.mu p.1 p.2)| ≤
        132 * terminalMass S p.1 / S.r p.1 p.2 := by
  obtain ⟨δ, C, lam₀, hδ, hC, hlam, hgap, hflux, hmassTail, hRlim, htail, hlimit, hlog⟩ :=
    (charged_terminal_equivalence ui e S h).2 hs
  exact Exterior.radial_optical_coefficient_of_terminal h M ell hR hC hRlim hmass hell
    hellsmall hsmall hlog

/-- [node eq:charged-exterior-optics]
The exterior logarithmic incoming-expansion ratio is controlled by
`132M/ell` (charged_SF_new_version.tex:L1187–1191). The coefficient is universal; the
cutoff depends on the fixed development, signed bound and profile,
uniformly in both subsequent labels. -/
theorem charged_exterior_optics {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) (M ell : ℝ → ℝ) {R₀ : ℝ} (hR : 0 < R₀)
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0)) :
    ∃ u₀ ∈ Ioo ui 0, ∀ p ∈ adaptiveExterior S ui u₀ ell,
      0 < ell (terminalRadius S p.1) ∧
      |Real.log (S.nu p.1 p.2 / S.nu p.1 0)| ≤
        132 * terminalMass S p.1 / ell (terminalRadius S p.1) := by
  obtain ⟨δ, C, lam₀, hδ, hC, hlam, hgap, hflux, hmassTail, hRlim, htail, hlimit, hlog⟩ :=
    (charged_terminal_equivalence ui e S h).2 hs
  exact charged_exterior_optics_of_terminal h M ell hR hC hRlim hmass hell hellsmall hsmall hlog

/-- [node c:exterior#incoming-optical-majorant]
An integrable majorant for incoming optical transport
(charged_SF_new_version.tex:L1196–1200). The coefficient `264` is universal; the cutoff
depends on the fixed development, signed bound and profile, uniformly in
both subsequent labels. -/
theorem Exterior.incoming_optical_majorant {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) (M ell : ℝ → ℝ) {R₀ : ℝ} (hR : 0 < R₀)
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0)) :
    ∃ u₀ ∈ Ioo ui 0, ∀ p ∈ adaptiveExterior S ui u₀ ell,
      0 < ell (terminalRadius S p.1) ∧
      |S.rUV p.1 p.2 / S.lam p.1 p.2| ≤
        264 * (-S.nu p.1 0) * terminalMass S p.1 / ell (terminalRadius S p.1) ^ 2 := by
  obtain ⟨δ, C, lam₀, hδ, hC, hlam, hgap, hflux, hmassTail, hRlim, htail, hlimit, hlog⟩ :=
    (charged_terminal_equivalence ui e S h).2 hs
  exact Exterior.incoming_optical_majorant_of_terminal h M ell hR hC hRlim hmass hell
    hellsmall hsmall hlog

/-- [internal]
Incoming pasts stay in the constructed exterior, with strict increase
of the separation towards the past (charged_SF_new_version.tex:L1192–1195). The cutoff
depends on the fixed development, signed bound and profile, uniformly in
both subsequent labels. -/
theorem Exterior.incoming_past_invariance {ui e k : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) (M ell : ℝ → ℝ) {R₀ : ℝ} (hR : 0 < R₀)
    (hk : 0 < k ∧ k < 1 / 8)
    (hLip : LipschitzOnWith (Real.toNNReal k) ell (Ioc 0 R₀))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0)) :
    ∃ u₀ ∈ Ioo ui 0, ∀ p ∈ adaptiveExterior S ui u₀ ell,
      (∀ s ∈ Icc u₀ p.1, (s, p.2) ∈ adaptiveExterior S ui u₀ ell) ∧
      StrictAntiOn (fun s => S.r s p.2 - ell (S.r s 0)) (Icc u₀ p.1) := by
  obtain ⟨δ, C, lam₀, hδ, hC, hlam, hgap, hflux, hmassTail, hRlim, htail, hlimit, hlog⟩ :=
    (charged_terminal_equivalence ui e S h).2 hs
  exact Exterior.incoming_past_invariance_of_terminal h M ell hR hC hk hLip hRlim hmass hell
    hellsmall hsmall hlog

/-- [node c:exterior#uniform-optical-limits]
Uniform positive outgoing-expansion and incoming-ratio limits
(charged_SF_new_version.tex:L1205–1215). The positive expansion limit depends on the
fixed development and signed bound. Cutoffs may also depend on the
constructed profile and tolerance, uniformly in both subsequent labels. -/
theorem Exterior.uniform_optical_limits {ui e k : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) (M ell : ℝ → ℝ) {R₀ : ℝ} (hR : 0 < R₀)
    (hk : 0 < k ∧ k < 1 / 8)
    (hLip : LipschitzOnWith (Real.toNNReal k) ell (Ioc 0 R₀))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hint : (∫⁻ R in Ioc 0 R₀, ENNReal.ofReal (M R / ell R ^ 2)) < ⊤) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧
      Tendsto (fun u => S.lam u 0) (𝓝[<] 0) (𝓝 lam₀) ∧
    ∀ ε : ℝ, 0 < ε → ∃ u₀ ∈ Ioo ui 0, ∀ p ∈ adaptiveExterior S ui u₀ ell,
      |S.lam p.1 p.2 - lam₀| < ε ∧ |S.nu p.1 p.2 / S.nu p.1 0 - 1| < ε := by
  obtain ⟨δ, C, lam₀, hδ, hC, hlam, hgap, hflux, hmassTail, hRlim, htail, hlimit, hlog⟩ :=
    (charged_terminal_equivalence ui e S h).2 hs
  exact ⟨lam₀, hlam, hlimit, Exterior.uniform_optical_limits_of_terminal h M ell hR hC hk hLip hRlim
    hmass hell hellsmall hsmall hint hlog hlam hlimit⟩

/-- [node c:exterior#exterior-lambda-lower-bound]
A positive uniform exterior lower expansion bound
(charged_SF_new_version.tex:L1201–1204). The bound and cutoff may depend on the fixed
development, signed bound and constructed profile, uniformly in both
subsequent labels. -/
theorem Exterior.exterior_lambda_lower_bound {ui e k : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) (M ell : ℝ → ℝ) {R₀ : ℝ} (hR : 0 < R₀)
    (hk : 0 < k ∧ k < 1 / 8)
    (hLip : LipschitzOnWith (Real.toNNReal k) ell (Ioc 0 R₀))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hint : (∫⁻ R in Ioc 0 R₀, ENNReal.ofReal (M R / ell R ^ 2)) < ⊤) :
    ∃ c > 0, ∃ u₀ ∈ Ioo ui 0,
      ∀ p ∈ adaptiveExterior S ui u₀ ell, c ≤ S.lam p.1 p.2 := by
  obtain ⟨δ, C, lam₀, hδ, hC, hlam, hgap, hflux, hmassTail, hRlim, htail, hlimit, hlog⟩ :=
    (charged_terminal_equivalence ui e S h).2 hs
  exact Exterior.exterior_lambda_lower_bound_of_terminal h M ell hR hC hk hLip hRlim hmass hell
    hellsmall hsmall hint hlog hlam hlimit

/-- [node eq:charged-frontier-speed]
The actual frontier has the a.e. speed identity and local inverse
distance bounds (charged_SF_new_version.tex:L1215–1223). The entry label depends on
the fixed development, signed bound, profile and slope. The local
constants `L,m` may also depend on the proper interval, and precede
every pair of labels in that interval. -/
theorem charged_frontier_speed {k : ℝ}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) (M ell : ℝ → ℝ) {R₀ : ℝ} (hR : 0 < R₀)
    (hk : 0 < k ∧ k < 1 / 8)
    (hLip : LipschitzOnWith (Real.toNNReal k) ell (Ioc 0 R₀))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0)) :
    ∃ u₀ ∈ Ioo ui 0, ∃ V : ℝ → ℝ,
      (∀ u ∈ Ico u₀ 0, u < V u ∧ V u < 0 ∧ S.r u (V u) = ell (S.r u 0)) ∧
      StrictMonoOn V (Ico u₀ 0) ∧ Tendsto V (𝓝[<] 0) (𝓝 0) ∧
      (∀ a b, u₀ ≤ a → a ≤ b → b < 0 →
        ∃ L > 0, ∃ m > 0,
          LipschitzOnWith (Real.toNNReal L) V (Icc a b) ∧
          (∀ u ∈ Icc a b, ∀ w ∈ Icc a b, m * dist u w ≤ dist (V u) (V w)) ∧
          (∀ᵐ u ∂volume.restrict (Icc a b),
            S.lam u (V u) * deriv V u =
                -S.nu u (V u) - deriv ell (S.r u 0) * (-S.nu u 0) ∧
              (1 / 2 - k) * (-S.nu u 0) ≤ S.lam u (V u) * deriv V u ∧
              0 < S.lam u (V u) * deriv V u)) := by
  obtain ⟨δ, C, lam₀, hδ, hC, hlam, hgap, hflux, hmassTail, hRlim, htail, hlimit, hlog⟩ :=
    (charged_terminal_equivalence ui e S h).2 hs
  exact charged_frontier_speed_of_terminal h M ell hR hC hk hLip hRlim hmass hell
    hellsmall hsmall hlog

/-- [internal]
On every comparable late exterior annulus, the original equations and
terminal proposition give the Maxwell oscillation bound
(charged_SF_new_version.tex:L1170–1177). The scalar constant and cutoff may depend on
the fixed development, signed bound and adaptive profile, uniformly in
all subsequent annuli and labels; the coefficient `4` is universal. -/
theorem Exterior.annular_charge_oscillation (h : OriginalData ui e S)
    (hs : SignedTerminalBound ui S) (M ell : ℝ → ℝ) {R₀ : ℝ} (hR : 0 < R₀)
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0)) :
    ∃ C : ℝ, 0 < C ∧ ∃ u₀ ∈ Ioo ui 0,
      ∀ u a b r, (u, a) ∈ adaptiveExterior S ui u₀ ell →
        0 < r → u < a → a ≤ b → b ≤ 0 →
        (∀ v ∈ Icc a b, S.r u v ≤ 2 * r) →
        S.r u b - S.r u a ≤ r →
        ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
          |S.Q u s - S.Q u t| ≤
            4 * |e| * (C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) *
              r * Real.sqrt (terminalMass S u * r) := by
  obtain ⟨C, hC, hC2, ul, hul, hlog⟩ := Exterior.scalar_log_envelope h hs M ell hR hmass hell hsmall
  obtain ⟨ue, hue, henergy⟩ := charged_exterior_scalar_energy h hs M ell hR hmass hell hsmall
  refine ⟨C + 2, hC2, max ul ue, ⟨lt_max_of_lt_left hul.1, max_lt hul.2 hue.2⟩, ?_⟩
  intro u a b r hp hr hua hab hb hrb hlen
  have hseg : outSeg u a 0 ⊆ origDomain ui :=
    (outSeg_subset_origDomain_iff (hab.trans hb)).2
      ⟨hp.1.1, hp.1.2.1, hua.le, le_rfl⟩
  have hps (v : ℝ) (hv : v ∈ Icc a 0) : (u, v) ∈ adaptiveExterior S ui ul ell :=
    ⟨hseg ⟨rfl, hv⟩, (le_max_left ul ue).trans hp.2.1,
      hp.2.2.trans (Exterior.outgoing_radius_mono h hua.le hv.1
        (fun _ hx => hseg (outSeg_subset_outSeg le_rfl hv.2 hx)))⟩
  have hc := ((Calculus.continuousOn_out_section h.solution.cont_theta hseg).div
    (Complex.continuous_ofReal.comp_continuousOn
      (Calculus.continuousOn_out_section h.solution.cont_lam hseg))
    (fun v hv => Complex.ofReal_ne_zero.mpr
      (h.solution.lam_pos (u, v) (hseg ⟨rfl, hv⟩)).ne')).norm.pow 2
  have hi := (hc.mul
    (Calculus.continuousOn_out_section h.solution.cont_lam hseg)).intervalIntegrable_of_Icc
    (μ := volume) (hab.trans hb)
  have hE := (intervalIntegral.integral_mono_interval le_rfl hab hb
    ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun v hv =>
      mul_nonneg (sq_nonneg _) (h.solution.lam_pos (u, v)
        (hseg ⟨rfl, hv.1.le, hv.2⟩)).le)) hi).trans
    (henergy u a ⟨hp.1, (le_max_right ul ue).trans hp.2.1, hp.2.2⟩).1
  exact Exterior.annular_charge_oscillation_of_energy h hr (by positivity) hua hab
    (fun p hq => hseg (outSeg_subset_outSeg le_rfl hb hq)) hrb hlen
    (fun v hv => hlog (u, v) (hps v ⟨hv.1, hv.2.trans hb⟩)) hE

/-- [internal]
At every sufficiently late adaptive exterior point, select the source's
annulus and prove its Maxwell oscillation (charged_SF_new_version.tex:L1162–1177).
The scalar constant and entry depend on the fixed development, signed
bound and admissible profile, uniformly in the point and both annular
labels. The coefficient `4` is universal. -/
theorem Exterior.annular_charge_oscillation_at_point (h : OriginalData ui e S)
    (hs : SignedTerminalBound ui S) (M ell : ℝ → ℝ) {R₀ : ℝ} (hR : 0 < R₀)
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0)) :
    ∃ C > 0, ∃ u₀ ∈ Ioo ui 0, ∀ u v,
      (u, v) ∈ adaptiveExterior S ui u₀ ell →
      ∃ a b, u < a ∧ a ≤ v ∧ v ≤ b ∧ b ≤ 0 ∧ ell (terminalRadius S u) ≤ S.r u a ∧
        S.r u v / 2 ≤ S.r u a ∧ S.r u b ≤ 2 * S.r u v ∧
        S.r u v / 2 ≤ S.r u b - S.r u a ∧ S.r u b - S.r u a ≤ S.r u v ∧
        ((a = v ∧ S.r u b = 2 * S.r u v) ∨
          (b = 0 ∧ S.r u a = terminalRadius S u / 2)) ∧
        (∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
          |S.Q u s - S.Q u t| ≤
            4 * |e| * (C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) *
              S.r u v * Real.sqrt (terminalMass S u * S.r u v)) := by
  obtain ⟨C, hC, uo, huo, hosc⟩ :=
    Exterior.annular_charge_oscillation h hs M ell hR hmass hell hsmall
  have hcollapse := Terminal.terminal_radius_collapse h.ui_neg h.solution h.mu
  have hpos : ∀ᶠ u in 𝓝[<] (0:ℝ), 0 < S.r u 0 := by
    filter_upwards [Ioo_mem_nhdsLT h.ui_neg] with u hu
    exact h.solution.r_pos (u, 0) ⟨hu.1.le, hu.2, hu.2.le, le_rfl⟩ hu.2
  have ht : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hcollapse, hpos⟩
  have he : ∀ᶠ u in 𝓝[<] (0:ℝ),
      0 < S.r u 0 ∧ S.r u 0 < R₀ ∧ ell (S.r u 0) / S.r u 0 < 1 / 2 := by
    filter_upwards [hpos, hcollapse.eventually (Iio_mem_nhds hR),
      (hellsmall.comp ht).eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1/2))]
      with u hu hr hratio
    exact ⟨hu, hr, hratio⟩
  obtain ⟨d, hd, hdb⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp he
  obtain ⟨ug, hug, hug0⟩ := exists_between (max_lt hd h.ui_neg)
  refine ⟨C, hC, max uo ug, ⟨lt_max_of_lt_left huo.1, max_lt huo.2 hug0⟩, ?_⟩
  intro u v hp
  have hgeo := hdb (show u ∈ Ioo d 0 from
    ⟨(le_max_left d ui).trans_lt (hug.trans_le ((le_max_right uo ug).trans hp.2.1)), hp.1.2.1⟩)
  have hℓ := hell (S.r u 0) ⟨hgeo.1, hgeo.2.1.le⟩
  have hℓR : 2 * ell (terminalRadius S u) ≤ terminalRadius S u := by
    have hh := (div_lt_iff₀ hgeo.1).mp hgeo.2.2
    dsimp only [terminalRadius]; linarith only [hh]
  have huv : u < v := by
    by_contra hn
    have heq : v = u := le_antisymm (le_of_not_gt hn) hp.1.2.2.1
    have hz := (h.solution.axis u
      (show (u, u) ∈ origDomain ui from ⟨hp.1.1, hp.1.2.1, le_rfl, hp.1.2.1.le⟩)).1
    have hr := hℓ.trans_le hp.2.2
    rw [heq, hz] at hr
    exact (lt_irrefl 0) hr
  obtain ⟨a, b, hua, hav, hvb, hb, hℓa, hra, hrb, hlo, hhi, hcase⟩ :=
    Exterior.annulus_labels h hp.1 huv hℓ hp.2.2 hℓR
  have hab := hav.trans hvb
  have hseg : outSeg u a b ⊆ origDomain ui :=
    (outSeg_subset_origDomain_iff hab).2 ⟨hp.1.1, hp.1.2.1, hua.le, hb⟩
  refine ⟨a, b, hua, hav, hvb, hb, hℓa, hra, hrb, hlo, hhi, hcase, ?_⟩
  exact hosc u a b (S.r u v)
    ⟨hseg ⟨rfl, le_rfl, hab⟩, (le_max_left uo ug).trans hp.2.1, hℓa⟩
    (h.solution.r_pos (u, v) hp.1 huv) hua hab hb
    (fun w hw => (Exterior.outgoing_radius_mono h (hua.le.trans hw.1) hw.2
      (fun p hq => hseg (outSeg_subset_outSeg hw.1 le_rfl hq))).trans hrb) hhi

end EmcsfAcExtension.Global
