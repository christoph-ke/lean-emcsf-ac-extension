module

public import EmcsfAcExtension.Global.Exterior.DerivativeSourceIncomingWeight
public import EmcsfAcExtension.Global.Exterior.DerivativeSourceIncomingRadius
public import EmcsfAcExtension.Global.Exterior.FrontierIncomingIntegral
public import EmcsfAcExtension.Global.Exterior.VariationTailsTerminalBounds

/-! # The literal common radius majorant for incoming transport

The radial scalar-field profile is the actual outgoing supremum, transported
by the canonical terminal-radius inverse. Every carrier and final time is
chosen after the same exterior, supremum and radius weight. The numerical
constant `296=264+32` is uniform in the solution, coupling and carrier.
Source: `charged_SF_new_version.tex:L1356–L1360`, L1405–L1408; internal project record (I1)–(I2).
-/

public section

open Set MeasureTheory Filter Topology Complex

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
The continuous incoming covariant derivative of the normalized scalar.
This is the literal source in normalized scalar transport, with no
boundary trace or outgoing derivative in its definition. -/
@[expose] noncomputable def incomingCovariantSource (e : ℝ) (S : Fields) (u v : ℝ) : ℂ :=
  (-S.nu u v / ((1 - S.mu u v) * S.r u v) : ℝ) *
    ((S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) *
      (S.theta u v / (S.lam u v : ℂ)) + I * e * S.Q u v * S.phi u v)

/-- [internal]
The exact two-term common radius majorant, with the actual row supremum.
It is integrable with a vanishing radius tail and bounds incoming transport
on every continuous exterior carrier. The cutoff and radial profile precede
all carriers, both endpoints and cylinder radii. The coefficient `296` is
numerical, uniformly in all data and scales. -/
theorem incoming_transport_radius_majorant_of_terminal {ui e C k₀ R₀ : ℝ} {S : Fields}
    (h : OriginalData ui e S) (M ell : ℝ → ℝ) (hR : 0 < R₀) (hC : 0 < C)
    (hk₀ : 0 < k₀ ∧ k₀ < 1 / 8)
    (hLip : LipschitzOnWith (Real.toNNReal k₀) ell (Ioc 0 R₀))
    (hMc : ContinuousOn M (Ioc 0 R₀)) (hM : ∀ R ∈ Ioc 0 R₀, 0 ≤ M R)
    (hAfinite : (∫⁻ R in Ioc 0 R₀, ENNReal.ofReal (M R / ell R ^ 2)) < ⊤)
    (hcollapse : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hphi : ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) :
    ∃ c ∈ Ioo ui 0, ∃ t SF : ℝ → ℝ,
      (∀ u ∈ Ico c 0, u < t u ∧ t u < 0 ∧ S.r u (t u) = ell (S.r u 0)) ∧
      ContinuousOn t (Ico c 0) ∧ ContinuousOn SF (Ioc 0 (S.r c 0)) ∧
      (∀ u ∈ Ico c 0, SF (S.r u 0) = outgoingFieldSup S t u) ∧
      let L := fun R => (C + 2) * (1 + Real.sqrt (Real.log (S.r ui 0 / R)))
      let T := incomingRadiusWeight e M ell L SF
      IntegrableOn T (Ioc 0 (S.r c 0)) ∧
      Tendsto (fun ρ => ∫ R in Ioc 0 ρ, T R) (𝓝[>] 0) (𝓝 0) ∧
      (∀ a b, c ≤ a → a ≤ b → b < 0 → ∀ V : ℝ → ℝ,
        ContinuousOn V (Icc a b) →
        (∀ u ∈ Icc a b, (u, V u) ∈ adaptiveExterior S ui c ell) →
        (∫ u in a..b, ‖incomingCovariantSource e S u (V u)‖) ≤
          296 * ∫ R in Ioc 0 (S.r a 0), T R) ∧
      (∀ ε > 0, ∃ u₀ ∈ Ioo c 0, ∀ a b, u₀ ≤ a → a ≤ b → b < 0 →
        ∀ V : ℝ → ℝ, ContinuousOn V (Icc a b) →
          (∀ u ∈ Icc a b, (u, V u) ∈ adaptiveExterior S ui c ell) →
          (∫ u in a..b, ‖incomingCovariantSource e S u (V u)‖) ≤ ε) := by
  obtain ⟨uf, huf, B, hB, hfield⟩ := outgoing_field_bound_of_terminal h M ell hR hC
    hk₀ hLip hMc hM hAfinite hcollapse hmass hell hellsmall hsmall hphi
  obtain ⟨ug, hug, t, hroot, _hmono, _htt, hsegments⟩ := charged_frontier_speed_of_terminal
    h M ell hR hC hk₀ hLip hcollapse hmass hell hellsmall hsmall hphi
  obtain ⟨up, hup, hpoint⟩ := incoming_transport_bound_of_terminal h M ell hR hC
    hcollapse hmass hell hellsmall hsmall hphi
  have hRi : 0 < S.r ui 0 := h.solution.r_pos (ui, 0)
    ⟨le_rfl, h.ui_neg, h.ui_neg.le, le_rfl⟩ h.ui_neg
  obtain ⟨Rc, hRc, iA, iG, _⟩ := forcing_integrability_of_terminal_profiles
    (e := e) hRi (show 0 ≤ C + 2 by linarith) hR hMc hLip.continuousOn hM
    hell hellsmall hsmall hAfinite
  obtain ⟨c, hc, hcR⟩ := (show ∀ᶠ u in 𝓝[<] (0 : ℝ),
      u ∈ Ioo (max ug (max uf up)) 0 ∧ S.r u 0 < Rc from by
    filter_upwards [Ioo_mem_nhdsLT (max_lt hug.2 (max_lt huf.2 hup.2)),
      hcollapse.eventually (Iio_mem_nhds hRc.1)] with u hu hr
    exact ⟨hu, hr⟩).exists
  have huc : c ∈ Ioo ui 0 := ⟨hug.1.trans ((le_max_left _ _).trans_lt hc.1), hc.2⟩
  have hcg : ug ≤ c := (le_max_left _ _).trans hc.1.le
  have hcf : uf ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans hc.1.le)
  have hcp : up ≤ c := (le_max_right _ _).trans ((le_max_right _ _).trans hc.1.le)
  have hrootc (u : ℝ) (hu : u ∈ Ico c 0) := hroot u ⟨hcg.trans hu.1, hu.2⟩
  have ht : ContinuousOn t (Ico c 0) := by
    apply continuousOn_boundary_Ico_of_proper_segments
    intro b hcb hb
    obtain ⟨D, _, m, _, hD, _⟩ := hsegments c b hcg hcb hb
    exact hD.continuousOn
  have hfieldc : ∀ p ∈ adaptiveExterior S ui c ell,
      ‖S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ)‖ ≤ B :=
    fun p hp => hfield p ⟨hp.1, hcf.trans hp.2.1, hp.2.2⟩
  have hsup := outgoingFieldSup_bounds h huc.1.le
    (fun u hu => ⟨(hrootc u hu).1, (hrootc u hu).2.1.le, (hrootc u hu).2.2⟩) hfieldc
  have csup := outgoingFieldSup_continuousOn h huc.1.le ht
    (fun u hu => ⟨(hrootc u hu).1, (hrootc u hu).2.1.le⟩)
  have hmem (u : ℝ) (hu : u ∈ Ico c 0) : (u, 0) ∈ origDomain ui :=
    ⟨huc.1.le.trans hu.1, hu.2, hu.2.le, le_rfl⟩
  have cR : ContinuousOn (fun u => S.r u 0) (Ico c 0) :=
    h.solution.cont_r.comp (continuous_id.prodMk continuous_const).continuousOn hmem
  have hanti := (Terminal.terminal_radius_strictAntiOn h.solution).mono
    (Ico_subset_Ico_left huc.1.le)
  have hRp (u : ℝ) (hu : u ∈ Ico c 0) := h.solution.r_pos (u, 0) (hmem u hu) hu.2
  have hRu (u : ℝ) (hu : u ∈ Ico c 0) : S.r u 0 ∈ Ioc 0 (S.r c 0) :=
    ⟨hRp u hu, hanti.antitoneOn ⟨le_rfl, huc.2⟩ hu hu.1⟩
  obtain ⟨SF, cSF, hSFrow, hSF⟩ := radial_profile_of_terminal_order huc.2 cR hanti hRp
    hcollapse csup (fun u hu => ⟨(hsup u hu).1, (hsup u hu).2.1⟩)
  let L := fun R => (C + 2) * (1 + Real.sqrt (Real.log (S.r ui 0 / R)))
  let T := incomingRadiusWeight e M ell L SF
  have hsub : Ioc 0 (S.r c 0) ⊆ Ioc 0 R₀ := Ioc_subset_Ioc_right (hcR.le.trans hRc.2)
  have hsubRc : Ioc 0 (S.r c 0) ⊆ Ioc 0 Rc := Ioc_subset_Ioc_right hcR.le
  have hL0 (R : ℝ) : 0 ≤ L R := by dsimp only [L]; positivity
  have iT : IntegrableOn T (Ioc 0 (S.r c 0)) := incomingRadiusWeight_integrable
    (hMc.mono hsub) (hLip.continuousOn.mono hsub)
    (logarithmic_envelope_continuousOn hRi) cSF
    (fun R hRR => hM R (hsub hRR)) (fun R hRR => hell R (hsub hRR))
    (fun R _ => hL0 R) hSF (iA.mono_set hsubRc) (iG.mono_set hsubRc)
  have hT0 (R : ℝ) (hRR : R ∈ Ioc 0 (S.r c 0)) : 0 ≤ T R :=
    incomingRadiusWeight_nonneg (hM R (hsub hRR)) (hSF R hRR).1 (hL0 R)
  have hquant (a b : ℝ) (hca : c ≤ a) (hab : a ≤ b) (hb : b < 0)
      (V : ℝ → ℝ) (hV : ContinuousOn V (Icc a b))
      (hVmem : ∀ u ∈ Icc a b, (u, V u) ∈ adaptiveExterior S ui c ell) :
      (∫ u in a..b, ‖incomingCovariantSource e S u (V u)‖) ≤
        296 * ∫ R in Ioc 0 (S.r a 0), T R := by
    have hlabel (u : ℝ) (hu : u ∈ Icc a b) : t u ≤ V u := by
      have hp := hVmem u hu
      have htu := hrootc u ⟨hca.trans hu.1, hu.2.trans_lt hb⟩
      apply le_of_not_gt
      intro hvt
      have hh := outgoing_radius_strictMono h ⟨hp.1.1, hp.1.2.1⟩
        ⟨hp.1.2.2.1, hp.1.2.2.2⟩ ⟨htu.1.le, htu.2.1.le⟩ hvt
      rw [htu.2.2] at hh
      exact (not_lt_of_ge hp.2.2) hh
    have hproper (u : ℝ) (hu : u ∈ Icc a b) : u < V u :=
      (hrootc u ⟨hca.trans hu.1, hu.2.trans_lt hb⟩).1.trans_le (hlabel u hu)
    have hcont := continuousOn_covariant_incoming_source h.solution hV
      (fun u hu => (hVmem u hu).1) hproper
    apply incoming_integral_le_radius_tail h ⟨huc.1.le, huc.2⟩ hca hab hb
      (by norm_num : (0 : ℝ) ≤ 296) iT hT0
      (hcont.norm.intervalIntegrable_of_Icc hab)
    intro u hu
    have hp := hVmem u hu
    have htime : u ∈ Ico c 0 := ⟨hca.trans hu.1, hu.2.trans_lt hb⟩
    have hr := hRu u htime
    have hR0 := hsub hr
    have hn := (neg_pos.mpr (h.solution.nu_neg (u, 0) (hmem u htime))).le
    have hAn : 0 ≤ M (S.r u 0) / ell (S.r u 0) ^ 2 := by
      exact div_nonneg (hM _ hR0) (sq_nonneg _)
    have hf := (hsup u htime).2.2 (V u) ⟨hlabel u hu, hp.1.2.2.2⟩
    rw [← hSFrow u htime] at hf
    have hpbound := hpoint (u, V u) ⟨hp.1, hcp.trans hp.2.1, hp.2.2⟩
    rw [terminalMass_def, ← hmass u ⟨hp.1.1, hp.1.2.1⟩] at hpbound
    dsimp only [terminalRadius] at hpbound
    have hfc := mul_le_mul_of_nonneg_left hf (by positivity :
      0 ≤ 264 * (M (S.r u 0) / ell (S.r u 0) ^ 2))
    have hfc' := mul_le_mul_of_nonneg_left
      (add_le_add_right hfc (32 * |e| * L (S.r u 0) *
        Real.sqrt (M (S.r u 0) / ell (S.r u 0)))) hn
    have h₁ := mul_nonneg hn (mul_nonneg hAn (hSF _ hr).1)
    have h₂ : 0 ≤ (-S.nu u 0) * (|e| * L (S.r u 0) *
        Real.sqrt (M (S.r u 0) / ell (S.r u 0))) := by positivity
    change ‖incomingCovariantSource e S u (V u)‖ ≤ _ at hpbound
    dsimp only [incomingCovariantSource] at hpbound
    dsimp only [incomingRadiusWeight, T]
    dsimp only [L] at hfc' h₂ ⊢
    nlinarith only [hpbound, hfc', h₁, h₂]
  have hRcp : 0 < S.r c 0 := hRp c ⟨le_rfl, huc.2⟩
  have htail := radius_integral_tail_tendsto hRcp iT
  refine ⟨c, huc, t, SF, hrootc, ht, cSF, hSFrow, iT, htail, hquant, ?_⟩
  have hrpos : ∀ᶠ u in 𝓝[<] (0 : ℝ), 0 < S.r u 0 := by
    filter_upwards [Ioo_mem_nhdsLT h.ui_neg] with u hu
    exact h.solution.r_pos (u, 0) ⟨hu.1.le, hu.2, hu.2.le, le_rfl⟩ hu.2
  have hRt : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hcollapse, hrpos⟩
  have htzero := (htail.comp hRt).const_mul (296 : ℝ)
  simp only [mul_zero] at htzero
  intro ε hε
  obtain ⟨d, hd, hdb⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp
    (htzero.eventually (Iio_mem_nhds hε))
  let u₀ := max d c / 2
  have hu₀ : u₀ ∈ Ioo c 0 := by
    have hh := max_lt hd huc.2
    dsimp only [u₀]
    constructor <;> linarith [le_max_right d c]
  refine ⟨u₀, hu₀, ?_⟩
  intro a b ha hab hb V hV hVm
  have hda : d < a := by
    have hh := max_lt hd huc.2
    dsimp only [u₀] at ha
    linarith [le_max_left d c]
  exact (hquant a b (hu₀.1.le.trans ha) hab hb V hV hVm).trans
    (hdb ⟨hda, hab.trans_lt hb⟩).le

end EmcsfAcExtension.Global.Exterior
