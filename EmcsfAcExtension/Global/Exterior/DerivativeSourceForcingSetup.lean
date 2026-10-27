module

public import EmcsfAcExtension.Global.Exterior.DerivativeSourceForcingTerminal
public import EmcsfAcExtension.Global.Exterior.VariationTailsMajorant
public import EmcsfAcExtension.Global.Exterior.VariationTailsRadius
public import EmcsfAcExtension.Global.Exterior.OpticsTerminal
public import EmcsfAcExtension.Global.Exterior.FrontierIntegrability

/-! # Terminal setup for the exterior variation argument

All frontier, optical, history and integrability inputs are derived from
the original solution and the approved terminal/adaptive handoff. The
weights are constructed as `k=20744 n M/ell²`, `q=20480 n G`.
Their coefficients are numerical and uniform; the cutoff and local
bi-Lipschitz constants depend only on the fixed terminal inputs and,
for the latter, the stated proper interval. Source: `charged_SF_new_version.tex:L1337–L1391`,
approved internal project record (M3)–(M4).
-/

public section

open Set MeasureTheory Filter Topology
open scoped NNReal

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
The actual late frontier and integrable time weights needed for the
moving-interval argument. No density, variation or time-integrability
profile is assumed. The radial mass inputs are the approved terminal
adaptive outputs. The weights have universal coefficients `20744` and
`20480`; proper inverse constants precede every pair of labels. -/
theorem terminal_derivative_forcing_setup {ui e C k₀ R₀ : ℝ} {S : Fields}
    (h : OriginalData ui e S) (M ell : ℝ → ℝ) (hR : 0 < R₀) (hC : 0 < C)
    (hk₀ : 0 < k₀ ∧ k₀ < 1 / 8)
    (hLip : LipschitzOnWith (Real.toNNReal k₀) ell (Ioc 0 R₀))
    (hMc : ContinuousOn M (Ioc 0 R₀))
    (hM : ∀ R ∈ Ioc 0 R₀, 0 ≤ M R)
    (hAfinite : (∫⁻ R in Ioc 0 R₀, ENNReal.ofReal (M R / ell R ^ 2)) < ⊤)
    (hcollapse : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hphi : ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) :
    ∃ c ∈ Ioo ui 0, ∃ t k q : ℝ → ℝ,
      (∀ u ∈ Ico c 0, u < t u ∧ t u < 0 ∧ S.r u (t u) = ell (S.r u 0)) ∧
      StrictMonoOn t (Ico c 0) ∧ Tendsto t (𝓝[<] 0) (𝓝 0) ∧
      (∀ a b, c ≤ a → a ≤ b → b < 0 → ∃ K L : ℝ≥0,
        LipschitzOnWith K t (uIcc a b) ∧
        AntilipschitzWith L ((uIcc a b).domRestrict t)) ∧
      IntervalIntegrable k volume c 0 ∧ IntervalIntegrable q volume c 0 ∧
      (∀ u ∈ Ico c 0, 0 ≤ k u ∧ 0 ≤ q u) ∧
      (∀ p ∈ adaptiveExterior S ui c ell,
        |S.rUV p.1 p.2 / S.lam p.1 p.2| ≤ k p.1) ∧
      (∀ a u, ui ≤ a → a ≤ u → u ∈ Ico c 0 →
        (∫ v in t u..0, densityModulusHistory e S a (u, v)) ≤
          k u * (eVariationOn (S.a u) (Icc (t u) 0)).toReal + q u) ∧
      (∀ u ∈ Ico c 0, (∫ v in t u..0, ‖rawDensitySource e S u v‖) ≤
        k u * (eVariationOn (S.a u) (Icc (t u) 0)).toReal + q u) := by
  have hRi : 0 < S.r ui 0 := h.solution.r_pos (ui, 0)
    ⟨le_rfl, h.ui_neg, h.ui_neg.le, le_rfl⟩ h.ui_neg
  obtain ⟨Rc, hRc, iA, iG, _hAtail, _hGtail⟩ := forcing_integrability_of_terminal_profiles
    (e := e) hRi (show 0 ≤ C + 2 by linarith) hR hMc hLip.continuousOn hM
    hell hellsmall hsmall hAfinite
  obtain ⟨ug, hug, t, hroot, htmono, htt, hproper⟩ := charged_frontier_speed_of_terminal
    h M ell hR hC hk₀ hLip hcollapse hmass hell hellsmall hsmall hphi
  obtain ⟨uh, huh, hhistory⟩ := density_history_majorant_of_terminal h M ell hR hC
    hcollapse hmass hell hellsmall hsmall hphi
  obtain ⟨uo, huo, hopt⟩ := incoming_optical_majorant_of_terminal h M ell hR hC
    hcollapse hmass hell hellsmall hsmall hphi
  obtain ⟨us, hus, hsource⟩ := source_variation_majorant_of_terminal h M ell hR hC
    hcollapse hmass hell hellsmall hsmall hphi
  have hlate : ∀ᶠ u in 𝓝[<] (0 : ℝ), S.r u 0 < Rc :=
    hcollapse.eventually (Iio_mem_nhds hRc.1)
  obtain ⟨d, hd, hdb⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hlate
  let ur := max d ui / 2
  have hur : ur ∈ Ioo ui 0 := by
    have hh := max_lt hd h.ui_neg
    dsimp [ur]
    constructor <;> linarith [le_max_right d ui]
  let c := max ug (max uh (max uo (max us ur)))
  have hc : c ∈ Ioo ui 0 :=
    ⟨lt_max_of_lt_left hug.1, max_lt hug.2 (max_lt huh.2 (max_lt huo.2 (max_lt hus.2 hur.2)))⟩
  have hcg : ug ≤ c := le_max_left _ _
  have hch : uh ≤ c := (le_max_left uh (max uo (max us ur))).trans (le_max_right _ _)
  have hco : uo ≤ c := (le_max_left uo (max us ur)).trans
    ((le_max_right uh (max uo (max us ur))).trans (le_max_right _ _))
  have hcs : us ≤ c := (le_max_left us ur).trans ((le_max_right uo (max us ur)).trans
    ((le_max_right uh (max uo (max us ur))).trans (le_max_right _ _)))
  have hcr : ur ≤ c := (le_max_right us ur).trans ((le_max_right uo (max us ur)).trans
    ((le_max_right uh (max uo (max us ur))).trans (le_max_right _ _)))
  have hdomain (u : ℝ) (hu : u ∈ Ico c 0) : (u, 0) ∈ origDomain ui :=
    ⟨hc.1.le.trans hu.1, hu.2, hu.2.le, le_rfl⟩
  have hRu (u : ℝ) (hu : u ∈ Ico c 0) : S.r u 0 ∈ Ioc 0 Rc := by
    refine ⟨h.solution.r_pos (u, 0) (hdomain u hu) hu.2, ?_⟩
    have hud : d < u := by
      have hh := hcr.trans hu.1
      have hm := max_lt hd h.ui_neg
      dsimp [ur] at hh
      linarith [le_max_left d ui]
    exact (hdb ⟨hud, hu.2⟩).le
  let L := fun R => (C + 2) * (1 + Real.sqrt (Real.log (S.r ui 0 / R)))
  let k := fun u => 20744 * (-S.nu u 0) * (M (S.r u 0) / ell (S.r u 0) ^ 2)
  let q := fun u => 20480 * (-S.nu u 0) * exteriorForcing e M ell L (S.r u 0)
  have ik : IntegrableOn k (Ico c 0) := by
    have hi := (integrable_terminal_radius_pullback h ⟨hc.1.le, hc.2⟩
      (hRu c ⟨le_rfl, hc.2⟩).2 iA).const_mul (20744 : ℝ)
    change Integrable k (volume.restrict (Ico c 0))
    apply hi.congr
    filter_upwards with u
    dsimp only [k]
    ring
  have iq : IntegrableOn q (Ico c 0) := by
    have hi := (integrable_terminal_radius_pullback h ⟨hc.1.le, hc.2⟩
      (hRu c ⟨le_rfl, hc.2⟩).2 iG).const_mul (20480 : ℝ)
    change Integrable q (volume.restrict (Ico c 0))
    apply hi.congr
    filter_upwards with u
    dsimp only [q, L]
    ring
  have hweights (u : ℝ) (hu : u ∈ Ico c 0) : 0 ≤ k u ∧ 0 ≤ q u := by
    have hr := hRu u hu
    have hR0 : S.r u 0 ∈ Ioc 0 R₀ := ⟨hr.1, hr.2.trans hRc.2⟩
    have hm := hM (S.r u 0) hR0
    have he := (hell (S.r u 0) hR0).le
    have hn := (neg_pos.mpr (h.solution.nu_neg (u, 0) (hdomain u hu))).le
    have hl : 0 ≤ L (S.r u 0) := by dsimp [L]; positivity
    dsimp [k, q, exteriorForcing]
    constructor <;> positivity
  refine ⟨c, hc, t, k, q, ?_, htmono.mono (Ico_subset_Ico_left hcg), htt,
    ?_, (intervalIntegrable_iff_integrableOn_Ico_of_le hc.2.le).2 ik,
    (intervalIntegrable_iff_integrableOn_Ico_of_le hc.2.le).2 iq, hweights, ?_, ?_, ?_⟩
  · intro u hu
    exact hroot u ⟨hcg.trans hu.1, hu.2⟩
  · intro a b hca hab hb
    obtain ⟨B, _hB, m, hm, hLipT, hinv, _hspeed⟩ :=
      hproper a b (hcg.trans hca) hab hb
    refine ⟨Real.toNNReal B, Real.toNNReal m⁻¹, ?_, ?_⟩
    · simpa only [uIcc_of_le hab] using hLipT
    · apply boundary_antilipschitz_of_inverse_distance hm
      simpa only [uIcc_of_le hab] using hinv
  · intro p hp
    have hu : p.1 ∈ Ico c 0 := ⟨hp.2.1, hp.1.2.1⟩
    have hh := (hopt p ⟨hp.1, hco.trans hp.2.1, hp.2.2⟩).2
    have hm := hmass p.1 ⟨hp.1.1, hp.1.2.1⟩
    have hh' : |S.rUV p.1 p.2 / S.lam p.1 p.2| ≤
        264 * (-S.nu p.1 0) * (M (S.r p.1 0) / ell (S.r p.1 0) ^ 2) := by
      simpa only [terminalMass, terminalRadius, ← hm, mul_div_assoc] using hh
    refine hh'.trans ?_
    have hn := (neg_pos.mpr (h.solution.nu_neg (p.1, 0) (hdomain p.1 hu))).le
    have hm0 := hM (S.r p.1 0) ⟨(hRu p.1 hu).1, (hRu p.1 hu).2.trans hRc.2⟩
    have hp0 : 0 ≤ (-S.nu p.1 0) * (M (S.r p.1 0) / ell (S.r p.1 0) ^ 2) := by positivity
    dsimp [k]
    nlinarith only [hp0]
  · intro a u hia hau hu
    have ht := hroot u ⟨hcg.trans hu.1, hu.2⟩
    have hp : (u, t u) ∈ adaptiveExterior S ui uh ell :=
      ⟨⟨hc.1.le.trans hu.1, hu.2, ht.1.le, ht.2.1.le⟩,
        hch.trans hu.1, ht.2.2.ge⟩
    exact hhistory a u (t u) hia hau ht.1 hp ht.2.2
  · intro u hu
    have ht := hroot u ⟨hcg.trans hu.1, hu.2⟩
    have hp : (u, t u) ∈ adaptiveExterior S ui us ell :=
      ⟨⟨hc.1.le.trans hu.1, hu.2, ht.1.le, ht.2.1.le⟩,
        hcs.trans hu.1, ht.2.2.ge⟩
    have hs := hsource u (t u) hp ht.2.2
    have hn := (neg_pos.mpr (h.solution.nu_neg (u, 0) (hdomain u hu))).le
    have hm := hM (S.r u 0) ⟨(hRu u hu).1, (hRu u hu).2.trans hRc.2⟩
    have hnn : 0 ≤ (-S.nu u 0) * (M (S.r u 0) / ell (S.r u 0) ^ 2) *
        (eVariationOn (S.a u) (Icc (t u) 0)).toReal := by positivity
    dsimp only [k, q, L] at hs ⊢
    nlinarith only [hs, hnn]

end EmcsfAcExtension.Global.Exterior
