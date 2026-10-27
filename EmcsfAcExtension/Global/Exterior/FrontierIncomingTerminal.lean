module

public import EmcsfAcExtension.Global.Exterior.FrontierIncomingTails

/-! # Terminal construction of the common incoming majorant

This consumer combines the pointwise optical estimate with the approved
radial forcing. Its sole variation input is a uniform field bound, to be
discharged by the outgoing-variation consumer. Source:
`charged_SF_new_version.tex:L1356–L1360`, L1405–L1408, internal project record (I2).
-/

public section

open Set MeasureTheory Filter Topology Complex

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
Terminal profiles and a uniform field bound give one incoming-transport
tail cutoff before all continuous exterior carriers and final times.
The constants `264,32` are numerical. The field bound `B` is fixed on an
entire late exterior; it never depends on the carrier or terminal time.
The outgoing-variation consumer supplies this helper's field premise. -/
theorem incoming_transport_tail_of_uniform_field_bound
    {ui e C R₀ uf B : ℝ} {S : Fields} (h : OriginalData ui e S)
    (M ell : ℝ → ℝ) (hR : 0 < R₀) (hC : 0 < C) (huf : uf ∈ Ioo ui 0)
    (hcollapse : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hMc : ContinuousOn M (Ioc 0 R₀)) (hec : ContinuousOn ell (Ioc 0 R₀))
    (hM : ∀ R ∈ Ioc 0 R₀, 0 ≤ M R)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hAfinite : (∫⁻ R in Ioc 0 R₀, ENNReal.ofReal (M R / ell R ^ 2)) < ⊤)
    (hphi : ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0))))
    (hfield : ∀ p ∈ adaptiveExterior S ui uf ell,
      ‖S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ)‖ ≤ B) :
    ∃ c ∈ Ioo ui 0, ∃ H : ℝ → ℝ,
      IntegrableOn H (Ico c 0) ∧
      (∀ p ∈ adaptiveExterior S ui c ell,
        ‖(-S.nu p.1 p.2 / ((1 - S.mu p.1 p.2) * S.r p.1 p.2) : ℝ) *
          ((S.mu p.1 p.2 - S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 : ℝ) *
            (S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ)) +
            I * e * S.Q p.1 p.2 * S.phi p.1 p.2)‖ ≤ H p.1) ∧
      ∀ ε > 0, ∃ u₀ ∈ Ioo c 0,
      ∀ a b : ℝ, u₀ ≤ a → a ≤ b → b < 0 →
        ∀ V : ℝ → ℝ, ContinuousOn V (Icc a b) →
          (∀ u ∈ Icc a b, (u, V u) ∈ adaptiveExterior S ui c ell) →
          (∫ u in a..b,
            ‖(-S.nu u (V u) / ((1 - S.mu u (V u)) * S.r u (V u)) : ℝ) *
              ((S.mu u (V u) - S.Q u (V u) ^ 2 / S.r u (V u) ^ 2 : ℝ) *
                (S.theta u (V u) / (S.lam u (V u) : ℂ)) +
                I * e * S.Q u (V u) * S.phi u (V u))‖) ≤ ε := by
  obtain ⟨up, hup, hpoint⟩ := incoming_transport_bound_of_terminal h M ell hR hC
    hcollapse hmass hell hellsmall hsmall hphi
  have hRi : 0 < S.r ui 0 :=
    h.solution.r_pos (ui, 0) ⟨le_rfl, h.ui_neg, h.ui_neg.le, le_rfl⟩ h.ui_neg
  obtain ⟨Rc, hRc, hAi, hGi, _⟩ := forcing_integrability_of_terminal_profiles
    (e := e) (C := C + 2) hRi (by linarith only [hC]) hR hMc hec hM hell
      hellsmall hsmall hAfinite
  obtain ⟨c, hc, hcR⟩ := (show ∀ᶠ u in 𝓝[<] (0 : ℝ),
      u ∈ Ioo (max up uf) 0 ∧ S.r u 0 < Rc from by
    filter_upwards [Ioo_mem_nhdsLT (max_lt hup.2 huf.2),
      hcollapse.eventually (Iio_mem_nhds hRc.1)] with u hu hr
    exact ⟨hu, hr⟩).exists
  have huc : c ∈ Ioo ui 0 :=
    ⟨hup.1.trans ((le_max_left up uf).trans_lt hc.1), hc.2⟩
  have hpc : up ≤ c := (le_max_left up uf).trans hc.1.le
  have hfc : uf ≤ c := (le_max_right up uf).trans hc.1.le
  let L : ℝ → ℝ := fun R => (C + 2) * (1 + Real.sqrt (Real.log (S.r ui 0 / R)))
  let A : ℝ → ℝ := fun u => (-S.nu u 0) * (M (S.r u 0) / ell (S.r u 0) ^ 2)
  let Q : ℝ → ℝ := fun u => (-S.nu u 0) * exteriorForcing e M ell L (S.r u 0)
  have hAi' : IntegrableOn A (Ico c 0) :=
    integrable_terminal_radius_pullback h ⟨huc.1.le, huc.2⟩ hcR.le hAi
  have hGi' : IntegrableOn Q (Ico c 0) :=
    integrable_terminal_radius_pullback h ⟨huc.1.le, huc.2⟩ hcR.le hGi
  have hRadius (u : ℝ) (hu : u ∈ Ico c 0) : S.r u 0 ∈ Ioc 0 R₀ := by
    have hui : u ∈ Ico ui 0 := ⟨huc.1.le.trans hu.1, hu.2⟩
    refine ⟨h.solution.r_pos (u, 0) ⟨hui.1, hui.2, hui.2.le, le_rfl⟩ hui.2, ?_⟩
    have hs : inSeg c u 0 ⊆ origDomain ui :=
      (inSeg_subset_origDomain_iff hu.1).2 ⟨huc.1.le, hu.2, hu.2.le, le_rfl⟩
    have hf := (h.solution.eq_in c u 0 hu.1 hu.2 hs).1
    have hn : 0 ≤ ∫ x in c..u, -S.nu x 0 :=
      intervalIntegral.integral_nonneg hu.1 (fun x hx =>
        (neg_pos.mpr (h.solution.nu_neg (x, 0) (hs ⟨hx.1, hx.2, rfl⟩))).le)
    rw [intervalIntegral.integral_neg, ← hf.2] at hn
    have hle : S.r u 0 ≤ S.r c 0 := by linarith only [hn]
    exact hle.trans (hcR.le.trans hRc.2)
  have hproper : ∀ p ∈ adaptiveExterior S ui c ell, p.1 < p.2 := by
    rintro ⟨u, v⟩ hp
    have hr : 0 < S.r u v := (hell _ (hRadius u ⟨hp.2.1, hp.1.2.1⟩)).trans_le hp.2.2
    rcases hp.1.2.2.1.eq_or_lt with he | he
    · change u = v at he
      subst v
      rw [(h.solution.axis u hp.1).1] at hr
      exact False.elim (lt_irrefl _ hr)
    · exact he
  have hbound : ∀ p ∈ adaptiveExterior S ui c ell,
      ‖(-S.nu p.1 p.2 / ((1 - S.mu p.1 p.2) * S.r p.1 p.2) : ℝ) *
        ((S.mu p.1 p.2 - S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 : ℝ) *
          (S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ)) +
          I * e * S.Q p.1 p.2 * S.phi p.1 p.2)‖ ≤ 264 * B * A p.1 + 32 * Q p.1 := by
    intro p hp
    have hpt := hpoint p ⟨hp.1, hpc.trans hp.2.1, hp.2.2⟩
    have hf := hfield p ⟨hp.1, hfc.trans hp.2.1, hp.2.2⟩
    have hu : p.1 ∈ Ico c 0 := ⟨hp.2.1, hp.1.2.1⟩
    have hr := hRadius p.1 hu
    have hn : 0 ≤ -S.nu p.1 0 := (neg_pos.mpr
      (h.solution.nu_neg (p.1, 0) ⟨hp.1.1, hu.2, hu.2.le, le_rfl⟩)).le
    have hM' := hM _ hr
    have he' := hell _ hr
    have hL : 0 ≤ L (S.r p.1 0) := by dsimp only [L]; positivity
    have hs := scalar_charge_weight_le_forcing (e := e) hM' he' hL
    have hF := mul_le_mul_of_nonneg_left hf (by positivity :
      0 ≤ 264 * (M (S.r p.1 0) / ell (S.r p.1 0) ^ 2))
    have hQ := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 32)
    have hh := mul_le_mul_of_nonneg_left (add_le_add hF hQ) hn
    have hmi := hmass p.1 ⟨hp.1.1, hp.1.2.1⟩
    rw [terminalMass_def, ← hmi] at hpt
    dsimp only [terminalRadius, L] at hpt
    calc
      _ ≤ _ := hpt
      _ ≤ (-S.nu p.1 0) * (264 * (M (S.r p.1 0) / ell (S.r p.1 0) ^ 2) * B +
          32 * exteriorForcing e M ell L (S.r p.1 0)) := by
        simpa only [L, mul_assoc] using! hh
      _ = 264 * B * A p.1 + 32 * Q p.1 := by dsimp only [A, Q]; ring
  exact ⟨c, huc, (fun u => 264 * B * A u + 32 * Q u),
    (hAi'.const_mul (264 * B)).add (hGi'.const_mul 32), hbound,
    incoming_transport_tail_of_common_majorant h.solution huc.2 hAi' hGi' hbound hproper⟩

end EmcsfAcExtension.Global.Exterior
