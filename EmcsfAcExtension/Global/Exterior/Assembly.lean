module

public import EmcsfAcExtension.Global.Exterior.ScalarLimits
public import EmcsfAcExtension.Global.Exterior.EntryClosed
public import EmcsfAcExtension.Global.Exterior.SignedDuhamel
import EmcsfAcExtension.Global.Terminal.Hypotheses
import EmcsfAcExtension.Global.Terminal.OpticalUpper
import EmcsfAcExtension.Global.Exterior.Radii

/-! # The adaptive exterior proposition

The profile is chosen before every late cutoff, row, carrier and endpoint.
All terminal and density inputs are discharged from the original signed
terminal setting. Source: `charged_SF_new_version.tex:L1071–1095`; the entry conclusions
are the inputs consumed at L3854–3886. No local existence theorem is used.
-/

public section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.Exterior

/-- [node c:exterior]
The complete adaptive exterior, with an arbitrarily prescribed positive
slope below `1/8`. The mass profile and positive optical limit depend on
the fixed development and signed bound. The adaptive profile, frontier
and gauge may also depend on the prescribed slope. All later
cutoffs precede their rows, labels, cylinder radii and final endpoints;
proper inverse constants may depend on their proper interval. The common
complex limit retains the scalar background. The exact entry interaction
is integrable on late rows and its norm tends to zero. -/
theorem main {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    ∃ M : ℝ → ℝ,
      (∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0) ∧
      ContinuousOn M (Ioc 0 (S.r ui 0)) ∧ (∀ R ∈ Ioc 0 (S.r ui 0), 0 ≤ M R) ∧
      ∃ lam₀ > 0, Tendsto (fun u => S.lam u 0) (𝓝[<] 0) (𝓝 lam₀) ∧
      ∀ k : ℝ, 0 < k ∧ k < 1 / 8 →
      ∃ ell : ℝ → ℝ, ∃ R₀ > 0, R₀ = S.r ui 0 ∧
      MonotoneOn ell (Ioc 0 R₀) ∧
      LipschitzOnWith (Real.toNNReal k) ell (Ioc 0 R₀) ∧
      (∀ R ∈ Ioc 0 R₀, 0 < ell R ∧ ell R ≤ k * R) ∧
      Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0) ∧
      (∫⁻ R in Ioc 0 R₀, ENNReal.ofReal (M R / ell R ^ 2)) < ⊤ ∧
      ∃ c ∈ Ioo ui 0, ∃ V χ : ℝ → ℝ, ∃ z : ℂ,
        (∀ u ∈ Ico c 0, u < V u ∧ V u < 0 ∧ S.r u (V u) = ell (S.r u 0)) ∧
        StrictMonoOn V (Ico c 0) ∧ Tendsto V (𝓝[<] 0) (𝓝 0) ∧
        ContinuousOn V (Ico c 0) ∧
        (∀ p ∈ adaptiveExterior S ui c ell,
          (∀ s ∈ Icc c p.1, (s, p.2) ∈ adaptiveExterior S ui c ell) ∧
          StrictAntiOn (fun s => S.r s p.2 - ell (S.r s 0)) (Icc c p.1)) ∧
        (∀ a b, c ≤ a → a ≤ b → b < 0 → ∃ L > 0, ∃ m > 0,
          LipschitzOnWith (Real.toNNReal L) V (Icc a b) ∧
          (∀ u ∈ Icc a b, ∀ w ∈ Icc a b, m * dist u w ≤ dist (V u) (V w)) ∧
          (∀ᵐ u ∂volume.restrict (Icc a b),
            S.lam u (V u) * deriv V u =
                -S.nu u (V u) - deriv ell (S.r u 0) * (-S.nu u 0) ∧
              (1 / 2 - k) * (-S.nu u 0) ≤ S.lam u (V u) * deriv V u ∧
              0 < S.lam u (V u) * deriv V u)) ∧
        BoundedVariationOn (curveParallel e S S.a id V c) (Ico c 0) ∧
        Tendsto (fun a => eVariationOn (curveParallel e S S.a id V c) (Ico a 0))
          (𝓝[<] 0) (𝓝 0) ∧
        Tendsto (fun u => (eVariationOn (S.a u) (Icc (V u) 0)).toReal) (𝓝[<] 0) (𝓝 0) ∧
        (∀ ε > 0, ∀ᶠ u in 𝓝[<] (0 : ℝ), ∀ v ∈ Icc (V u) 0,
          ‖S.theta u v / (S.lam u v : ℂ)‖ < ε) ∧
        (∀ ε > 0, ∃ d ∈ Ioo c 0, ∀ p ∈ adaptiveExterior S ui d ell,
          |S.lam p.1 p.2 - lam₀| < ε ∧ |S.nu p.1 p.2 / S.nu p.1 0 - 1| < ε) ∧
        (∀ ε > 0, ∃ d ∈ Ioo c 0, ∀ p ∈ adaptiveExterior S ui d ell,
          S.mu p.1 p.2 ≤ ε) ∧
        (∀ ε > 0, ∃ d ∈ Ioo c 0, ∀ (a b ρ : ℝ) (W : ℝ → ℝ),
          d ≤ a → a ≤ b → b < 0 → ContinuousOn W (Icc a b) →
          (∀ u ∈ Icc a b, u < W u ∧ W u ≤ 0 ∧ S.r u (W u) = ρ) →
          (∀ u ∈ Icc a b, ell (S.r u 0) ≤ ρ) →
          curveCovVar e S S.a id W a b ≤ ENNReal.ofReal ε) ∧
        ContDiffOn ℝ 1 χ (Iio 0) ∧ χ ui = 0 ∧
        (∀ u ∈ Ico c 0, (gaugeFields e S χ).A u (V u) = 0) ∧
        (gaugeFields e S χ).a ui = S.a ui ∧
        AbsolutelyContinuousOnInterval ((gaugeFields e S χ).a ui) ui 0 ∧
        Tendsto (fun u => (gaugeFields e S χ).a u (V u)) (𝓝[<] 0) (𝓝 z) ∧
        (∀ ε > 0, ∀ᶠ u in 𝓝[<] (0 : ℝ), ∀ v ∈ Icc (V u) 0,
          ‖(gaugeFields e S χ).a u v - z‖ < ε ∧
          ‖(gaugeFields e S χ).phi u v - z‖ < ε) ∧
        (∃ d ∈ Ioo c 0, ∀ u ∈ Ico d 0,
          IntervalIntegrable (weightedJ S u) volume (V u) 0) ∧
        Tendsto (fun u => ∫ v in V u..0, ‖weightedJ S u v‖) (𝓝[<] 0) (𝓝 0) := by
  obtain ⟨M, hmass, hM, hMc, hMR, hMI⟩ := terminal_mass_profile h hs
  obtain ⟨lam₀, hlam, hlimit⟩ := Terminal.terminal_lambda_limit h hs
  obtain ⟨Λ, _, _, hupper⟩ := Terminal.lambda_gap_upper h.ui_neg h.solution h.mu
  have hR := (terminal_radius_mem h ⟨le_rfl, h.ui_neg⟩).1
  refine ⟨M, hmass, hMc, hM, lam₀, hlam, hlimit, ?_⟩
  intro k hk
  obtain ⟨ell, hmono, hLip, hell, hellsmall, hsmall, hI⟩ :=
    Terminal.adaptive_majorant M (S.r ui 0) k hR hk hM hMc hMR hMI
  have hepos := fun R hR' => (hell R hR').1
  obtain ⟨lam₁, _, hlimit₁, hopt⟩ := uniform_optical_limits h hs M ell hR hk hLip
    hmass hepos hellsmall hsmall hI
  have hlameq : lam₁ = lam₀ := tendsto_nhds_unique hlimit₁ hlimit
  subst lam₁
  obtain ⟨cv, hcv, V, χ, z, hroot, hm, ht, hV, hbv, _, hχ, hzero, hA,
      hdatum, hAC, hz, huniform⟩ := uniform_common_scalar_limit h hs M ell hk hLip
    hMc hM hI hmass hepos hellsmall hsmall
  obtain ⟨cp, hcp, hpast⟩ := incoming_past_invariance h hs M ell hR hk hLip
    hmass hepos hellsmall hsmall
  obtain ⟨cs, hcs, hvcs, hspeed⟩ := frontier_speed_of_root h hs hcv M ell V hk hLip
    hmass hepos hellsmall hsmall hroot
  obtain ⟨cc, hcc, hcyl⟩ := cylinder_covariant_variation_tail h hs M ell hR hk hLip
    hMc hM hI hmass hepos hellsmall hsmall
  let c := max cs (max cp cc)
  have hc : c ∈ Ioo ui 0 := ⟨lt_max_of_lt_left hcs.1, max_lt hcs.2 (max_lt hcp.2 hcc.2)⟩
  have hsc : cs ≤ c := le_max_left _ _
  have hvc : cv ≤ c := hvcs.trans hsc
  have hpc : cp ≤ c := (le_max_left cp cc).trans (le_max_right cs (max cp cc))
  have hsub : Ico c 0 ⊆ Ico cv 0 := Ico_subset_Ico_left hvc
  have hmem (u : ℝ) (hu : u ∈ Ico cv 0) : (u, V u) ∈ origDomain ui :=
    ⟨hcv.1.le.trans hu.1, hu.2, (hroot u hu).1.le, (hroot u hu).2.1.le⟩
  have hbv' := frontier_bv_later_of_bv h hvc hc.2 hV hmem hbv
  obtain ⟨hvar, hfield⟩ := density_decay_of_root h hs hcv M ell V hk hLip hMc hM hI
    hmass hepos hellsmall hsmall hroot
  obtain ⟨hentryAll, hentrylim⟩ :=
    Entry.small_initial_interaction_norm h hs hcv M ell V hk hLip hMc hM hI
      hmass hepos hellsmall hsmall hroot
  obtain ⟨ub, hub, hentry⟩ := hentryAll Λ (fun u hu v hv =>
    hupper (u, v) ⟨hcv.1.le.trans hu.1, hu.2, (hroot u hu).1.le.trans hv.1, hv.2⟩)
  refine ⟨ell, S.r ui 0, hR, rfl, hmono, hLip, hell,
    hellsmall, hsmall, hI, c, hc, V, χ, z,
    (fun u hu => hroot u (hsub hu)), hm.mono hsub, ht, hV.mono hsub, ?_, ?_, hbv',
    tendsto_eVariationOn_curveParallel_terminal_tail hc.2 hbv', hvar, hfield, ?_, ?_, ?_,
    hχ, hzero, (fun u hu => hA u (hsub hu)), hdatum, hAC, hz, huniform, ?_, hentrylim⟩
  · intro p hp
    obtain ⟨hkeep, hanti⟩ := hpast p ⟨hp.1, hpc.trans hp.2.1, hp.2.2⟩
    refine ⟨?_, hanti.mono (Icc_subset_Icc_left hpc)⟩
    intro s hs'
    have hh := hkeep s ⟨hpc.trans hs'.1, hs'.2⟩
    exact ⟨hh.1, hs'.1, hh.2.2⟩
  · intro a b ha hab hb
    exact hspeed a b (hsc.trans ha) hab hb
  · intro ε hε
    obtain ⟨s, hs', hbound⟩ := hopt ε hε
    obtain ⟨d, hd, hd0⟩ := exists_between (max_lt hc.2 hs'.2)
    refine ⟨d, ⟨(le_max_left c s).trans_lt hd, hd0⟩, ?_⟩
    intro p hp
    exact hbound p ⟨hp.1, (le_max_right c s).trans (hd.le.trans hp.2.1), hp.2.2⟩
  · intro ε hε
    obtain ⟨s, hs', hbound⟩ := exterior_small_gap h hs M ell hR hε hmass hepos hsmall
    obtain ⟨d, hd, hd0⟩ := exists_between (max_lt hc.2 hs'.2)
    refine ⟨d, ⟨(le_max_left c s).trans_lt hd, hd0⟩, ?_⟩
    intro p hp
    have hh := hbound p ⟨hp.1, (le_max_right c s).trans (hd.le.trans hp.2.1), hp.2.2⟩
    exact hh.2.1.trans hh.2.2
  · intro ε hε
    obtain ⟨s, hs', hbound⟩ := hcyl ε hε
    obtain ⟨d, hd, hd0⟩ := exists_between (max_lt hc.2 hs'.2)
    refine ⟨d, ⟨(le_max_left c s).trans_lt hd, hd0⟩, ?_⟩
    intro a b ρ W ha hab hb hW hWroot hinterior
    exact hbound a b ρ W ((le_max_right c s).trans (hd.le.trans ha)) hab hb
      hW hWroot hinterior
  · obtain ⟨d, hd, hd0⟩ := exists_between (max_lt hc.2 hub.2)
    refine ⟨d, ⟨(le_max_left c ub).trans_lt hd, hd0⟩, ?_⟩
    intro u hu
    exact (hentry u ⟨(le_max_right c ub).trans (hd.le.trans hu.1), hu.2⟩).1

end EmcsfAcExtension.Global.Exterior
