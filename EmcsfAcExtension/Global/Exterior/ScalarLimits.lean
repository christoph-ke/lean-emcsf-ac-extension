module

public import EmcsfAcExtension.Global.Exterior.GaugeLimit
public import EmcsfAcExtension.Global.Exterior.AssemblyGeometry

/-! # The exterior scalar limit with all density inputs discharged

The frontier covariant variation and outgoing decay are proved from the
signed terminal setting. The residual gauge retains the original scalar
background. Source: `charged_SF_new_version.tex:L1417–1424`.
-/

public section

open Set Filter Topology MeasureTheory

namespace EmcsfAcExtension.Global.Exterior

/-- [node c:exterior#uniform-common-scalar-limit]
Choose the frontier comparison gauge and the common finite complex limit
from the original signed terminal setting and the fixed constructed
profile. Every density premise is discharged. The frontier, gauge and
complex limit depend on that development and profile, before all late
rows and outgoing labels. No scalar translation is made. -/
theorem uniform_common_scalar_limit {ui e k : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S)
    (M ell : ℝ → ℝ) (hk : 0 < k ∧ k < 1 / 8)
    (hLip : LipschitzOnWith (Real.toNNReal k) ell (Ioc 0 (S.r ui 0)))
    (hMc : ContinuousOn M (Ioc 0 (S.r ui 0)))
    (hM : ∀ R ∈ Ioc 0 (S.r ui 0), 0 ≤ M R)
    (hI : (∫⁻ R in Ioc 0 (S.r ui 0), ENNReal.ofReal (M R / ell R ^ 2)) < ⊤)
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 (S.r ui 0), 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0)) :
    ∃ c ∈ Ioo ui 0, ∃ V χ : ℝ → ℝ, ∃ z : ℂ,
      (∀ u ∈ Ico c 0, u < V u ∧ V u < 0 ∧ S.r u (V u) = ell (S.r u 0)) ∧
      StrictMonoOn V (Ico c 0) ∧ Tendsto V (𝓝[<] 0) (𝓝 0) ∧
      ContinuousOn V (Ico c 0) ∧
      BoundedVariationOn (curveParallel e S S.a id V c) (Ico c 0) ∧
      Tendsto (fun a => eVariationOn (curveParallel e S S.a id V c) (Ico a 0))
        (𝓝[<] 0) (𝓝 0) ∧
      ContDiffOn ℝ 1 χ (Iio 0) ∧ χ ui = 0 ∧
      (∀ u ∈ Ico c 0, (gaugeFields e S χ).A u (V u) = 0) ∧
      (gaugeFields e S χ).a ui = S.a ui ∧
      AbsolutelyContinuousOnInterval ((gaugeFields e S χ).a ui) ui 0 ∧
      Tendsto (fun u => (gaugeFields e S χ).a u (V u)) (𝓝[<] 0) (𝓝 z) ∧
      (∀ ε > 0, ∀ᶠ u in 𝓝[<] (0 : ℝ), ∀ v ∈ Icc (V u) 0,
        ‖(gaugeFields e S χ).a u v - z‖ < ε ∧
        ‖(gaugeFields e S χ).phi u v - z‖ < ε) := by
  have hR := (terminal_radius_mem h ⟨le_rfl, h.ui_neg⟩).1
  obtain ⟨c, hc, V, hroot, hm, ht, hbv, htail⟩ :=
    frontier_covariant_variation h hs M ell hR hk hLip hMc hM hI hmass hell hellsmall hsmall
  have hV := frontier_continuous_of_root h hc ell V hk.1.le hLip hroot hm.monotoneOn
  have hmem (u : ℝ) (hu : u ∈ Ico c 0) : (u, V u) ∈ origDomain ui :=
    ⟨hc.1.le.trans hu.1, hu.2, (hroot u hu).1.le, (hroot u hu).2.1.le⟩
  obtain ⟨hvar, hfield⟩ := density_decay_of_root h hs hc M ell V hk hLip hMc hM hI
    hmass hell hellsmall hsmall hroot
  obtain ⟨χ, hχ, hzero, hder, hA, hdatum⟩ :=
    frontier_gauge_choice h.solution h.ui_neg hc.2 hV hmem
  obtain ⟨z, hz, huniform⟩ := uniform_common_scalar_limit_of_density h.solution hc.2
    hV hmem hder hbv hvar hfield
  exact ⟨c, hc, V, χ, z, hroot, hm, ht, hV, hbv, htail,
    hχ, hzero, hA, funext hdatum, outgoing_ac_gauge h.datumAC, hz, huniform⟩

/-- [node c:exterior#frontier-normalized-scalar-limit]
The unconditional frontier limit, with the same constructed gauge and
common exterior limit. All density estimates are discharged; the complex
limit depends only on the fixed development, signed bound and profile. -/
alias frontier_normalized_scalar_limit := uniform_common_scalar_limit

end EmcsfAcExtension.Global.Exterior
