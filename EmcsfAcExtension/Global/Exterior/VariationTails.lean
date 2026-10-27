module

public import EmcsfAcExtension.Global.Exterior.VariationTransport
public import EmcsfAcExtension.Global.Exterior.VariationTailsContinuity
public import EmcsfAcExtension.Global.Exterior.VariationTailsLimits
public import EmcsfAcExtension.Global.Exterior.DerivativeSourceTerminal

/-! # Outgoing variation and outgoing-field tail consumers

The outgoing variation is the actual variation of the original normalized
scalar. Continuity uses the single prescribed initial density on each
proper swept exterior. The field comparison then transfers variation
decay to uniform field decay. Source: `charged_SF_new_version.tex:L1337–L1391` and
approved internal project record, support-moving-interval and outgoing-variation-decay.
-/

public section

open Set MeasureTheory Filter Topology

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
Actual outgoing variation is continuous on every proper swept exterior.
The representative's initial derivative is only L¹; continuity follows
by dominated convergence, with no derivative regularity premise. -/
theorem continuousOn_outgoing_variation
    {ui e a b : ℝ} {S : Fields} {t : ℝ → ℝ}
    (hS : IsSolution e S (origDomain ui)) (hab : a ≤ b)
    (ht : ContinuousOn t (Icc a b)) (hm : MonotoneOn t (Icc a b))
    (hmem : ∀ u ∈ Icc a b, (u, t u) ∈ origDomain ui)
    (hproper : ∀ u ∈ Icc a b, u < t u) :
    ContinuousOn (fun u => (eVariationOn (S.a u) (Icc (t u) 0)).toReal)
      (Icc a b) := by
  obtain ⟨P, R, hP, hR, heq⟩ := exists_swept_density_factors hS hab ht hm hmem hproper
  have hta : t a ≤ 0 := (hmem a ⟨le_rfl, hab⟩).2.2.2
  have hc := continuousOn_moving_fixedDensity_norm hta ht
    (fun u hu => ⟨hm ⟨le_rfl, hab⟩ hu hu.1, (hmem u hu).2.2.2⟩)
    hP.continuousOn hR.continuousOn (swept_initial_density_intervalIntegrable hS hab hmem)
  apply hc.congr
  intro u hu
  dsimp only
  rw [swept_row_variation_eq_density_integral hS hab hmem hproper hu]
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le (hmem u hu).2.2.2] at hv
  exact congrArg norm (heq (u, v) ⟨hu, hv⟩)

/-- [internal]
The terminal consumer of FV and actual outgoing-variation decay. The
conclusion is uniform in every label of the outgoing adaptive interval.
The coefficient `4` in FV is numerical. The late cutoff may depend on
the solution and adaptive profile; no constant depends on a later row
or on its label. -/
theorem outgoing_field_decay_of_terminal
    {ui e uc R₀ : ℝ} {S : Fields} (h : OriginalData ui e S)
    (M ell t : ℝ → ℝ) (hR : 0 < R₀) (huc : uc ∈ Ioo ui 0)
    (hcollapse : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hrow : ∀ u ∈ Ico uc 0, (u, t u) ∈ origDomain ui ∧
      S.r u (t u) = ell (S.r u 0))
    (hvar : Tendsto (fun u => (eVariationOn (S.a u) (Icc (t u) 0)).toReal)
      (𝓝[<] 0) (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ u in 𝓝[<] (0 : ℝ), ∀ v ∈ Icc (t u) 0,
      ‖S.theta u v / (S.lam u v : ℂ)‖ < ε := by
  obtain ⟨u₀, hu₀, hFV⟩ := charged_exterior_FV_of_terminal h M ell hR hcollapse hmass
    hell hellsmall hsmall
  have hrpos : ∀ᶠ u in 𝓝[<] (0 : ℝ), 0 < S.r u 0 := by
    filter_upwards [Ioo_mem_nhdsLT h.ui_neg] with u hu
    exact h.solution.r_pos (u, 0) ⟨hu.1.le, hu.2, hu.2.le, le_rfl⟩ hu.2
  have hRt : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hcollapse, hrpos⟩
  have hsqrt : Tendsto (fun u => Real.sqrt (M (S.r u 0) / ell (S.r u 0)))
      (𝓝[<] 0) (𝓝 0) := by
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp (hsmall.comp hRt)
    have hh' : Tendsto (fun u => Real.sqrt (M (S.r u 0) / ell (S.r u 0)))
        (𝓝[<] 0) (𝓝 (Real.sqrt 0)) := by
      apply hh.congr'
      exact Eventually.of_forall fun u => by simp only [Function.comp_apply]
    simpa only [Real.sqrt_zero] using hh'
  have hbound : Tendsto (fun u => (eVariationOn (S.a u) (Icc (t u) 0)).toReal +
      4 * Real.sqrt (M (S.r u 0) / ell (S.r u 0))) (𝓝[<] 0) (𝓝 0) := by
    simpa only [mul_zero, add_zero] using hvar.add (hsqrt.const_mul 4)
  intro ε hε
  filter_upwards [Ioo_mem_nhdsLT (max_lt hu₀.2 huc.2),
    hbound.eventually (Iio_mem_nhds hε)] with u hu hb v hv
  have huc' : u ∈ Ico uc 0 := ⟨(le_max_right u₀ uc).trans hu.1.le, hu.2⟩
  have hr := hrow u huc'
  have hp : (u, t u) ∈ adaptiveExterior S ui u₀ ell :=
    ⟨hr.1, (le_max_left u₀ uc).trans hu.1.le, hr.2.ge⟩
  have hle := hFV u (t u) hp hr.2 v hv
  rw [terminalMass_def, ← hmass u ⟨huc.1.le.trans huc'.1, hu.2⟩] at hle
  exact hle.trans_lt hb

end EmcsfAcExtension.Global.Exterior
