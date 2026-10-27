module

public import EmcsfAcExtension.Global.Exterior.VariationTailsUniform
public import EmcsfAcExtension.Global.Exterior.DerivativeSourceForcingSetup

/-! # Terminal consumers of outgoing variation boundedness

The approved terminal and adaptive-radius outputs supply every input to
the genuine moving-interval argument. The resulting constants may depend
on the fixed original solution, coupling and adaptive profile, uniformly
in all later rows and all exterior labels. No variation bound or source
integrability conclusion is assumed. Source: `charged_SF_new_version.tex:L1337–L1380`.
-/

public section

open Set MeasureTheory Filter Topology

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
The actual outgoing normalized scalar has uniformly bounded variation
on all later adaptive exterior rows. All input estimates of M3 and all
integrability and continuity inputs of Grönwall are discharged here.
The finite bound depends on the fixed data and profile, before every
later row is chosen. -/
theorem outgoing_variation_bound_of_terminal {ui e C k₀ R₀ : ℝ} {S : Fields}
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
    ∃ c ∈ Ioo ui 0, ∃ t : ℝ → ℝ, ∃ KV ≥ 0,
      (∀ u ∈ Ico c 0, u < t u ∧ t u < 0 ∧ S.r u (t u) = ell (S.r u 0)) ∧
      (∀ u ∈ Ico c 0, (eVariationOn (S.a u) (Icc (t u) 0)).toReal ≤ KV) := by
  obtain ⟨c, hc, t, k, q, hroot, hmono, htt, hsegments, hk, hq, hpos,
      hopt, hhistory, hsource⟩ := terminal_derivative_forcing_setup h M ell hR hC hk₀ hLip
        hMc hM hAfinite hcollapse hmass hell hellsmall hsmall hphi
  let KV := ((eVariationOn (S.a c) (Icc (t c) 0)).toReal + ∫ s in c..0, q s) *
    Real.exp (∫ s in c..0, k s)
  have hq₀ae : ∀ᵐ u ∂volume.restrict (Icc c 0), 0 ≤ q u := by
    rw [← restrict_Ico_eq_restrict_Icc]
    exact (ae_restrict_mem measurableSet_Ico).mono fun u hu => (hpos u hu).2
  have hKV : 0 ≤ KV := mul_nonneg
    (add_nonneg ENNReal.toReal_nonneg
      (intervalIntegral.integral_nonneg_of_ae_restrict hc.2.le hq₀ae)) (Real.exp_pos _).le
  refine ⟨c, hc, t, KV, hKV, hroot, ?_⟩
  exact outgoing_variation_bound_of_history h hc (fun u hu => ⟨(hroot u hu).1, (hroot u hu).2.1⟩)
    hmono.monotoneOn hsegments hk hq (fun u hu => (hpos u hu).1)
      (fun u hu => (hpos u hu).2) hhistory

/-- [internal]
The complete terminal consumer needed by the incoming transport tails:
one constant bounds the continuous outgoing field on the whole late
adaptive exterior. The constant may depend on the fixed data, coupling
and profile, uniformly in both characteristic coordinates. -/
theorem outgoing_field_bound_of_terminal {ui e C k₀ R₀ : ℝ} {S : Fields}
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
    ∃ c ∈ Ioo ui 0, ∃ B ≥ 0, ∀ p ∈ adaptiveExterior S ui c ell,
      ‖S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ)‖ ≤ B := by
  obtain ⟨cv, hcv, t, KV, hKV, hroot, hbound⟩ := outgoing_variation_bound_of_terminal h M ell
    hR hC hk₀ hLip hMc hM hAfinite hcollapse hmass hell hellsmall hsmall hphi
  obtain ⟨cf, hcf, hFV⟩ := charged_exterior_FV_of_terminal h M ell hR hcollapse hmass
    hell hellsmall hsmall
  have hrpos : ∀ᶠ u in 𝓝[<] (0 : ℝ), 0 < S.r u 0 := by
    filter_upwards [Ioo_mem_nhdsLT h.ui_neg] with u hu
    exact h.solution.r_pos (u, 0) ⟨hu.1.le, hu.2, hu.2.le, le_rfl⟩ hu.2
  have hRt : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hcollapse, hrpos⟩
  have hlate : ∀ᶠ u in 𝓝[<] (0 : ℝ), M (S.r u 0) / ell (S.r u 0) ≤ 1 :=
    ((hsmall.comp hRt).eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
      (fun _ hu => hu.le)
  obtain ⟨d, hd, hdb⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hlate
  let ur := max d ui / 2
  have hur : ur ∈ Ioo ui 0 := by
    have hm := max_lt hd h.ui_neg
    dsimp [ur]
    constructor <;> linarith [le_max_right d ui]
  let c := max cv (max cf ur)
  have hc : c ∈ Ioo ui 0 := ⟨lt_max_of_lt_left hcv.1, max_lt hcv.2 (max_lt hcf.2 hur.2)⟩
  refine ⟨c, hc, KV + 4, by positivity, ?_⟩
  intro p hp
  have hu : p.1 ∈ Ico cv 0 := ⟨(le_max_left cv (max cf ur)).trans hp.2.1, hp.1.2.1⟩
  have ht := hroot p.1 hu
  have htv : t p.1 ≤ p.2 := by
    apply le_of_not_gt
    intro hv
    have hs := outgoing_radius_strictMono h ⟨hp.1.1, hp.1.2.1⟩
      ⟨hp.1.2.2.1, hp.1.2.2.2⟩ ⟨ht.1.le, ht.2.1.le⟩ hv
    rw [ht.2.2] at hs
    exact (not_lt_of_ge hp.2.2) hs
  have hpfront : (p.1, t p.1) ∈ adaptiveExterior S ui cf ell :=
    ⟨⟨hp.1.1, hp.1.2.1, ht.1.le, ht.2.1.le⟩,
      (le_max_left cf ur).trans ((le_max_right cv (max cf ur)).trans hp.2.1), ht.2.2.ge⟩
  have hsmallrow : M (S.r p.1 0) / ell (S.r p.1 0) ≤ 1 := by
    apply hdb
    refine ⟨?_, hp.1.2.1⟩
    have hurp := (le_max_right cf ur).trans ((le_max_right cv (max cf ur)).trans hp.2.1)
    have hm := max_lt hd h.ui_neg
    dsimp [ur] at hurp
    linarith [le_max_left d ui]
  have hsqrt : Real.sqrt (M (S.r p.1 0) / ell (S.r p.1 0)) ≤ 1 :=
    (Real.sqrt_le_sqrt hsmallrow).trans_eq (by norm_num)
  have hv := hFV p.1 (t p.1) hpfront ht.2.2 p.2 ⟨htv, hp.1.2.2.2⟩
  rw [terminalMass_def, ← hmass p.1 ⟨hp.1.1, hp.1.2.1⟩] at hv
  linarith only [hv, hsqrt, hbound p.1 hu]

end EmcsfAcExtension.Global.Exterior
