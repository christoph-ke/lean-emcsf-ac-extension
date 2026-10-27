module

public import EmcsfAcExtension.Global.Exterior.SignedVariation

/-! # The explicit initial contribution to exterior variation decay

The multiplier is fixed before either late row. The initial density is
the ordinary L¹ derivative on one fixed proper row; no uniform modulus
over initial rows is asserted. Source: `charged_SF_new_version.tex:L1381–1391`;
approved internal project record (D1)–(D3).
-/

public section

open Set Filter Topology MeasureTheory

namespace EmcsfAcExtension.Global.Exterior

/-- [node c:exterior#outgoing-variation-decay]
The explicit fixed-row initial contribution, supplementing the decay
export. The positive multiplier and integrable forcing depend on the
fixed development, signed bound and adaptive profile, uniformly in both
subsequent rows. Each initial density has its own vanishing L¹ tail. -/
theorem outgoing_variation_initial_contribution
    {ui e k₀ R₀ : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S)
    (M ell : ℝ → ℝ) (hR : 0 < R₀)
    (hk₀ : 0 < k₀ ∧ k₀ < 1 / 8)
    (hLip : LipschitzOnWith (Real.toNNReal k₀) ell (Ioc 0 R₀))
    (hMc : ContinuousOn M (Ioc 0 R₀)) (hM : ∀ R ∈ Ioc 0 R₀, 0 ≤ M R)
    (hAfinite : (∫⁻ R in Ioc 0 R₀, ENNReal.ofReal (M R / ell R ^ 2)) < ⊤)
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0)) :
    ∃ c ∈ Ioo ui 0, ∃ t J : ℝ → ℝ, ∃ P > 0,
      (∀ u ∈ Ico c 0, u < t u ∧ t u < 0 ∧ S.r u (t u) = ell (S.r u 0)) ∧
      IntervalIntegrable J volume c 0 ∧
      Tendsto (fun s => ∫ x in s..0, J x) (𝓝[<] 0) (𝓝 0) ∧
      (∀ s ∈ Ico c 0,
        IntervalIntegrable (deriv (S.a s)) volume (t s) 0 ∧
        Tendsto (fun u => ∫ v in t u..0, ‖deriv (S.a s) v‖) (𝓝[<] 0) (𝓝 0)) ∧
      (∀ s u, c ≤ s → s ≤ u → u < 0 →
        (eVariationOn (S.a u) (Icc (t u) 0)).toReal ≤
          P * (∫ v in t u..0, ‖deriv (S.a s) v‖) + P * (∫ x in s..u, J x)) := by
  obtain ⟨C, hC, hcollapse, hphi⟩ := terminal_control h hs
  obtain ⟨c, hc, t, k, q, hroot, hm, ht, hsegments, hk, hq, hpos,
      hopt, hhistory, hsource⟩ := terminal_derivative_forcing_setup h M ell hR hC hk₀ hLip
        hMc hM hAfinite hcollapse hmass hell hellsmall hsmall hphi
  let KV := ((eVariationOn (S.a c) (Icc (t c) 0)).toReal + ∫ s in c..0, q s) *
    Real.exp (∫ s in c..0, k s)
  have hvar := outgoing_variation_bound_of_history h hc
    (fun u hu => ⟨(hroot u hu).1, (hroot u hu).2.1⟩) hm.monotoneOn hsegments hk hq
      (fun u hu => (hpos u hu).1) (fun u hu => (hpos u hu).2) hhistory
  have hcoef (u : ℝ) (hu : u ∈ Ico c 0) (v : ℝ) (hv : v ∈ Icc (t u) 0) :
      |S.rUV u v / S.lam u v| ≤ k u := by
    have hr := hroot u hu
    have hd : u ∈ Ico ui 0 := ⟨hc.1.le.trans hu.1, hu.2⟩
    have hrad := (outgoing_radius_strictMono h hd).monotoneOn
      ⟨hr.1.le, hr.2.1.le⟩ ⟨hr.1.le.trans hv.1, hv.2⟩ hv.1
    exact hopt (u, v) ⟨⟨hd.1, hd.2, hr.1.le.trans hv.1, hv.2⟩,
      hu.1, hr.2.2.ge.trans hrad⟩
  let J := fun x => k x * KV + q x
  have hJ : IntervalIntegrable J volume c 0 := (hk.mul_const KV).add hq
  refine ⟨c, hc, t, J, Real.exp (∫ x in c..0, k x), Real.exp_pos _, hroot,
    hJ, time_integral_tail_tendsto hc.2 hJ, ?_, ?_⟩
  · intro s hs'
    have hr := hroot s hs'
    have hseg : outSeg s (t s) 0 ⊆ origDomain ui :=
      (outSeg_subset_origDomain_iff hr.2.1.le).2
        ⟨hc.1.le.trans hs'.1, hs'.2, hr.1.le, le_rfl⟩
    have hac := (h.solution.ac_out s (t s) 0 hr.2.1.le hseg).2.2.2.2
    have hi := hac.intervalIntegrable_deriv_complex
    refine ⟨hi, fixed_row_norm_tail_tendsto hr.2.1.le hi ht ?_⟩
    filter_upwards [Ioo_mem_nhdsLT hs'.2] with u hu
    have hul : u ∈ Ico c 0 := ⟨hs'.1.trans hu.1.le, hu.2⟩
    exact ⟨hm.monotoneOn hs' hul hu.1.le, (hroot u hul).2.1.le⟩
  · intro s u hcs hsu hu
    exact outgoing_variation_duhamel_of_majorants h hc
      (fun x hx => ⟨(hroot x hx).1, (hroot x hx).2.1.le⟩) hm.monotoneOn
      hcs hsu hu hk hq (fun x hx => (hpos x hx).1) hcoef hvar hsource

end EmcsfAcExtension.Global.Exterior
