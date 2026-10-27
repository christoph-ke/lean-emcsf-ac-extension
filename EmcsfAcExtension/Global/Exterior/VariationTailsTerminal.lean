module

public import EmcsfAcExtension.Global.Exterior.VariationTailsTerminalBounds
public import EmcsfAcExtension.Global.Exterior.VariationTailsDecay

/-! # Terminal outgoing decay and the uniform boundary exit tail

Every analytic and geometric input is discharged from the approved
terminal adaptive outputs. The outgoing derivative on a selected proper
segment uses its prescribed initial-row representative. The common exit
majorant is fixed before choosing a boundary or its final time. Source:
`charged_SF_new_version.tex:L1381–L1416`, approved internal project record (D1)–(D3), (M5).
-/

public section

open Set MeasureTheory Filter Topology
open scoped NNReal

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
The actual outgoing variation and field tend uniformly to zero. One
vanishing majorant controls the exit cost of every proper increasing
bi-Lipschitz boundary in the exterior, including all admissible cylinders.
Its constants depend only on the fixed original data, coupling and profile,
uniformly in the boundary, cylinder radius, initial row, and final time.
No variation or exit estimate is a hypothesis. -/
theorem variation_and_boundary_exit_tails_of_terminal
    {ui e C k₀ R₀ : ℝ} {S : Fields}
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
    ∃ c ∈ Ioo ui 0, ∃ t E : ℝ → ℝ,
      (∀ u ∈ Ico c 0, u < t u ∧ t u < 0 ∧ S.r u (t u) = ell (S.r u 0)) ∧
      StrictMonoOn t (Ico c 0) ∧ Tendsto t (𝓝[<] 0) (𝓝 0) ∧
      Tendsto (fun u => (eVariationOn (S.a u) (Icc (t u) 0)).toReal) (𝓝[<] 0) (𝓝 0) ∧
      (∀ ε > 0, ∀ᶠ u in 𝓝[<] (0 : ℝ), ∀ v ∈ Icc (t u) 0,
        ‖S.theta u v / (S.lam u v : ℂ)‖ < ε) ∧
      (∀ a b, c ≤ a → a ≤ b → b < 0 → ∃ K L : ℝ≥0,
        LipschitzOnWith K t (uIcc a b) ∧
        AntilipschitzWith L ((uIcc a b).domRestrict t)) ∧
      Tendsto E (𝓝[<] 0) (𝓝 0) ∧
      ∀ (a b : ℝ) (γ : ℝ → ℝ) (K L : ℝ≥0),
        c ≤ a → a ≤ b → b < 0 → LipschitzOnWith K γ (uIcc a b) →
        MonotoneOn γ (uIcc a b) → AntilipschitzWith L ((uIcc a b).domRestrict γ) →
        (∀ u ∈ Icc a b, t u ≤ γ u ∧ γ u ≤ 0) →
        (∫ u in a..b, deriv γ u * ‖densityRepresentative e S a u (γ u)‖) ≤ E a := by
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
  have hproper (u : ℝ) (hu : u ∈ Ico c 0) : u < t u ∧ t u ≤ 0 :=
    ⟨(hroot u hu).1, (hroot u hu).2.1.le⟩
  have hvar := outgoing_variation_bound_of_history h hc
    (fun u hu => ⟨(hroot u hu).1, (hroot u hu).2.1⟩) hmono.monotoneOn hsegments hk hq
      (fun u hu => (hpos u hu).1) (fun u hu => (hpos u hu).2) hhistory
  have hcoef (u : ℝ) (hu : u ∈ Ico c 0) (v : ℝ) (hv : v ∈ Icc (t u) 0) :
      |S.rUV u v / S.lam u v| ≤ k u := by
    have hr := hroot u hu
    have hd : u ∈ Ico ui 0 := ⟨hc.1.le.trans hu.1, hu.2⟩
    have hrad := (outgoing_radius_strictMono h hd).monotoneOn
      ⟨hr.1.le, hr.2.1.le⟩ ⟨hr.1.le.trans hv.1, hv.2⟩ hv.1
    exact hopt (u, v) ⟨⟨hd.1, hd.2, hr.1.le.trans hv.1, hv.2⟩,
      hu.1, hr.2.2.ge.trans hrad⟩
  have hVdecay := outgoing_variation_decay_of_majorants h hc hproper hmono.monotoneOn htt
    hk hq (fun u hu => (hpos u hu).1) (fun u hu => (hpos u hu).2) hKV hcoef hvar hsource
  let E := fun a => (eVariationOn (S.a a) (Icc (t a) 0)).toReal +
    ∫ u in a..0, (k u * KV + q u)
  refine ⟨c, hc, t, E, hroot, hmono, htt, hVdecay, ?_, hsegments, ?_, ?_⟩
  · apply outgoing_field_decay_of_terminal h M ell t hR hc hcollapse hmass hell
      hellsmall hsmall (fun u hu => ?_) hVdecay
    have hr := hroot u hu
    exact ⟨⟨hc.1.le.trans hu.1, hu.2, hr.1.le, hr.2.1.le⟩, hr.2.2⟩
  · exact variation_exit_majorant_tendsto_zero hc.2 hk hq hVdecay
  · intro a b γ K L ha hab hb hγ hγm hγa hinside
    exact boundary_exit_bound_of_history h hc hproper ha hab hb hγ hγm hγa hinside
      hk hq (fun u hu => (hpos u hu).1) (fun u hu => (hpos u hu).2) hKV hvar hhistory

end EmcsfAcExtension.Global.Exterior
