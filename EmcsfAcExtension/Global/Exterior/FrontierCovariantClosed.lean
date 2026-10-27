module

public import EmcsfAcExtension.Global.Exterior.FrontierIncomingClosed
public import EmcsfAcExtension.Global.Exterior.VariationTransportCovariant

/-! # Finite frontier covariant variation and its intrinsic terminal tail

The proof first bounds every proper truncation in one fixed parallel
gauge. Compact exhaustion gives finite variation on the half-open curve;
finite variation then gives its intrinsic vanishing endpoint tail.
Source: `charged_SF_new_version.tex:L1347–L1362`, L1416, approved internal project record (I3).
-/

public section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal NNReal

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
An actual late adaptive frontier has finite covariant variation and a
vanishing intrinsic terminal variation tail. The initial parallel gauge
is fixed throughout the complete half-open curve. All uniform variation,
incoming and exit-cost estimates are discharged from terminal inputs.
The finite bound may depend on the solution, coupling, profile and fixed
entry row, uniformly in every subsequent proper truncation.
-/
theorem frontier_covariant_variation_of_terminal
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
    ∃ c ∈ Ioo ui 0, ∃ t : ℝ → ℝ,
      (∀ u ∈ Ico c 0, u < t u ∧ t u < 0 ∧ S.r u (t u) = ell (S.r u 0)) ∧
      StrictMonoOn t (Ico c 0) ∧ Tendsto t (𝓝[<] 0) (𝓝 0) ∧
      BoundedVariationOn (curveParallel e S S.a id t c) (Ico c 0) ∧
      Tendsto (fun a => eVariationOn (curveParallel e S S.a id t c) (Ico a 0))
        (𝓝[<] 0) (𝓝 0) := by
  obtain ⟨cs, hcs, t, k, q, hroot, hmono, htt, hsegments, hk, hq, hpos,
      _, hhistory, _⟩ := terminal_derivative_forcing_setup h M ell hR hC hk₀ hLip
        hMc hM hAfinite hcollapse hmass hell hellsmall hsmall hphi
  let KV := ((eVariationOn (S.a cs) (Icc (t cs) 0)).toReal + ∫ s in cs..0, q s) *
    Real.exp (∫ s in cs..0, k s)
  have hqpos : ∀ᵐ u ∂volume.restrict (Icc cs 0), 0 ≤ q u := by
    rw [← restrict_Ico_eq_restrict_Icc]
    exact (ae_restrict_mem measurableSet_Ico).mono fun u hu => (hpos u hu).2
  have hKV : 0 ≤ KV := mul_nonneg
    (add_nonneg ENNReal.toReal_nonneg
      (intervalIntegral.integral_nonneg_of_ae_restrict hcs.2.le hqpos)) (Real.exp_pos _).le
  have hvar := outgoing_variation_bound_of_history h hcs
    (fun u hu => ⟨(hroot u hu).1, (hroot u hu).2.1⟩) hmono.monotoneOn hsegments hk hq
      (fun u hu => (hpos u hu).1) (fun u hu => (hpos u hu).2) hhistory
  obtain ⟨ci, hci, _, _, _, _, ht⟩ := incoming_transport_tails_of_terminal h M ell hR hC
    hk₀ hLip hMc hM hAfinite hcollapse hmass hell hellsmall hsmall hphi
  obtain ⟨uc, huc, hinc⟩ := ht 1 (by norm_num)
  let c := max cs uc
  have hc : c ∈ Ioo ui 0 := ⟨lt_max_of_lt_left hcs.1, max_lt hcs.2 huc.2⟩
  have hsc : cs ≤ c := le_max_left _ _
  have huc' : uc ≤ c := le_max_right _ _
  have hic : ci ≤ c := huc.1.le.trans huc'
  let E := (eVariationOn (S.a c) (Icc (t c) 0)).toReal +
    ∫ u in c..0, (k u * KV + q u)
  have hbv : BoundedVariationOn (curveParallel e S S.a id t c) (Ico c 0) := by
    apply boundedVariationOn_curveParallel_Ico_of_uniform_bound
      (K := ENNReal.ofReal (1 + E)) ENNReal.ofReal_ne_top
    intro b hb
    by_cases hab : c < b
    · obtain ⟨K, L, hVL, ha⟩ := hsegments c b hsc hab.le hb.2
      have hlate (u : ℝ) (hu : u ∈ Icc c b) : u ∈ Ico cs 0 :=
        ⟨hsc.trans hu.1, hu.2.trans_lt hb.2⟩
      have hm : MonotoneOn t (uIcc c b) := by
        rw [uIcc_of_le hab.le]
        exact hmono.monotoneOn.mono (fun u hu => hlate u hu)
      have hmem (u : ℝ) (hu : u ∈ Icc c b) : (u, t u) ∈ origDomain ui :=
        ⟨hcs.1.le.trans (hlate u hu).1, (hlate u hu).2,
          (hroot u (hlate u hu)).1.le, (hroot u (hlate u hu)).2.1.le⟩
      have hproper (u : ℝ) (hu : u ∈ Icc c b) : u < t u :=
        (hroot u (hlate u hu)).1
      have hIn := hinc c b huc' hab.le hb.2 t
        (by simpa only [uIcc_of_le hab.le] using hVL.continuousOn)
        (fun u hu => ⟨hmem u hu, hic.trans hu.1, (hroot u (hlate u hu)).2.2.ge⟩)
      have hExit := boundary_exit_bound_of_history h hcs
        (fun u hu => ⟨(hroot u hu).1, (hroot u hu).2.1.le⟩) hsc hab.le hb.2
        hVL hm ha (fun u hu => ⟨le_rfl, (hroot u (hlate u hu)).2.1.le⟩)
        hk hq (fun u hu => (hpos u hu).1) (fun u hu => (hpos u hu).2) hKV hvar hhistory
      have hCov := boundary_covariant_variation_le h.solution hab hVL hm ha
        (by simpa only [uIcc_of_le hab.le] using hmem)
        (by simpa only [uIcc_of_le hab.le] using hproper)
      rw [boundary_weighted_density_norm_eq_exit hab.le
        (by simpa only [uIcc_of_le hab.le] using hm)] at hCov
      exact hCov.trans (ENNReal.ofReal_le_ofReal (add_le_add hIn hExit))
    · have he : c = b := le_antisymm hb.1 (not_lt.mp hab)
      subst b
      simp only [curveCovVar_def, Icc_self,
        eVariationOn.subsingleton _ Set.subsingleton_singleton]
      exact bot_le
  exact ⟨c, hc, t, (fun u hu => hroot u ⟨hsc.trans hu.1, hu.2⟩),
    hmono.mono (Ico_subset_Ico_left hsc), htt, hbv,
    tendsto_eVariationOn_curveParallel_terminal_tail hc.2 hbv⟩

end EmcsfAcExtension.Global.Exterior
