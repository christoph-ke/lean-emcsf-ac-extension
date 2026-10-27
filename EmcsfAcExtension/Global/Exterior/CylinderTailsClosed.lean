module

public import EmcsfAcExtension.Global.Exterior.CylinderTailsChain
public import EmcsfAcExtension.Global.Exterior.FrontierIncomingClosed
public import EmcsfAcExtension.Global.Exterior.VariationTailsCylinder

/-! # Uniform terminal covariant variation on exterior cylinders

The incoming and outgoing costs have independently proved uniform tails.
Their cutoffs are selected before cylinder radius and admissible final
time. The proper covariant chain rule then adds the two costs.
Source: `charged_SF_new_version.tex:L1405–L1409`, approved internal project record (I3).
-/

public section

open Set MeasureTheory Filter Topology Complex

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
Covariant normalized-scalar variation tends uniformly to zero on every
proper constant-radius cylinder portion that remains in the adaptive
exterior. The late cutoff precedes the radius, initial row, final time
and graph. All source, variation, speed and chain-rule hypotheses are
discharged from the original solution and approved terminal inputs.
The cost-addition coefficient is the universal constant `1`.
-/
theorem cylinder_covariant_variation_tail_of_terminal
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
    ∃ c ∈ Ioo ui 0, ∀ ε > 0, ∃ u₀ ∈ Ioo c 0,
      ∀ (a b ρ : ℝ) (V : ℝ → ℝ),
        u₀ ≤ a → a ≤ b → b < 0 → ContinuousOn V (Icc a b) →
        (∀ u ∈ Icc a b, u < V u ∧ V u ≤ 0 ∧ S.r u (V u) = ρ) →
        (∀ u ∈ Icc a b, ell (S.r u 0) ≤ ρ) →
        curveCovVar e S S.a id V a b ≤ ENNReal.ofReal ε := by
  obtain ⟨ci, hci, _, _, _, _, ht⟩ := incoming_transport_tails_of_terminal h M ell hR hC
    hk₀ hLip hMc hM hAfinite hcollapse hmass hell hellsmall hsmall hphi
  obtain ⟨ce, hce, E, hE, hexit⟩ := cylinder_exit_tail_of_terminal h M ell hR hC
    hk₀ hLip hMc hM hAfinite hcollapse hmass hell hellsmall hsmall hphi
  let c := max ci ce
  have hc : c ∈ Ioo ui 0 := ⟨lt_max_of_lt_left hci.1, max_lt hci.2 hce.2⟩
  refine ⟨c, hc, ?_⟩
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨uc, huc, hinc⟩ := ht (ε / 2) hhalf
  obtain ⟨d, hd, hdb⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp
    (hE.eventually (Iio_mem_nhds hhalf))
  obtain ⟨u₀, hu₀m, hu₀0⟩ := exists_between (max_lt hc.2 (max_lt huc.2 hd))
  have hcu₀ : c < u₀ := (le_max_left c (max uc d)).trans_lt hu₀m
  have hicu₀ : uc ≤ u₀ := (le_max_left uc d).trans
    ((le_max_right c (max uc d)).trans hu₀m.le)
  have hdu₀ : d < u₀ := (le_max_right uc d).trans_lt
    ((le_max_right c (max uc d)).trans_lt hu₀m)
  refine ⟨u₀, ⟨hcu₀, hu₀0⟩, ?_⟩
  intro a b ρ V ha hab hb hV hroot hinterior
  have hia : ui ≤ a := hc.1.le.trans (hcu₀.le.trans ha)
  by_cases hab' : a < b
  · have hIn := hinc a b (hicu₀.trans ha) hab hb V hV (by
      intro u hu
      have hr := hroot u hu
      refine ⟨⟨hia.trans hu.1, hu.2.trans_lt hb, hr.1.le, hr.2.1⟩,
        (le_max_left ci ce).trans (hcu₀.le.trans (ha.trans hu.1)), ?_⟩
      rw [hr.2.2]
      exact hinterior u hu)
    have hExit := hexit a b ρ V
      ((le_max_right ci ce).trans (hcu₀.le.trans ha)) hab hb hV hroot hinterior
    have hEa : E a < ε / 2 := hdb ⟨hdu₀.trans_le ha, hab.trans_lt hb⟩
    have hCov := cylinder_covariant_variation_le_of_graph h hia hab' hb hV hroot
    rw [boundary_weighted_density_norm_eq_exit hab
      (cylinder_label_strictMono_of_graph h hia hb hroot).monotoneOn] at hCov
    apply hCov.trans
    apply ENNReal.ofReal_le_ofReal
    linarith only [hIn, hExit, hEa]
  · have he : a = b := le_antisymm hab (not_lt.mp hab')
    subst b
    simp only [curveCovVar_def, Icc_self,
      eVariationOn.subsingleton _ Set.subsingleton_singleton]
    exact bot_le

end EmcsfAcExtension.Global.Exterior
