module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Apriori.BootstrapScalarAux
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseFinal
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseAxis
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Infra.Calculus.TriangleDiff
import EmcsfAcExtension.Infra.AC.Variation

/-! # Strict improvement of the scalar bootstrap

The scalar background is tracked along the axis from the original vertex.
The fixed source constants four and ten therefore need no enlargement
(`charged_SF_new_version.tex:L4755–L4813`, approved internal project record (23)).
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [node restart-sec-independent-area#scalar-bootstrap-improvement]
Both scalar ratios and the scalar oscillation from the axis are at most
`3 ε`; the scalar itself is at most `‖h 0‖ + (33/8) ε < M`.
The positive thresholds precede every datum and depend only on the fixed
box, uniformly in higher derivatives. The strict scalar margin also holds
when `ε = 0`; strict ratio improvement is used with a positive margin. -/
theorem scalar_bootstrap_improvement : ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e T ε M S h → ε ≤ ε₀ → |e| * (T / 2) * M ≤ δ₀ →
    ∀ u v, (u, v) ∈ triangle 0 T →
      ‖S.theta u v / S.lam u v‖ ≤ 3 * ε ∧
      ‖S.xi u v / S.nu u v‖ ≤ 3 * ε ∧
      ‖S.phi u v - S.phi u u‖ ≤ 3 * ε ∧
      ‖S.phi u v‖ ≤ ‖h 0‖ + 33 / 8 * ε ∧ ‖S.phi u v‖ < M := by
  obtain ⟨ε₀, δ₀, hε₀, hδ₀, hclosed⟩ := bv_envelope_final_individual
  refine ⟨ε₀, δ₀, hε₀, hδ₀, ?_⟩
  intro e T ε M S h hset hε hδ u v hp
  obtain ⟨hJ, _, hVa, hVb⟩ := hclosed e T ε M S h hset hε hδ
  have hε0 := hset.eps_nonneg
  have huT : u ∈ Icc 0 T := ⟨hp.1, hp.2.1.trans hp.2.2⟩
  have hvar : (eVariationOn (S.a u) (Icc u v)).toReal ≤ 3 / 2 * ε :=
    ENNReal.toReal_le_of_le_ofReal (by positivity)
      (((eVariationOn.mono (S.a u) (Icc_subset_Icc le_rfl hp.2.2)).trans
        (le_iSup₂_of_le u huT le_rfl)).trans hVa)
  have hs : MapsTo (fun x : ℝ => (x, v)) (Icc 0 v) (triangle 0 T) :=
    fun x hx => ⟨hx.1, hx.2, hp.2.2⟩
  let q : ℝ → ℂ := fun x =>
    pdU (triangle 0 T) S.b x v + I * e * S.A x v * S.b x v
  have cq : ContinuousOn q (Icc 0 v) := by
    apply ((continuousOn_pdU hset.c1.c1_b (uniqueDiffOn_triangle hset.pos)).add
      (((continuousOn_const (c := I * e)).mul
        (Complex.continuous_ofReal.comp_continuousOn hset.c1.c1_A.continuousOn)).mul
          hset.c1.c1_b.continuousOn)).comp
            (continuous_id.prodMk continuous_const).continuousOn hs
  have hv0 := hp.1.trans hp.2.1
  have heq : ENNReal.ofReal (∫ x in 0..v, ‖q x‖) = ∫⁻ x in Icc 0 v, ‖q x‖ₑ := by
    rw [intervalIntegral.integral_of_le hv0, ← integral_Icc_eq_integral_Ioc]
    exact ofReal_integral_norm_eq_lintegral_enorm
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hv0).mp
        (cq.intervalIntegrable_of_Icc (μ := volume) hv0))
  have hwhole : (∫ x in 0..v, ‖q x‖) ≤ 3 / 2 * ε := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 3 / 2 * ε)).mp
    rw [heq]
    exact (le_iSup₂_of_le v ⟨hv0, hp.2.2⟩ le_rfl).trans hVb
  have hpart : (∫ x in u..v, ‖q x‖) ≤ 3 / 2 * ε :=
    (intervalIntegral.integral_mono_interval hp.1 hp.2.1 le_rfl
      (ae_of_all _ (fun x => norm_nonneg (q x)))
      ((cq.intervalIntegrable_of_Icc hv0).norm)).trans hwhole
  have hratioO := (scalar_ratio_out_le_variation hset.c1 hp.1 hp.2.1 hp.2.2).trans hvar
  have hratioI := (scalar_ratio_in_le_integral hset.c1 hp.1 hp.2.1 hp.2.2).trans hpart
  have hosc := (scalar_axis_oscillation_le_variation hset.pos hset.c1
    hp.1 hp.2.1 hp.2.2).trans hvar
  have haxis := (smooth_axis_variation_budget hset.pos hset.c1 hset.data.2).trans hJ
  have ca : ContDiffOn ℝ 1 (fun t => S.phi t t) (Icc 0 T) :=
    hset.c1.c1_phi.comp (contDiffOn_id.prodMk contDiffOn_id)
      (fun t ht => ⟨ht.1, le_rfl, ht.2⟩)
  have hac : AbsolutelyContinuousOnInterval (fun t => S.phi t t) 0 T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hset.pos.le] using ca
  have hd := (hac.boundedVariationOn_Icc hset.pos.le).dist_le huT ⟨le_rfl, hset.pos.le⟩
  rw [dist_eq_norm] at hd
  have haxisR := ENNReal.toReal_le_of_le_ofReal
    (by positivity : 0 ≤ 9 / 8 * ε) haxis
  have hvertex : S.phi 0 0 = h 0 :=
    (hset.c1.axis 0 ⟨le_rfl, le_rfl, hset.pos.le⟩).2.2.2.2.1.symm.trans
      (hset.data.1 0 ⟨le_rfl, hset.pos.le⟩).2
  have ha : ‖S.phi u u - h 0‖ ≤ 9 / 8 * ε := by
    rw [hvertex] at hd
    exact hd.trans haxisR
  have hnorm := norm_le_norm_add_norm_sub (S.phi u u) (S.phi u v)
  have hnorma := norm_le_norm_add_norm_sub (h 0) (S.phi u u)
  rw [norm_sub_rev] at hnorm hnorma
  have hphi : ‖S.phi u v‖ ≤ ‖h 0‖ + 33 / 8 * ε := by
    linarith only [hnorm, hnorma, hosc, ha, hε0]
  refine ⟨hratioO.trans (by linarith only [hε0]),
    hratioI.trans (by linarith only [hε0]), hosc.trans (by linarith only [hε0]), hphi, ?_⟩
  rw [hset.M_eq]
  linarith only [hphi, hε0]

end EmcsfAcExtension.Local
