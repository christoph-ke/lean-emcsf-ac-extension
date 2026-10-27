module

public import EmcsfAcExtension.Infra.Mixed.FiberCauchy
public import EmcsfAcExtension.Infra.Mixed.Envelope

/-!
# Common measurable representatives on parametrized sections

Auxiliary analysis A5 of internal project record. Moving closed intervals
are parametrized affinely by `[0,1]`. The only exceptional labels are the
Banach-valued subsequence's null set and the null set of degenerate fibers.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace EmcsfAcExtension.Mixed

/-- A5 on moving intervals: L¹-Cauchy continuous fibers have a jointly measurable
representative, uniform convergence on every nonexceptional fiber along one
subsequence, and whole-sequence mixed L¹ convergence. The dominating envelope is
measurable and its integral is the exact limit of the original envelope integrals.
All suprema and estimates have coefficient one, independent of the endpoints. -/
theorem exists_parametric_mixed_limit {μ : Measure ℝ} {S : Set ℝ}
    {a b : ℝ → ℝ} {j : ℕ → ℝ → ℝ → ℂ}
    {F : ℕ → ℝ → C(Icc (0 : ℝ) 1, ℂ)}
    (hS : MeasurableSet S) (ha : Measurable a) (hb : Measurable b)
    (hab : ∀ v ∈ S, a v ≤ b v)
    (hlt : ∀ᵐ v ∂μ.restrict S, a v < b v)
    (hrep : ∀ n v, v ∈ S → ∀ q : Icc (0 : ℝ) 1,
      F n v q = j n (a v + q.1 * (b v - a v)) v)
    (hF : ∀ n, Integrable (F n) (μ.restrict S))
    (hC : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      (∫ v in S, ‖F n v - F m v‖ ∂μ) < ε) :
    ∃ ns : ℕ → ℕ, ∃ N : Set ℝ, ∃ f : ℝ → ℝ → ℂ, ∃ J : ℝ → ℝ≥0∞,
      StrictMono ns ∧ MeasurableSet N ∧ μ N = 0 ∧ N ⊆ S ∧
      Measurable (Function.uncurry f) ∧ Measurable J ∧
      (∀ v ∈ N, ∀ u, f u v = 0) ∧
      (∀ v ∈ S, v ∉ N → TendstoUniformlyOn (fun l u => j (ns l) u v)
        (fun u => f u v) atTop (Icc (a v) (b v))) ∧
      (∀ u v, ‖f u v‖ₑ ≤ J v) ∧ (∫⁻ v in S, J v ∂μ) < ⊤ ∧
      Tendsto (fun n => ∫⁻ v in S, ⨆ u ∈ Icc (a v) (b v), ‖j n u v - f u v‖ₑ ∂μ)
        atTop (𝓝 0) ∧
      Tendsto (fun n => ∫⁻ v in S, ⨆ u ∈ Icc (a v) (b v), ‖j n u v‖ₑ ∂μ)
        atTop (𝓝 (∫⁻ v in S, J v ∂μ)) := by
  classical
  obtain ⟨g, hgm, hgi, hlim, hnorm, ns, N₀, hns, hN₀m, hN₀, hgzero, hseq⟩ :=
    exists_L1_limit_of_integral_cauchy hF hC
  let B := {v | ¬a v < b v}
  have hBm : MeasurableSet B := (measurableSet_lt ha hb).compl
  let N := (N₀ ∪ B) ∩ S
  have hNm : MeasurableSet N := (hN₀m.union hBm).inter hS
  have hN : μ N = 0 := by
    have hB : (μ.restrict S) B = 0 := ae_iff.mp hlt
    have hnull := measure_union_null hN₀ hB
    rw [Measure.restrict_apply (hN₀m.union hBm)] at hnull
    exact hnull
  have hgood v (hv : v ∈ S) (hNv : v ∉ N) : a v < b v := by
    by_contra h
    exact hNv ⟨Or.inr h, hv⟩
  have hseq' v (hv : v ∈ S) (hNv : v ∉ N) :
      Tendsto (fun l => F (ns l) v) atTop (𝓝 (g v)) :=
    hseq v (fun hn => hNv ⟨Or.inl hn, hv⟩)
  let q (u v : ℝ) : Icc (0 : ℝ) 1 :=
    projIcc 0 1 zero_le_one ((u - a v) / (b v - a v))
  let D := {p : ℝ × ℝ | p.2 ∈ S ∧ p.2 ∉ N ∧ p.1 ∈ Icc (a p.2) (b p.2)}
  have hDm : MeasurableSet D :=
    (hS.preimage measurable_snd).inter ((hNm.compl.preimage measurable_snd).inter
      ((measurableSet_le (ha.comp measurable_snd) measurable_fst).inter
        (measurableSet_le measurable_fst (hb.comp measurable_snd))))
  let e (p : ℝ × ℝ) : ℂ := g p.2 (q p.1 p.2)
  have hem : Measurable e := by
    have hq : Measurable (fun p : ℝ × ℝ => q p.1 p.2) := by
      simpa only [q, Function.comp_def] using!
        continuous_projIcc.measurable.comp
          ((measurable_fst.sub (ha.comp measurable_snd)).div
            ((hb.comp measurable_snd).sub (ha.comp measurable_snd)))
    simpa only [e, Function.comp_def] using!
      continuous_eval.measurable.comp ((hgm.measurable.comp measurable_snd).prodMk hq)
  let f (u v : ℝ) : ℂ := D.indicator e (u, v)
  let J (v : ℝ) : ℝ≥0∞ := ‖g v‖ₑ
  have hfm : Measurable (Function.uncurry f) := hem.indicator hDm
  have hJm : Measurable J := hgm.measurable.enorm
  have hfval u v (hv : v ∈ S) (hNv : v ∉ N) (hu : u ∈ Icc (a v) (b v)) :
      f u v = g v (q u v) :=
    indicator_of_mem (show (u, v) ∈ D from ⟨hv, hNv, hu⟩) e
  have harg v (hv : v ∈ S) (r : Icc (0 : ℝ) 1) :
      a v + r.1 * (b v - a v) ∈ Icc (a v) (b v) :=
    ⟨by nlinarith [r.property.1, hab v hv], by nlinarith [r.property.2, hab v hv]⟩
  have hqparam v (hv : v ∈ S) (hNv : v ∉ N) (r : Icc (0 : ℝ) 1) :
      q (a v + r.1 * (b v - a v)) v = r := by
    have hgap : b v - a v ≠ 0 := (sub_pos.mpr (hgood v hv hNv)).ne'
    have heq : (a v + r.1 * (b v - a v) - a v) / (b v - a v) = r.1 := by
      field_simp
      ring
    dsimp only [q]
    rw [heq, projIcc_of_mem zero_le_one r.property]
  have hfparam v (hv : v ∈ S) (hNv : v ∉ N) (r : Icc (0 : ℝ) 1) :
      f (a v + r.1 * (b v - a v)) v = g v r := by
    rw [hfval _ v hv hNv (harg v hv r), hqparam v hv hNv r]
  have herror n v (hv : v ∈ S) (hNv : v ∉ N) :
      (⨆ u ∈ Icc (a v) (b v), ‖j n u v - f u v‖ₑ) = ‖F n v - g v‖ₑ := by
    rw [← iSup_enorm_affine_eq (fun u => j n u v - f u v) (hab v hv),
      ContinuousMap.enorm_eq_iSup_enorm]
    apply iSup_congr
    intro r
    rw [hfparam v hv hNv r, ← hrep n v hv r]
    rfl
  have henv n v (hv : v ∈ S) :
      (⨆ u ∈ Icc (a v) (b v), ‖j n u v‖ₑ) = ‖F n v‖ₑ := by
    rw [← iSup_enorm_affine_eq (fun u => j n u v) (hab v hv),
      ContinuousMap.enorm_eq_iSup_enorm]
    apply iSup_congr
    intro r
    rw [hrep n v hv r]
  have hlimE : Tendsto (fun n => ∫⁻ v in S, ‖F n v - g v‖ₑ ∂μ) atTop (𝓝 0) := by
    have heq n : (∫⁻ v in S, ‖F n v - g v‖ₑ ∂μ) =
        ENNReal.ofReal (∫ v in S, ‖F n v - g v‖ ∂μ) := by
      simpa only [Pi.sub_apply] using!
        (ofReal_integral_norm_eq_lintegral_enorm ((hF n).sub hgi)).symm
    simpa only [heq, Function.comp_apply, ENNReal.ofReal_zero] using!
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim
  have hnormE : Tendsto (fun n => ∫⁻ v in S, ‖F n v‖ₑ ∂μ) atTop
      (𝓝 (∫⁻ v in S, J v ∂μ)) := by
    change Tendsto _ _ (𝓝 (∫⁻ v in S, ‖g v‖ₑ ∂μ))
    rw [← ofReal_integral_norm_eq_lintegral_enorm hgi]
    convert ENNReal.continuous_ofReal.continuousAt.tendsto.comp hnorm using 1
    ext n
    exact (ofReal_integral_norm_eq_lintegral_enorm (hF n)).symm
  refine ⟨ns, N, f, J, hns, hNm, hN, inter_subset_right, hfm, hJm, ?_, ?_, ?_,
    hgi.hasFiniteIntegral, ?_, ?_⟩
  · intro v hv u
    exact indicator_of_notMem (fun hp => hp.2.1 hv) e
  · intro v hv hNv
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hnorm0 := tendsto_iff_norm_sub_tendsto_zero.1 (hseq' v hv hNv)
    filter_upwards [(tendsto_order.1 hnorm0).2 ε hε] with l hl u hu
    rw [dist_comm, dist_eq_norm, hfval u v hv hNv hu]
    have hgap : 0 < b v - a v := sub_pos.mpr (hgood v hv hNv)
    have hmem : (u - a v) / (b v - a v) ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (sub_nonneg.mpr hu.1) hgap.le,
        (div_le_one hgap).mpr (sub_le_sub_right hu.2 (a v))⟩
    have hqa : a v + (q u v).1 * (b v - a v) = u := by
      dsimp only [q]
      rw [projIcc_of_mem zero_le_one hmem, div_mul_cancel₀ _ hgap.ne']
      ring
    have hraw := hrep (ns l) v hv (q u v)
    rw [hqa] at hraw
    rw [← hraw]
    exact (ContinuousMap.norm_coe_le_norm (F (ns l) v - g v) (q u v)).trans_lt hl
  · intro u v
    by_cases hp : (u, v) ∈ D
    · rw [show f u v = e (u, v) from indicator_of_mem hp e]
      simpa only [e, J, ofReal_norm] using!
        ENNReal.ofReal_le_ofReal (ContinuousMap.norm_coe_le_norm (g v) (q u v))
    · rw [show f u v = 0 from indicator_of_notMem hp e]
      simp only [enorm_zero]
      exact zero_le
  · convert hlimE using 1
    ext n
    apply lintegral_congr_ae
    have hnot : ∀ᵐ v ∂μ, v ∉ N := by simpa [ae_iff] using hN
    filter_upwards [ae_restrict_mem hS, ae_restrict_of_ae hnot] with v hv hNv
    exact herror n v hv hNv
  · convert hnormE using 1
    ext n
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hS] with v hv
    exact henv n v hv

end EmcsfAcExtension.Mixed
