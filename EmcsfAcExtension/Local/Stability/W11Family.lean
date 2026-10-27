module

public import EmcsfAcExtension.Infra.Mixed.FiberCauchy

/-! # Uniform L¹ completeness over section families

A common Cauchy index gives a common convergence index after taking
individual Banach-space limits. No null set of section labels is used.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace EmcsfAcExtension.Local

/-- Uniformly L¹-Cauchy families of real densities have integrable limits
with uniform L¹ error. All error coefficients are one, independent of
section labels, measures, intervals and density bounds. -/
theorem stab_family_L1_limit_of_uniform_cauchy {ι : Type*} {μ : ι → Measure ℝ}
    {F : ℕ → ι → ℝ → ℝ}
    (hF : ∀ n i, Integrable (F n i) (μ i))
    (hC : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, ∀ i,
      (∫⁻ x, ‖F n i x - F m i x‖ₑ ∂μ i) < ENNReal.ofReal δ) :
    ∃ q : ι → ℝ → ℝ, (∀ i, Integrable (q i) (μ i)) ∧
      ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ i,
        (∫ x, |F n i x - q i x| ∂μ i) < δ := by
  have hc : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, ∀ i,
      (∫ x, ‖F n i x - F m i x‖ ∂μ i) < δ := by
    intro δ hδ
    obtain ⟨N, hN⟩ := hC δ hδ
    refine ⟨N, fun n hn m hm i => ?_⟩
    have heq : ENNReal.ofReal (∫ x, ‖F n i x - F m i x‖ ∂μ i) =
        ∫⁻ x, ‖F n i x - F m i x‖ₑ ∂μ i := by
      simpa only [Pi.sub_apply] using!
        ofReal_integral_norm_eq_lintegral_enorm ((hF n i).sub (hF m i))
    exact (ENNReal.ofReal_lt_ofReal_iff hδ).mp (heq.trans_lt (hN n hn m hm i))
  have hex i := Mixed.exists_L1_limit_of_integral_cauchy (fun n => hF n i) (by
    intro δ hδ
    obtain ⟨N, hN⟩ := hc δ hδ
    exact ⟨N, fun n hn m hm => hN n hn m hm i⟩)
  choose q hqm hqi hlim hnorm hseq using hex
  refine ⟨q, hqi, ?_⟩
  intro δ hδ
  obtain ⟨N, hN⟩ := hc (δ / 2) (half_pos hδ)
  refine ⟨N, fun n hn i => ?_⟩
  obtain ⟨m, hmN, hm⟩ := ((eventually_ge_atTop N).and
    ((tendsto_order.1 (hlim i)).2 (δ / 2) (half_pos hδ))).exists
  have hi₁ := ((hF n i).sub (hF m i)).norm
  have hi₂ := ((hF m i).sub (hqi i)).norm
  have hi₃ := ((hF n i).sub (hqi i)).norm
  have htri : (∫ x, ‖F n i x - q i x‖ ∂μ i) ≤
      (∫ x, ‖F n i x - F m i x‖ ∂μ i) + ∫ x, ‖F m i x - q i x‖ ∂μ i := by
    have hiadd := integral_add hi₁ hi₂
    simp only [Pi.sub_apply] at hiadd
    rw [← hiadd]
    apply integral_mono hi₃ (hi₁.add hi₂)
    intro x
    simpa only [dist_eq_norm, Pi.sub_apply, Pi.add_apply] using! dist_triangle (F n i x) (F m i x)
        (q i x)
  simp only [Real.norm_eq_abs] at htri ⊢
  have hnm := hN n hn m hmN i
  simp only [Real.norm_eq_abs] at hnm hm
  linarith only [htri, hnm, hm]

end EmcsfAcExtension.Local
