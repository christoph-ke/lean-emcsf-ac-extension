module

public import EmcsfAcExtension.Local.Defs.Limit
public import EmcsfAcExtension.Infra.W11.Distance
import EmcsfAcExtension.Infra.Mixed.EnvelopeCauchy

/-! # Identification of strong scalar section limits

The analytic identification step in internal project record A1 and
`charged_SF_new_version.tex:L6450–6459`: an existing uniform limit of AC sections with
uniformly L¹-Cauchy derivatives is their AC primitive limit. This step keeps
ordinary derivatives and their sectionwise exceptional sets explicit.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace EmcsfAcExtension.Local

/-- Identify the uniform limit of a family of AC curves with its strong AC limit.
The derivative convergence is uniform over the sections; the primitive identities
hold at every endpoint. This is an auxiliary A1 identification, without a graph
closure claim or a numerical constant. -/
theorem ac_family_limit_of_derivative_cauchy {ι : Type*}
    {s t : ι → ℝ} {F : ℕ → ι → ℝ → ℂ} {f : ι → ℝ → ℂ}
    (hst : ∀ i, s i ≤ t i)
    (hF : ∀ n i, AbsolutelyContinuousOnInterval (F n i) (s i) (t i))
    (hlim : TendstoUniformlyOn (fun n (p : ι × ℝ) => F n p.1 p.2)
      (fun p => f p.1 p.2) atTop {p | p.2 ∈ Icc (s p.1) (t p.1)})
    (hC : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, ∀ i,
      (∫ x in s i..t i, ‖deriv (F n i) x - deriv (F m i) x‖) < ε) :
    (∀ i, AbsolutelyContinuousOnInterval (f i) (s i) (t i)) ∧
      (∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ i,
        (∫ x in s i..t i, ‖deriv (F n i) x - deriv (f i) x‖) < ε) ∧
      (∀ i x, x ∈ Icc (s i) (t i) →
        f i x = f i (s i) + ∫ y in s i..x, deriv (f i) y) := by
  have hz : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ i,
      ‖F n i (s i) - f i (s i)‖ < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((Metric.tendstoUniformlyOn_iff.mp hlim) ε hε)
    refine ⟨N, fun n hn i => ?_⟩
    simpa only [dist_comm, dist_eq_norm] using hN n hn (i, s i) ⟨le_rfl, hst i⟩
  obtain ⟨q, hq, hD, hac, hd, _, hprim⟩ :=
    Mixed.exists_ac_family_limit_of_uniform_derivative_cauchy hst hF hC hz
  have heq : ∀ i, EqOn (f i) (fun x => f i (s i) + ∫ y in s i..x, q i y)
      (Icc (s i) (t i)) := by
    intro i x hx
    exact tendsto_nhds_unique (hlim.tendsto_at (show
      (i, x) ∈ {p : ι × ℝ | p.2 ∈ Icc (s p.1) (t p.1)} from hx))
        (hprim.tendsto_at (show
          (i, x) ∈ {p : ι × ℝ | p.2 ∈ Icc (s p.1) (t p.1)} from hx))
  have hfac i : AbsolutelyContinuousOnInterval (f i) (s i) (t i) :=
    (hac i).congr (by simpa only [uIcc_of_le (hst i)] using (heq i).symm)
  have hdq i : deriv (f i) =ᵐ[volume.restrict (Icc (s i) (t i))] q i := by
    have ha : ∀ᵐ x : ℝ, x ≠ s i := by simp [ae_iff, measure_singleton]
    have hb : ∀ᵐ x : ℝ, x ≠ t i := by simp [ae_iff, measure_singleton]
    filter_upwards [hd i, ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae ha, ae_restrict_of_ae hb] with x hx hmem hxa hxb
    have hxx : x ∈ Ioo (s i) (t i) :=
      ⟨lt_of_le_of_ne hmem.1 hxa.symm, lt_of_le_of_ne hmem.2 hxb⟩
    have hevent : f i =ᶠ[𝓝 x] (fun x => f i (s i) + ∫ y in s i..x, q i y) :=
      Filter.eventuallyEq_of_mem (Icc_mem_nhds hxx.1 hxx.2) (heq i)
    exact hevent.deriv_eq.trans hx
  refine ⟨hfac, ?_, ?_⟩
  · intro ε hε
    obtain ⟨N, hN⟩ := hD ε hε
    refine ⟨N, fun n hn i => ?_⟩
    have hcongr : (∫ x in s i..t i, ‖deriv (F n i) x - deriv (f i) x‖) =
        ∫ x in s i..t i, ‖deriv (F n i) x - q i x‖ := by
      apply intervalIntegral.integral_congr_ae
      have hh := (ae_restrict_iff' measurableSet_Icc).mp (hdq i)
      filter_upwards [hh] with x hx hmem
      rw [uIoc_of_le (hst i)] at hmem
      rw [hx ⟨hmem.1.le, hmem.2⟩]
    rw [hcongr]
    exact hN n hn i
  · intro i x hx
    have hsub : uIcc (s i) x ⊆ uIcc (s i) (t i) := by
      rw [uIcc_of_le hx.1, uIcc_of_le (hst i)]
      exact Icc_subset_Icc le_rfl hx.2
    have hft := ((hfac i).mono hsub).integral_deriv_eq_sub_complex
    rw [hft]
    abel

end EmcsfAcExtension.Local
