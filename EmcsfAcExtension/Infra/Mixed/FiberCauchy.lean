module

public import EmcsfAcExtension.Infra.UnifIntegrable
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# L¹ completeness with common fiber representatives

Auxiliary analysis A5 of internal project record. A compact continuous
fiber is a Banach-valued function of its section label. L¹ completeness and an
a.e. convergent subsequence give a single measurable exceptional set of labels;
no exceptional set is chosen separately for each point on a fiber.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace EmcsfAcExtension.Mixed

private theorem norm_toL1_sub {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ) :
    ‖hf.toL1 f - hg.toL1 g‖ = ∫ x, ‖f x - g x‖ ∂μ := by
  rw [← Integrable.toL1_sub, L1.norm_of_fun_eq_integral_norm]
  rfl

/-- Real L¹ error convergence gives extended L¹ error convergence, uniformly in
all measure spaces and normed targets, with coefficient one. -/
theorem tendsto_eLpNorm_one_of_integral {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {F : ℕ → α → E} {f : α → E}
    (hF : ∀ n, Integrable (F n) μ) (hf : Integrable f μ)
    (hlim : Tendsto (fun n => ∫ x, ‖F n x - f x‖ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n - f) 1 μ) atTop (𝓝 0) := by
  have heq n : eLpNorm (F n - f) 1 μ = ENNReal.ofReal (∫ x, ‖F n x - f x‖ ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm ((hF n).sub hf).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hF n).sub hf)]
    rfl
  simpa only [heq, ENNReal.ofReal_zero, Function.comp_apply] using!
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim

/-- A5: an L¹ convergent sequence is uniformly integrable and has zero project
concentration defect. No finite-measure assumption or additional bound is required. -/
theorem unifIntegrable_and_concentrationDefect_eq_zero_of_integral_tendsto
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {F : ℕ → α → E} {f : α → E}
    (hF : ∀ n, Integrable (F n) μ) (hf : Integrable f μ)
    (hlim : Tendsto (fun n => ∫ x, ‖F n x - f x‖ ∂μ) atTop (𝓝 0)) :
    UnifIntegrable F 1 μ ∧ concentrationDefect F μ = 0 := by
  have hui : UnifIntegrable F 1 μ := unifIntegrable_of_tendsto_Lp le_rfl (by simp)
    (fun n => (memLp_one_iff_integrable).2 (hF n))
    ((memLp_one_iff_integrable).2 hf) (tendsto_eLpNorm_one_of_integral hF hf hlim)
  exact ⟨hui, (concentrationDefect_eq_zero_iff (fun n => (hF n).aestronglyMeasurable)).2 hui⟩

/-- A5 Banach-valued completeness: choose a strongly measurable L¹ limit, a
subsequence, and one measurable null set on which that representative vanishes.
The whole sequence converges in L¹ and its norm integrals converge exactly.
Taking the Banach space to be continuous functions on a compact fiber gives
uniform fiber convergence, rather than merely pointwise convergence on that fiber. -/
theorem exists_L1_limit_of_integral_cauchy {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} {F : ℕ → α → E}
    (hF : ∀ n, Integrable (F n) μ)
    (hC : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      (∫ x, ‖F n x - F m x‖ ∂μ) < ε) :
    ∃ f : α → E, StronglyMeasurable f ∧ Integrable f μ ∧
      Tendsto (fun n => ∫ x, ‖F n x - f x‖ ∂μ) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ x, ‖F n x‖ ∂μ) atTop (𝓝 (∫ x, ‖f x‖ ∂μ)) ∧
      ∃ ns : ℕ → ℕ, ∃ N : Set α, StrictMono ns ∧ MeasurableSet N ∧ μ N = 0 ∧
        (∀ x ∈ N, f x = 0) ∧
        ∀ x ∉ N, Tendsto (fun l => F (ns l) x) atTop (𝓝 (f x)) := by
  let G : ℕ → Lp E 1 μ := fun n => (hF n).toL1 (F n)
  have hGC : CauchySeq G := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    refine ⟨N, fun n hn m hm => ?_⟩
    rw [dist_eq_norm, norm_toL1_sub]
    exact hN n hn m hm
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hGC
  have hgi : Integrable (g : α → E) μ := L1.integrable_coeFn g
  have hlim : Tendsto (fun n => ∫ x, ‖F n x - g x‖ ∂μ) atTop (𝓝 0) := by
    have heq n : (∫ x, ‖F n x - g x‖ ∂μ) = ‖G n - g‖ := by
      rw [← norm_toL1_sub (hF n) hgi, Integrable.toL1_coeFn]
    simpa only [heq] using tendsto_iff_norm_sub_tendsto_zero.1 hg
  have hmeas := tendstoInMeasure_of_tendsto_eLpNorm (by simp : (1 : ℝ≥0∞) ≠ 0)
    (tendsto_eLpNorm_one_of_integral hF hgi hlim)
  obtain ⟨ns, hns, hns_lim⟩ := hmeas.exists_seq_tendsto_ae
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hns_lim)
  let f : α → E := Nᶜ.indicator g
  have hf : StronglyMeasurable f := (Lp.stronglyMeasurable g).indicator hNm.compl
  have heq : f =ᵐ[μ] g := by
    have ha : ∀ᵐ x ∂μ, x ∉ N := by simpa [ae_iff] using hN0
    filter_upwards [ha] with x hx
    exact indicator_of_mem hx g
  have hfi : Integrable f μ := hgi.congr heq.symm
  have hnorm_eq : (∫ x, ‖f x‖ ∂μ) = ‖g‖ := by
    rw [integral_congr_ae (heq.mono fun x hx => congrArg norm hx),
      ← L1.norm_of_fun_eq_integral_norm hgi, Integrable.toL1_coeFn]
  refine ⟨f, hf, hfi, ?_, ?_, ns, N, hns, hNm, hN0, ?_, ?_⟩
  · convert hlim using 1
    ext n
    apply integral_congr_ae
    filter_upwards [heq] with x hx
    rw [hx]
  · have hn n : (∫ x, ‖F n x‖ ∂μ) = ‖G n‖ := (L1.norm_of_fun_eq_integral_norm (hF n)).symm
    simpa only [hn, hnorm_eq] using hg.norm
  · intro x hx
    exact indicator_of_notMem (not_not.mpr hx) g
  · intro x hx
    have hgood : Tendsto (fun l => F (ns l) x) atTop (𝓝 (g x)) := by
      by_contra h
      exact hx (hNsub h)
    simpa only [f, indicator_of_mem (show x ∈ Nᶜ from hx)] using hgood

end EmcsfAcExtension.Mixed
