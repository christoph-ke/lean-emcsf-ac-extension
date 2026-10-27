module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity
import EmcsfAcExtension.Infra.Mixed.TriangleCauchy
import EmcsfAcExtension.Infra.Mixed.FiberCauchy

/-! # Uniform integrability of classical stability envelopes

Mixed-norm Cauchy estimates give L¹-Cauchy Banach-valued fibers.
Completeness then gives uniform integrability of the fiber norms,
which are the actual outgoing and incoming envelopes on their labels.
This argument stays below Construction and Limit in the import graph.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace EmcsfAcExtension.Local

private theorem norm_fiber_ui_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {μ : Measure ℝ} {F : ℕ → ℝ → E}
    (hF : ∀ n, Integrable (F n) μ)
    (hC : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      (∫⁻ x, ‖F n x - F m x‖ₑ ∂μ) < ENNReal.ofReal ε) :
    UnifIntegrable (fun n x => ‖F n x‖) 1 μ := by
  have hc : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      (∫ x, ‖F n x - F m x‖ ∂μ) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    refine ⟨N, fun n hn m hm => ?_⟩
    have hh := hN n hn m hm
    have heq : ENNReal.ofReal (∫ x, ‖F n x - F m x‖ ∂μ) =
        ∫⁻ x, ‖F n x - F m x‖ₑ ∂μ := by
      simpa only [Pi.sub_apply] using!
        ofReal_integral_norm_eq_lintegral_enorm ((hF n).sub (hF m))
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mp (heq.trans_lt hh)
  obtain ⟨f, _, hf, hlim, _⟩ := Mixed.exists_L1_limit_of_integral_cauchy hF hc
  have hui := (Mixed.unifIntegrable_and_concentrationDefect_eq_zero_of_integral_tendsto
    hF hf hlim).1
  unfold UnifIntegrable at hui ⊢
  have heq : (fun ε : ℝ≥0∞ => ⨆ n, ⨆ s, ⨆ (_ : μ s ≤ ε),
      eLpNorm (fun x => ‖F n x‖) 1 (μ.restrict s)) =
      (fun ε : ℝ≥0∞ => ⨆ n, ⨆ s, ⨆ (_ : μ s ≤ ε), eLpNorm (F n) 1 (μ.restrict s)) := by
    funext ε
    apply iSup_congr
    intro n
    apply iSup_congr
    intro s
    apply iSup_congr
    intro hs
    exact eLpNorm_norm _ (hF n).aestronglyMeasurable.restrict
  rwa [heq]

/-- [internal]
Outgoing classical envelope families are uniformly integrable when their
mixed difference norms are Cauchy. No derivative supremum or additional
smallness condition is assumed, and no constant is selected. -/
theorem stab_out_envelope_uniform_integrability_c1 {e T : ℝ} {Sn : ℕ → Fields}
    (hT : 0 < T) (hS : ∀ n, IsC1Solution e (Sn n) (triangle 0 T))
    (hC : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      jDist T (Sn n) (Sn m) < ENNReal.ofReal ε) :
    UnifIntegrable (fun n v => (outEnv 0 (jC1 (triangle 0 T) (Sn n)) v).toReal) 1
      (volume.restrict (Icc 0 T)) := by
  let j := fun n => jC1 (triangle 0 T) (Sn n)
  have hj n := continuousOn_jC1_aux hT (hS n)
  let F n := Mixed.outgoingFiber hT.le (j n) (hj n)
  have hFi n : Integrable (F n) (volume.restrict (Icc 0 T)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).1
      ((Mixed.continuous_outgoingFiber hT.le (hj n)).intervalIntegrable 0 T)
  have hnorm n v (hv : v ∈ Icc 0 T) : ‖F n v‖ₑ = outEnv 0 (j n) v := by
    rw [ContinuousMap.enorm_eq_iSup_enorm, outEnv_def]
    rw [← Mixed.iSup_enorm_affine_eq (fun u => j n u v) hv.1]
    apply iSup_congr
    intro q
    simpa only [F, zero_add, sub_zero] using congrArg enorm
      (Mixed.outgoingFiber_apply (j := j n) hT.le (hj n) hv q)
  have hsub n m v (hv : v ∈ Icc 0 T) : ‖F n v - F m v‖ₑ =
      outEnv 0 (fun u v => j n u v - j m u v) v := by
    rw [ContinuousMap.enorm_eq_iSup_enorm, outEnv_def]
    rw [← Mixed.iSup_enorm_affine_eq (fun u => j n u v - j m u v) hv.1]
    apply iSup_congr
    intro q
    simp only [ContinuousMap.sub_apply, F,
      Mixed.outgoingFiber_apply (j := j n) hT.le (hj n) hv q,
      Mixed.outgoingFiber_apply (j := j m) hT.le (hj m) hv q, zero_add, sub_zero]
  have hFC : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      (∫⁻ v in Icc 0 T, ‖F n v - F m v‖ₑ) < ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    refine ⟨N, fun n hn m hm => ?_⟩
    have heq : (∫⁻ v in Icc 0 T, ‖F n v - F m v‖ₑ) = jDist T (Sn n) (Sn m) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro v hv
      exact hsub n m v hv
    rw [heq]
    exact hN n hn m hm
  have hui := norm_fiber_ui_aux hFi hFC
  apply hui.ae_eq
  intro n
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  have hh := congrArg ENNReal.toReal (hnorm n v hv)
  simpa only [toReal_enorm] using hh

/-- [internal]
Incoming classical envelope families are uniformly integrable under
mixed Cauchy control. The proof uses the incoming affine fibers and
has no outgoing estimate of the incoming ratio as a premise. -/
theorem stab_in_envelope_uniform_integrability_c1 {e T : ℝ} {Sn : ℕ → Fields}
    (hT : 0 < T) (hS : ∀ n, IsC1Solution e (Sn n) (triangle 0 T))
    (hC : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      kDist e T (Sn n) (Sn m) < ENNReal.ofReal ε) :
    UnifIntegrable (fun n u => (inEnv T (kC1 e (triangle 0 T) (Sn n)) u).toReal) 1
      (volume.restrict (Icc 0 T)) := by
  let k := fun n => kC1 e (triangle 0 T) (Sn n)
  have hk n := continuousOn_kC1_aux hT (hS n)
  let F n := Mixed.incomingFiber hT.le (k n) (hk n)
  have hFi n : Integrable (F n) (volume.restrict (Icc 0 T)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).1
      ((Mixed.continuous_incomingFiber hT.le (hk n)).intervalIntegrable 0 T)
  have hnorm n u (hu : u ∈ Icc 0 T) : ‖F n u‖ₑ = inEnv T (k n) u := by
    rw [ContinuousMap.enorm_eq_iSup_enorm, inEnv_def]
    rw [← Mixed.iSup_enorm_affine_eq (fun v => k n u v) hu.2]
    apply iSup_congr
    intro q
    exact congrArg enorm (Mixed.incomingFiber_apply (k := k n) hT.le (hk n) hu q)
  have hsub n m u (hu : u ∈ Icc 0 T) : ‖F n u - F m u‖ₑ =
      inEnv T (fun u v => k n u v - k m u v) u := by
    rw [ContinuousMap.enorm_eq_iSup_enorm, inEnv_def]
    rw [← Mixed.iSup_enorm_affine_eq (fun v => k n u v - k m u v) hu.2]
    apply iSup_congr
    intro q
    simp only [ContinuousMap.sub_apply, F,
      Mixed.incomingFiber_apply (k := k n) hT.le (hk n) hu q,
      Mixed.incomingFiber_apply (k := k m) hT.le (hk m) hu q]
  have hFC : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      (∫⁻ u in Icc 0 T, ‖F n u - F m u‖ₑ) < ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    refine ⟨N, fun n hn m hm => ?_⟩
    have heq : (∫⁻ u in Icc 0 T, ‖F n u - F m u‖ₑ) = kDist e T (Sn n) (Sn m) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro u hu
      exact hsub n m u hu
    rw [heq]
    exact hN n hn m hm
  have hui := norm_fiber_ui_aux hFi hFC
  apply hui.ae_eq
  intro n
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  have hh := congrArg ENNReal.toReal (hnorm n u hu)
  simpa only [toReal_enorm] using hh

end EmcsfAcExtension.Local
