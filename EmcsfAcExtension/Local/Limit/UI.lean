module

public import EmcsfAcExtension.Local.Defs.Envelope
public import EmcsfAcExtension.Local.Defs.C1Class
public import EmcsfAcExtension.Infra.UnifIntegrable
import EmcsfAcExtension.Local.Limit.UIAux
import EmcsfAcExtension.Infra.Mixed.TriangleCauchy

/-! # Uniform integrability from strong same-label comparison

internal project record A5 and `charged_SF_new_version.tex:L5567–5576,L6448–6449`. The Cauchy
hypotheses
are the mixed-envelope components of `#strong-same-label-cauchy`. The proof
uses Banach-valued L¹ completeness, retaining the entire continuous fiber.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

private theorem unifIntegrable_norm_of_cauchy {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure ℝ} {F : ℕ → ℝ → E}
    (hF : ∀ n, Integrable (F n) μ)
    (hC : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      (∫⁻ v, ‖F n v - F m v‖ₑ ∂μ) < ENNReal.ofReal ε) :
    UnifIntegrable (fun n v => ‖F n v‖) 1 μ := by
  have hc : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      (∫ v, ‖F n v - F m v‖ ∂μ) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    refine ⟨N, fun n hn m hm => (ENNReal.ofReal_lt_ofReal_iff hε).mp ?_⟩
    have he : ENNReal.ofReal (∫ v, ‖F n v - F m v‖ ∂μ) =
        ∫⁻ v, ‖F n v - F m v‖ₑ ∂μ := by
      simpa only [Pi.sub_apply] using
        ofReal_integral_norm_eq_lintegral_enorm ((hF n).sub (hF m))
    rw [he]
    exact hN n hn m hm
  obtain ⟨f, _, hf, hlim, _⟩ := Mixed.exists_L1_limit_of_integral_cauchy hF hc
  have hui : UnifIntegrable F 1 μ :=
    (Mixed.unifIntegrable_and_concentrationDefect_eq_zero_of_integral_tendsto
    hF hf hlim).1
  rw [unifIntegrable_iff] at hui ⊢
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := hui ε hε
  refine ⟨δ, hδ, fun n s hs => ?_⟩
  rw [eLpNorm_norm (F n) (hF n).aestronglyMeasurable.restrict]
  exact hsmall n s hs

private theorem outgoing_ui_of_cauchy {T : ℝ} {j : ℕ → ℝ → ℝ → ℂ}
    (hT : 0 ≤ T) (hj : ∀ n, ContinuousOn (Function.uncurry (j n)) (triangle 0 T))
    (hC : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      (∫⁻ v in Icc 0 T, outEnv 0 (fun u v => j n u v - j m u v) v) <
        ENNReal.ofReal ε) :
    UnifIntegrable (fun n v => (outEnv 0 (j n) v).toReal) 1
      (volume.restrict (Icc 0 T)) := by
  let F n := Mixed.outgoingFiber hT (j n) (hj n)
  have hFi n : Integrable (F n) (volume.restrict (Icc 0 T)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mp
      ((Mixed.continuous_outgoingFiber hT (hj n)).intervalIntegrable 0 T)
  have heq n m v (hv : v ∈ Icc 0 T) :
      ‖F n v - F m v‖ₑ = outEnv 0 (fun u v => j n u v - j m u v) v := by
    rw [outEnv_def, ← Mixed.iSup_enorm_affine_eq (fun u => j n u v - j m u v) hv.1,
      ContinuousMap.enorm_eq_iSup_enorm]
    apply iSup_congr
    intro q
    rw [ContinuousMap.sub_apply, Mixed.outgoingFiber_apply hT (hj n) hv q,
      Mixed.outgoingFiber_apply hT (hj m) hv q]
    simp only [zero_add, sub_zero]
  have hui := unifIntegrable_norm_of_cauchy hFi (by
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    refine ⟨N, fun n hn m hm => ?_⟩
    rw [show (∫⁻ v in Icc 0 T, ‖F n v - F m v‖ₑ) =
      ∫⁻ v in Icc 0 T, outEnv 0 (fun u v => j n u v - j m u v) v from
        setLIntegral_congr_fun measurableSet_Icc (heq n m)]
    exact hN n hn m hm)
  apply hui.ae_eq
  intro n
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  have hh : ‖F n v‖ₑ = outEnv 0 (j n) v := by
    rw [outEnv_def, ← Mixed.iSup_enorm_affine_eq (fun u => j n u v) hv.1,
      ContinuousMap.enorm_eq_iSup_enorm]
    apply iSup_congr
    intro q
    rw [Mixed.outgoingFiber_apply hT (hj n) hv q]
    simp only [zero_add, sub_zero]
  simpa only [toReal_enorm] using congrArg ENNReal.toReal hh

private theorem incoming_ui_of_cauchy {T : ℝ} {k : ℕ → ℝ → ℝ → ℂ}
    (hT : 0 ≤ T) (hk : ∀ n, ContinuousOn (Function.uncurry (k n)) (triangle 0 T))
    (hC : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      (∫⁻ u in Icc 0 T, inEnv T (fun u v => k n u v - k m u v) u) <
        ENNReal.ofReal ε) :
    UnifIntegrable (fun n u => (inEnv T (k n) u).toReal) 1
      (volume.restrict (Icc 0 T)) := by
  let F n := Mixed.incomingFiber hT (k n) (hk n)
  have hFi n : Integrable (F n) (volume.restrict (Icc 0 T)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mp
      ((Mixed.continuous_incomingFiber hT (hk n)).intervalIntegrable 0 T)
  have heq n m u (hu : u ∈ Icc 0 T) :
      ‖F n u - F m u‖ₑ = inEnv T (fun u v => k n u v - k m u v) u := by
    rw [inEnv, ← Mixed.iSup_enorm_affine_eq (fun v => k n u v - k m u v) hu.2,
      ContinuousMap.enorm_eq_iSup_enorm]
    apply iSup_congr
    intro q
    rw [ContinuousMap.sub_apply, Mixed.incomingFiber_apply hT (hk n) hu q,
      Mixed.incomingFiber_apply hT (hk m) hu q]
  have hui := unifIntegrable_norm_of_cauchy hFi (by
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    refine ⟨N, fun n hn m hm => ?_⟩
    rw [show (∫⁻ u in Icc 0 T, ‖F n u - F m u‖ₑ) =
      ∫⁻ u in Icc 0 T, inEnv T (fun u v => k n u v - k m u v) u from
        setLIntegral_congr_fun measurableSet_Icc (heq n m)]
    exact hN n hn m hm)
  apply hui.ae_eq
  intro n
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  have hh : ‖F n u‖ₑ = inEnv T (k n) u := by
    rw [inEnv, ← Mixed.iSup_enorm_affine_eq (fun v => k n u v) hu.2,
      ContinuousMap.enorm_eq_iSup_enorm]
    apply iSup_congr
    intro q
    rw [Mixed.incomingFiber_apply hT (hk n) hu q]
  simpa only [toReal_enorm] using congrArg ENNReal.toReal hh

/-- [internal]
The strong mixed-envelope Cauchy property makes both classical envelope families
uniformly integrable over their full label interval. Uniformity is in the entire
approximation index, with no derivative supremum bound or selected constant. -/
theorem Null.envelope_uniform_integrability_of_cauchy {e T : ℝ} {Sn : ℕ → Fields}
    (hT : 0 < T) (hS : ∀ n, IsC1Solution e (Sn n) (triangle 0 T))
    (hj : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      jDist T (Sn n) (Sn m) < ENNReal.ofReal ε)
    (hk : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      kDist e T (Sn n) (Sn m) < ENNReal.ofReal ε) :
    UnifIntegrable (fun n v => (outEnv 0 (jC1 (triangle 0 T) (Sn n)) v).toReal) 1
        (volume.restrict (Icc 0 T)) ∧
      UnifIntegrable (fun n u => (inEnv T (kC1 e (triangle 0 T) (Sn n)) u).toReal) 1
        (volume.restrict (Icc 0 T)) := by
  exact ⟨outgoing_ui_of_cauchy hT.le (fun n => (hS n).continuousOn_jC1 hT) hj,
    incoming_ui_of_cauchy hT.le (fun n => (hS n).continuousOn_kC1 hT) hk⟩

end EmcsfAcExtension.Local
