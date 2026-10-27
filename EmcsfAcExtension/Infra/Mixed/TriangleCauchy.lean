module

public import EmcsfAcExtension.Infra.Mixed.ParametricLimit

/-!
# Completeness of both mixed norms on a closed triangle

Auxiliary analysis A5 of internal project record. The outgoing envelope
uses `u = q*v`; the incoming envelope uses `v = u + q*(T-u)`. Existing envelope
continuity supplies measurability. The representative theorem uses one null set
per family, uniform convergence on each good fiber, and the original sequence's
mixed-norm convergence.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace EmcsfAcExtension.Mixed

/-- The outgoing fiber as a continuous function of its unit-interval parameter.
Projection extends the original continuous field off the controlled triangle. -/
@[expose] def outgoingFiber {T : ℝ} (hT : 0 ≤ T) (j : ℝ → ℝ → ℂ)
    (hj : ContinuousOn (Function.uncurry j) (triangle 0 T)) (v : ℝ) :
    C(Icc (0 : ℝ) 1, ℂ) where
  toFun q := Function.uncurry j (triangleProj 0 T (q.1 * v, v))
  continuous_toFun := (continuous_comp_triangleProj hT hj).comp
    ((continuous_subtype_val.mul continuous_const).prodMk continuous_const)

/-- The outgoing continuous fiber depends continuously on its label. -/
theorem continuous_outgoingFiber {T : ℝ} (hT : 0 ≤ T) {j : ℝ → ℝ → ℂ}
    (hj : ContinuousOn (Function.uncurry j) (triangle 0 T)) :
    Continuous (outgoingFiber hT j hj) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_comp_triangleProj hT hj).comp
    ((continuous_snd.subtype_val.mul continuous_fst).prodMk continuous_fst)

/-- The outgoing parametrization agrees with the original field on every
controlled section, including the degenerate fiber at the axis. -/
theorem outgoingFiber_apply {T v : ℝ} (hT : 0 ≤ T) {j : ℝ → ℝ → ℂ}
    (hj : ContinuousOn (Function.uncurry j) (triangle 0 T)) (hv : v ∈ Icc 0 T)
    (q : Icc (0 : ℝ) 1) : outgoingFiber hT j hj v q = j (q.1 * v) v := by
  have hp : (q.1 * v, v) ∈ triangle 0 T :=
    ⟨mul_nonneg q.property.1 hv.1,
      mul_le_of_le_one_left hv.1 q.property.2, hv.2⟩
  change Function.uncurry j (triangleProj 0 T (q.1 * v, v)) = _
  rw [triangleProj_of_mem hp]
  rfl

/-- The incoming fiber uses exactly `v = u + q*(T-u)` on the unit interval. -/
@[expose] def incomingFiber {T : ℝ} (hT : 0 ≤ T) (k : ℝ → ℝ → ℂ)
    (hk : ContinuousOn (Function.uncurry k) (triangle 0 T)) (u : ℝ) :
    C(Icc (0 : ℝ) 1, ℂ) where
  toFun q := Function.uncurry k (triangleProj 0 T (u, u + q.1 * (T - u)))
  continuous_toFun := (continuous_comp_triangleProj hT hk).comp
    (continuous_const.prodMk
      (continuous_const.add (continuous_subtype_val.mul continuous_const)))

/-- The incoming continuous fiber depends continuously on its label. -/
theorem continuous_incomingFiber {T : ℝ} (hT : 0 ≤ T) {k : ℝ → ℝ → ℂ}
    (hk : ContinuousOn (Function.uncurry k) (triangle 0 T)) :
    Continuous (incomingFiber hT k hk) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_comp_triangleProj hT hk).comp
    (continuous_fst.prodMk (continuous_fst.add
      (continuous_snd.subtype_val.mul (continuous_const.sub continuous_fst))))

/-- The incoming parametrization agrees with the original field on controlled
sections, including the degenerate fiber at the final vertex. -/
theorem incomingFiber_apply {T u : ℝ} (hT : 0 ≤ T) {k : ℝ → ℝ → ℂ}
    (hk : ContinuousOn (Function.uncurry k) (triangle 0 T)) (hu : u ∈ Icc 0 T)
    (q : Icc (0 : ℝ) 1) : incomingFiber hT k hk u q = k u (u + q.1 * (T - u)) := by
  have hp : (u, u + q.1 * (T - u)) ∈ triangle 0 T :=
    ⟨hu.1, by change u ≤ u + q.1 * (T - u); nlinarith [q.property.1, hu.2],
      by change u + q.1 * (T - u) ≤ T; nlinarith [q.property.2, hu.2]⟩
  change Function.uncurry k (triangleProj 0 T (u, u + q.1 * (T - u))) = _
  rw [triangleProj_of_mem hp]
  rfl

private theorem integral_cauchy_of_mixed_cauchy {μ : Measure ℝ} {S : Set ℝ}
    {a b : ℝ → ℝ} {j : ℕ → ℝ → ℝ → ℂ}
    {F : ℕ → ℝ → C(Icc (0 : ℝ) 1, ℂ)}
    (hS : MeasurableSet S) (hab : ∀ v ∈ S, a v ≤ b v)
    (hrep : ∀ n v, v ∈ S → ∀ q : Icc (0 : ℝ) 1,
      F n v q = j n (a v + q.1 * (b v - a v)) v)
    (hF : ∀ n, Integrable (F n) (μ.restrict S))
    (hC : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      (∫⁻ v in S, ⨆ u ∈ Icc (a v) (b v), ‖j n u v - j m u v‖ₑ ∂μ) <
        ENNReal.ofReal ε) :
    ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      (∫ v in S, ‖F n v - F m v‖ ∂μ) < ε := by
  have henv n m v (hv : v ∈ S) :
      ‖F n v - F m v‖ₑ = ⨆ u ∈ Icc (a v) (b v), ‖j n u v - j m u v‖ₑ := by
    rw [← iSup_enorm_affine_eq (fun u => j n u v - j m u v) (hab v hv),
      ContinuousMap.enorm_eq_iSup_enorm]
    apply iSup_congr
    intro q
    rw [ContinuousMap.sub_apply, hrep n v hv q, hrep m v hv q]
  have hint n m : ENNReal.ofReal (∫ v in S, ‖F n v - F m v‖ ∂μ) =
      ∫⁻ v in S, ⨆ u ∈ Icc (a v) (b v), ‖j n u v - j m u v‖ₑ ∂μ := by
    calc
      _ = ∫⁻ v in S, ‖F n v - F m v‖ₑ ∂μ := by
        simpa only [Pi.sub_apply] using!
          ofReal_integral_norm_eq_lintegral_enorm ((hF n).sub (hF m))
      _ = _ := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem hS] with v hv
        exact henv n m v hv
  intro ε hε
  obtain ⟨N, hN⟩ := hC ε hε
  refine ⟨N, fun n hn m hm => (ENNReal.ofReal_lt_ofReal_iff hε).mp ?_⟩
  rw [hint]
  exact hN n hn m hm

/-- A5 outgoing mixed-norm completeness on the closed triangle. Every estimate
has coefficient one, uniformly in `T` and the continuous sequence. The resulting
measurable envelope dominates the representative at every point, hence also a.e.
The original whole sequence converges in mixed L¹ and its envelope masses converge
exactly to the mass of the limiting envelope. -/
theorem exists_outgoing_mixed_limit {T : ℝ} {j : ℕ → ℝ → ℝ → ℂ}
    (hT : 0 ≤ T) (hj : ∀ n, ContinuousOn (Function.uncurry (j n)) (triangle 0 T))
    (hC : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      (∫⁻ v in Icc 0 T, normEnvelope (fun u v => j n u v - j m u v) 0 v) <
        ENNReal.ofReal ε) :
    ∃ ns : ℕ → ℕ, ∃ N : Set ℝ, ∃ f : ℝ → ℝ → ℂ, ∃ J : ℝ → ℝ≥0∞,
      StrictMono ns ∧ MeasurableSet N ∧ volume N = 0 ∧ N ⊆ Icc 0 T ∧
      Measurable (Function.uncurry f) ∧ Measurable J ∧
      (∀ v ∈ N, ∀ u, f u v = 0) ∧
      (∀ v ∈ Icc 0 T, v ∉ N → TendstoUniformlyOn (fun l u => j (ns l) u v)
        (fun u => f u v) atTop (Icc 0 v)) ∧
      (∀ u v, ‖f u v‖ₑ ≤ J v) ∧ (∫⁻ v in Icc 0 T, J v) < ⊤ ∧
      Tendsto (fun n => ∫⁻ v in Icc 0 T, normEnvelope (fun u v => j n u v - f u v) 0 v)
        atTop (𝓝 0) ∧
      Tendsto (fun n => ∫⁻ v in Icc 0 T, normEnvelope (j n) 0 v)
        atTop (𝓝 (∫⁻ v in Icc 0 T, J v)) := by
  let F n := outgoingFiber hT (j n) (hj n)
  have hFi n : Integrable (F n) (volume.restrict (Icc 0 T)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mp
      ((continuous_outgoingFiber hT (hj n)).intervalIntegrable 0 T)
  have hrep : ∀ n v, v ∈ Icc 0 T → ∀ q : Icc (0 : ℝ) 1,
      F n v q = j n (0 + q.1 * (v - 0)) v := by
    intro n v hv q
    simpa only [zero_add, sub_zero] using outgoingFiber_apply hT (hj n) hv q
  have hlt : ∀ᵐ v ∂volume.restrict (Icc 0 T), (0 : ℝ) < v := by
    have hn : ∀ᵐ v : ℝ, v ≠ 0 := by simp [ae_iff, measure_singleton]
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hn] with v hv hn
    exact lt_of_le_of_ne hv.1 hn.symm
  have hc := integral_cauchy_of_mixed_cauchy measurableSet_Icc
    (fun v hv => hv.1) hrep hFi (by simpa only [normEnvelope] using hC)
  simpa only [normEnvelope, id_eq] using! exists_parametric_mixed_limit (j := j) measurableSet_Icc
    measurable_const measurable_id (fun v hv => hv.1) hlt hrep hFi hc

/-- A5 incoming mixed-norm completeness with the parametrization
`v = u + q*(T-u)`. The common null set consists of incoming labels `u`.
The coefficient-one bounds and exact envelope mass limit are uniform in `T`. -/
theorem exists_incoming_mixed_limit {T : ℝ} {k : ℕ → ℝ → ℝ → ℂ}
    (hT : 0 ≤ T) (hk : ∀ n, ContinuousOn (Function.uncurry (k n)) (triangle 0 T))
    (hC : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      (∫⁻ u in Icc 0 T, ⨆ v ∈ Icc u T, ‖k n u v - k m u v‖ₑ) < ENNReal.ofReal ε) :
    ∃ ns : ℕ → ℕ, ∃ N : Set ℝ, ∃ f : ℝ → ℝ → ℂ, ∃ K : ℝ → ℝ≥0∞,
      StrictMono ns ∧ MeasurableSet N ∧ volume N = 0 ∧ N ⊆ Icc 0 T ∧
      Measurable (Function.uncurry f) ∧ Measurable K ∧
      (∀ u ∈ N, ∀ v, f u v = 0) ∧
      (∀ u ∈ Icc 0 T, u ∉ N → TendstoUniformlyOn (fun l v => k (ns l) u v)
        (fun v => f u v) atTop (Icc u T)) ∧
      (∀ u v, ‖f u v‖ₑ ≤ K u) ∧ (∫⁻ u in Icc 0 T, K u) < ⊤ ∧
      Tendsto (fun n => ∫⁻ u in Icc 0 T, ⨆ v ∈ Icc u T, ‖k n u v - f u v‖ₑ)
        atTop (𝓝 0) ∧
      Tendsto (fun n => ∫⁻ u in Icc 0 T, ⨆ v ∈ Icc u T, ‖k n u v‖ₑ)
        atTop (𝓝 (∫⁻ u in Icc 0 T, K u)) := by
  let F n := incomingFiber hT (k n) (hk n)
  have hFi n : Integrable (F n) (volume.restrict (Icc 0 T)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mp
      ((continuous_incomingFiber hT (hk n)).intervalIntegrable 0 T)
  have hrep : ∀ n u, u ∈ Icc 0 T → ∀ q : Icc (0 : ℝ) 1,
      F n u q = k n u (u + q.1 * (T - u)) := by
    intro n u hu q
    exact incomingFiber_apply hT (hk n) hu q
  have hlt : ∀ᵐ u ∂volume.restrict (Icc 0 T), u < T := by
    have hn : ∀ᵐ u : ℝ, u ≠ T := by simp [ae_iff, measure_singleton]
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hn] with u hu hn
    exact lt_of_le_of_ne hu.2 hn
  have hc := integral_cauchy_of_mixed_cauchy
    (j := fun n v u => k n u v) measurableSet_Icc (fun u hu => hu.2) hrep hFi hC
  obtain ⟨ns, N, f, K, hns, hNm, hN0, hNsub, hfm, hKm, hfzero, hseq, hdom,
      hKi, hlim, hnorm⟩ := exists_parametric_mixed_limit
        (j := fun n v u => k n u v) measurableSet_Icc
        measurable_id measurable_const (fun u hu => hu.2) hlt hrep hFi hc
  refine ⟨ns, N, fun u v => f v u, K, hns, hNm, hN0, hNsub, ?_, hKm,
    hfzero, hseq, fun u v => hdom v u, hKi, hlim, hnorm⟩
  exact hfm.comp measurable_swap

/-- The incoming supremum of a continuous field, extended by zero outside the
label interval, is measurable. This uses continuity of the same unit-interval
parametrization and agrees with the uncountable supremum exactly. -/
theorem measurable_indicator_incoming_envelope {T : ℝ} (hT : 0 ≤ T)
    {k : ℝ → ℝ → ℂ} (hk : ContinuousOn (Function.uncurry k) (triangle 0 T)) :
    Measurable ((Icc (0 : ℝ) T).indicator (fun u => ⨆ v ∈ Icc u T, ‖k u v‖ₑ)) := by
  have henv u (hu : u ∈ Icc 0 T) : (⨆ v ∈ Icc u T, ‖k u v‖ₑ) =
      ‖incomingFiber hT k hk u‖ₑ := by
    rw [← iSup_enorm_affine_eq (fun v => k u v) hu.2, ContinuousMap.enorm_eq_iSup_enorm]
    apply iSup_congr
    intro q
    rw [incomingFiber_apply hT hk hu q]
  have hm : Measurable ((Icc (0 : ℝ) T).indicator
      (fun u => ‖incomingFiber hT k hk u‖ₑ)) :=
    ((continuous_incomingFiber hT hk).measurable.enorm).indicator measurableSet_Icc
  convert hm using 1
  ext u
  by_cases hu : u ∈ Icc 0 T
  · simp only [indicator_of_mem hu, henv u hu]
  · simp only [indicator_of_notMem hu]

end EmcsfAcExtension.Mixed
