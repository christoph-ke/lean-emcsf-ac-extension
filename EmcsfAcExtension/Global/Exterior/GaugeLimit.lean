module

public import EmcsfAcExtension.Global.Calculus.Gauge
public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Domains
import EmcsfAcExtension.Global.Api.Definitions
import EmcsfAcExtension.Infra.AC.Variation

/-! # The frontier comparison gauge and its complex endpoint

The phase is constructed on `u < 0`, by a proper integral of the original
frontier potential. Its convergence at zero is neither needed nor asserted.
Density and variation estimates are inputs in the original gauge. Source:
`charged_SF_new_version.tex:L1417–1424`; approved internal project record, (G1)–(G4).
-/

public section

open Set Filter Topology MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.Exterior

variable {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}

/-- [internal] The normalized outgoing scalar transforms by the same
unit phase as the scalar itself. The geometric fields are unchanged. -/
theorem gaugeFields_a (e : ℝ) (S : Fields) (χ : ℝ → ℝ) (u v : ℝ) :
    (gaugeFields e S χ).a u v = Complex.exp (I * e * χ u) * S.a u v := by
  simp only [Fields.a, gaugeFields, mul_add, mul_div_assoc]

/-- [node c:exterior#frontier-gauge-choice]
Construct a residual gauge on the whole original incoming interval,
normalized on the initial row, with zero frontier potential. Regularity
is C¹ on `u < 0`, with pointwise derivatives there, as required by internal project record.
The original zero-axis-potential normalization is not imposed on this
comparison gauge (`charged_SF_new_version.tex:L1417–1420`). -/
theorem frontier_gauge_choice (hS : IsSolution e S D) {ui uc : ℝ}
    (hui : ui < 0) (huc : uc < 0) {V : ℝ → ℝ}
    (hV : ContinuousOn V (Ico uc 0))
    (hmem : ∀ u ∈ Ico uc 0, (u, V u) ∈ D) :
    ∃ χ : ℝ → ℝ, ContDiffOn ℝ 1 χ (Iio 0) ∧ χ ui = 0 ∧
      (∀ u ∈ Ico uc 0, HasDerivAt χ (S.A u (V u)) u) ∧
      (∀ u ∈ Ico uc 0, (gaugeFields e S χ).A u (V u) = 0) ∧
      (∀ v, (gaugeFields e S χ).a ui v = S.a ui v) := by
  let π : ℝ → ℝ := fun u => max uc u
  have cπ : Continuous π := continuous_const.max continuous_id
  have mπ (u : ℝ) (hu : u ∈ Iio (0 : ℝ)) : π u ∈ Ico uc 0 :=
    ⟨le_max_left _ _, max_lt huc hu⟩
  let q : ℝ → ℝ := fun u => S.A (π u) (V (π u))
  have cq : ContinuousOn q (Iio 0) := hS.cont_A.comp
    (cπ.continuousOn.prodMk (hV.comp cπ.continuousOn mπ))
    (fun u hu => hmem _ (mπ u hu))
  have hqi (u : ℝ) (hu : u < 0) : IntervalIntegrable q volume ui u :=
    (cq.mono (fun x hx => (hx.2.trans_lt (max_lt hui hu)))).intervalIntegrable
  let χ : ℝ → ℝ := fun u => ∫ s in ui..u, q s
  have hd (u : ℝ) (hu : u < 0) : HasDerivAt χ (q u) u :=
    intervalIntegral.integral_hasDerivAt_right (hqi u hu)
      (cq.stronglyMeasurableAtFilter isOpen_Iio u hu)
      (cq.continuousAt (isOpen_Iio.mem_nhds hu))
  have hc : ContDiffOn ℝ 1 χ (Iio 0) := by
    apply (contDiffOn_one_iff_derivWithin isOpen_Iio.uniqueDiffOn).2
    refine ⟨fun u hu => (hd u hu).differentiableAt.differentiableWithinAt, ?_⟩
    apply cq.congr
    intro u hu
    rw [derivWithin_of_isOpen isOpen_Iio hu, (hd u hu).deriv]
  have hdf (u : ℝ) (hu : u ∈ Ico uc 0) : HasDerivAt χ (S.A u (V u)) u := by
    simpa only [q, π, max_eq_right hu.1] using hd u hu.2
  refine ⟨χ, hc, by simp [χ], hdf, ?_, ?_⟩
  · intro u hu
    simp only [gaugeFields, (hdf u hu).deriv, sub_self]
  · intro v
    rw [gaugeFields_a]
    simp [χ]

/-- [internal] Residual gauges preserve outgoing normalized-scalar
variation exactly, on every row and every subinterval. -/
theorem outgoing_variation_gauge (e : ℝ) (S : Fields) (χ : ℝ → ℝ) (u a b : ℝ) :
    eVariationOn ((gaugeFields e S χ).a u) (Icc a b) =
      eVariationOn (S.a u) (Icc a b) := by
  have he : (gaugeFields e S χ).a u = fun v => Complex.exp (I * e * χ u) * S.a u v :=
    funext (gaugeFields_a e S χ u)
  rw [he]
  exact Calculus.outgoing_variation_gauge e χ S.a u a b

/-- [internal] Residual gauges preserve outgoing absolute continuity.
No differentiability of the row datum is assumed pointwise. -/
theorem outgoing_ac_gauge {χ : ℝ → ℝ} {u a b : ℝ}
    (hac : AbsolutelyContinuousOnInterval (S.a u) a b) :
    AbsolutelyContinuousOnInterval ((gaugeFields e S χ).a u) a b := by
  have he : (gaugeFields e S χ).a u = fun v => Complex.exp (I * e * χ u) * S.a u v :=
    funext (gaugeFields_a e S χ u)
  rw [he]
  simpa only [smul_eq_mul] using hac.const_smul (Complex.exp (I * e * χ u))

/-- [internal] Along a frontier, the comparison-gauge trace is the
original parallel trace times its initial unit phase. This local FTC
uses a pointwise gauge derivative and a continuous original potential. -/
theorem frontier_parallel_eq_of_derivative (hS : IsSolution e S D)
    {χ V : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hV : ContinuousOn V (Icc s t))
    (hmem : ∀ u ∈ Icc s t, (u, V u) ∈ D)
    (hχ : ∀ u ∈ Icc s t, HasDerivAt χ (S.A u (V u)) u) :
    (gaugeFields e S χ).a t (V t) =
      Complex.exp (I * e * χ s) * curveParallel e S S.a id V s t := by
  have cq : ContinuousOn (fun u => S.A u (V u)) (Icc s t) :=
    hS.cont_A.comp (continuousOn_id.prodMk hV) hmem
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hχ u (by simpa only [uIcc_of_le hst] using hu))
    (cq.intervalIntegrable_of_Icc hst)
  rw [gaugeFields_a, curveParallel_def]
  simp only [deriv_id, id_eq, mul_one]
  rw [hi, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- [internal]
Finite complete frontier covariant variation, supplied by internal project record
in the original gauge, gives a finite complex limit in the comparison
gauge. No convergence of the gauge phase or subtraction of a scalar
constant is assumed (`charged_SF_new_version.tex:L1419–1421`). -/
theorem frontier_normalized_scalar_limit_of_density (hS : IsSolution e S D)
    {uc : ℝ} (huc : uc < 0) {χ V : ℝ → ℝ}
    (hV : ContinuousOn V (Ico uc 0))
    (hmem : ∀ u ∈ Ico uc 0, (u, V u) ∈ D)
    (hχ : ∀ u ∈ Ico uc 0, HasDerivAt χ (S.A u (V u)) u)
    (hdensity : BoundedVariationOn (curveParallel e S S.a id V uc) (Ico uc 0)) :
    ∃ c : ℂ, Tendsto (fun u => (gaugeFields e S χ).a u (V u))
      (𝓝[<] 0) (𝓝 c) := by
  have heq : EqOn (fun u => (gaugeFields e S χ).a u (V u))
      (fun u => Complex.exp (I * e * χ uc) * curveParallel e S S.a id V uc u)
      (Ico uc 0) := by
    intro u hu
    have hs : Icc uc u ⊆ Ico uc 0 := fun x hx => ⟨hx.1, hx.2.trans_lt hu.2⟩
    exact frontier_parallel_eq_of_derivative hS hu.1 (hV.mono hs)
      (fun x hx => hmem x (hs hx)) (fun x hx => hχ x (hs hx))
  have hb : BoundedVariationOn (fun u => (gaugeFields e S χ).a u (V u))
      (Ico uc 0) := by
    change eVariationOn _ _ ≠ ⊤
    rw [eVariationOn.eq_of_eqOn heq,
      Calculus.eVariationOn_unit_mul _
        (by simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im])]
    exact hdensity
  obtain ⟨c, hc⟩ := hb.exists_tendsto_left 0
  have hi : Ico uc (0 : ℝ) ∩ Iio 0 = Ico uc 0 :=
    inter_eq_left.mpr (fun _ hx => hx.2)
  rw [hi, nhdsWithin_Ico_eq_nhdsLT huc] at hc
  exact ⟨c, hc⟩

/-- [internal]
The original outgoing-variation decay and uniform normalized-field
decay extend the finite comparison-gauge frontier limit to both scalar
fields, uniformly on each exterior row (`charged_SF_new_version.tex:L1421–1424`).
The common complex constant is retained. All density inputs concern
the original gauge. -/
theorem uniform_common_scalar_limit_of_density {ui uc : ℝ}
    (hS : IsSolution e S (origDomain ui)) (huc : uc < 0) {χ V : ℝ → ℝ}
    (hV : ContinuousOn V (Ico uc 0))
    (hmem : ∀ u ∈ Ico uc 0, (u, V u) ∈ origDomain ui)
    (hχ : ∀ u ∈ Ico uc 0, HasDerivAt χ (S.A u (V u)) u)
    (hfrontier : BoundedVariationOn (curveParallel e S S.a id V uc) (Ico uc 0))
    (hvariation : Tendsto (fun u => (eVariationOn (S.a u) (Icc (V u) 0)).toReal)
      (𝓝[<] 0) (𝓝 0))
    (hfield : ∀ ε > 0, ∀ᶠ u in 𝓝[<] (0 : ℝ),
      ∀ v ∈ Icc (V u) 0, ‖S.theta u v / (S.lam u v : ℂ)‖ < ε) :
    ∃ c : ℂ,
      Tendsto (fun u => (gaugeFields e S χ).a u (V u)) (𝓝[<] 0) (𝓝 c) ∧
      ∀ ε > 0, ∀ᶠ u in 𝓝[<] (0 : ℝ), ∀ v ∈ Icc (V u) 0,
        ‖(gaugeFields e S χ).a u v - c‖ < ε ∧
        ‖(gaugeFields e S χ).phi u v - c‖ < ε := by
  obtain ⟨c, hc⟩ := frontier_normalized_scalar_limit_of_density
    hS huc hV hmem hχ hfrontier
  refine ⟨c, hc, ?_⟩
  intro ε hε
  have he : 0 < ε / 3 := by positivity
  filter_upwards [Ioo_mem_nhdsLT huc,
    hvariation.eventually (Iio_mem_nhds he),
    hc.eventually (Metric.ball_mem_nhds c he), hfield (ε / 3) he]
      with u hu hvar hlim hsmall
  have hm := hmem u ⟨hu.1.le, hu.2⟩
  have hs : outSeg u (V u) 0 ⊆ origDomain ui :=
    (outSeg_subset_origDomain_iff hm.2.2.2).2 ⟨hm.1, hm.2.1, hm.2.2.1, le_rfl⟩
  have hac := (hS.ac_out u (V u) 0 hm.2.2.2 hs).2.2.2.2
  have hga : AbsolutelyContinuousOnInterval ((gaugeFields e S χ).a u) (V u) 0 :=
    outgoing_ac_gauge hac
  have hb := hga.boundedVariationOn_Icc hm.2.2.2
  intro v hv
  have hd := hb.dist_le hv ⟨le_rfl, hm.2.2.2⟩
  rw [dist_eq_norm, outgoing_variation_gauge] at hd
  have ht : ‖(gaugeFields e S χ).a u v - c‖ < 2 * (ε / 3) := by
    have htri := norm_sub_le_norm_sub_add_norm_sub ((gaugeFields e S χ).a u v)
      ((gaugeFields e S χ).a u (V u)) c
    rw [dist_eq_norm] at hlim
    linarith only [htri, hd, hvar, hlim]
  have hdiff : ‖(gaugeFields e S χ).phi u v - (gaugeFields e S χ).a u v‖ =
      ‖S.theta u v / (S.lam u v : ℂ)‖ := by
    rw [gaugeFields_a]
    change ‖Complex.exp (I * e * χ u) * S.phi u v -
      Complex.exp (I * e * χ u) * S.a u v‖ = _
    rw [← mul_sub, norm_mul]
    simp [Fields.a, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  refine ⟨by linarith only [ht, hε], ?_⟩
  have htri := norm_sub_le_norm_sub_add_norm_sub ((gaugeFields e S χ).phi u v)
    ((gaugeFields e S χ).a u v) c
  rw [hdiff] at htri
  linarith only [htri, ht, hsmall v hv]

end EmcsfAcExtension.Global.Exterior
