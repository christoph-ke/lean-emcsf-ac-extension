module

public import EmcsfAcExtension.Infra.OrderedKernel

/-! # The four-variable ordered area kernel

The two inner variables retain their order. Integrating the lower outer
endpoint first reduces this kernel to the landed `orderedKernelDensity`.
All integrals are nonnegative, so finiteness is a conclusion.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The positive ordered area kernel before either outer integration.
The numerator has the natural primitive order `u ≤ s ≤ w ≤ v`. -/
@[expose] noncomputable def stabOrderedKernel (p : ℝ) (K J : ℝ → ℝ≥0∞) (u v : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((v - u) ^ (-p - 2)) * ∫⁻ w in Icc u v, ∫⁻ s in Icc u w,
    ENNReal.ofReal ((w - s) ^ p) * K s * J w

private theorem measurable_ordered_inner (p v : ℝ) {K J : ℝ → ℝ≥0∞}
    (hK : Measurable K) (hJ : Measurable J) :
    Measurable (fun s => ∫⁻ w in Icc s v, ENNReal.ofReal ((w - s) ^ p) * K s * J w) := by
  have hset : MeasurableSet {q : ℝ × ℝ | q.1 ≤ q.2 ∧ q.2 ≤ v} :=
    (measurableSet_le measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have hbase : Measurable (fun q : ℝ × ℝ =>
      ENNReal.ofReal ((q.2 - q.1) ^ p) * K q.1 * J q.2) := by fun_prop
  have hm := hbase.indicator hset
  convert hm.lintegral_prod_right' (ν := (volume : Measure ℝ)) using 1
  funext s
  rw [← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro w
  rfl

/-- Swapping the two inner ordered variables preserves the positive kernel.
No finiteness assumption on either input is needed. -/
theorem stab_ordered_inner_swap {p u v : ℝ} {K J : ℝ → ℝ≥0∞}
    (hK : Measurable K) (hJ : Measurable J) :
    (∫⁻ w in Icc u v, ∫⁻ s in Icc u w,
      ENNReal.ofReal ((w - s) ^ p) * K s * J w) =
    ∫⁻ s in Icc u v, ∫⁻ w in Icc s v,
      ENNReal.ofReal ((w - s) ^ p) * K s * J w := by
  exact (lintegral_lintegral_swap_triangle
    (F := fun q => ENNReal.ofReal ((q.2 - q.1) ^ p) * K q.1 * J q.2)
    (a := u) (b := v) (by fun_prop)).symm

/-- The landed density agrees with its local triangular integral when
`0 ≤ v ≤ T`. The outer truncation introduces no additional terms. -/
theorem stab_ordered_density_eq_triangle {p T v : ℝ} {K J : ℝ → ℝ≥0∞}
    (hK : Measurable K) (hJ : Measurable J) (_hv : 0 ≤ v) (hvT : v ≤ T) :
    orderedKernelDensity p T K J univ v =
      ∫⁻ s in Icc 0 v, ∫⁻ w in Icc s v,
        K s * J w * ENNReal.ofReal (orderedPowerKernel p s w v) := by
  let F := fun q : ℝ × ℝ => K q.1 * J q.2 *
    ENNReal.ofReal (orderedPowerKernel p q.1 q.2 v)
  have hF : Measurable F := by unfold F orderedPowerKernel; fun_prop
  have hsub : triangle 0 v ⊆ Icc 0 T ×ˢ Icc 0 T := by
    intro q hq
    exact ⟨⟨hq.1, hq.2.1.trans (hq.2.2.trans hvT)⟩,
      ⟨hq.1.trans hq.2.1, hq.2.2.trans hvT⟩⟩
  unfold orderedKernelDensity
  simp only [inter_univ]
  change (∫⁻ s in Icc 0 T, ∫⁻ w in Icc 0 T, (triangle 0 v).indicator F (s, w)) = _
  rw [← lintegral_prod _ ((hF.indicator (measurableSet_triangle 0 v)).aemeasurable),
    Measure.prod_restrict, lintegral_indicator (measurableSet_triangle 0 v),
    Measure.restrict_restrict (measurableSet_triangle 0 v), inter_eq_left.mpr hsub]
  exact lintegral_triangle_eq_lintegral_lintegral hF

private theorem lintegral_lower_outer_power_le {p s v : ℝ} (hp : 0 ≤ p)
    (hs : 0 ≤ s) (hsv : s < v) :
    (∫⁻ u in Icc 0 s, ENNReal.ofReal ((v - u) ^ (-p - 2))) ≤
      ENNReal.ofReal ((v - s) ^ (-(1 + p))) := by
  have hp' : -1 < p := lt_of_lt_of_le (by norm_num) hp
  have hc : ContinuousOn (fun u : ℝ => (v - u) ^ (-p - 2)) (uIcc 0 s) := by
    apply (continuousOn_const.sub continuousOn_id).rpow_const
    intro u hu
    rw [uIcc_of_le hs] at hu
    exact Or.inl (sub_pos.mpr (hu.2.trans_lt hsv)).ne'
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hs).1
    (hc.intervalIntegrable (μ := volume))
  have hn : 0 ≤ᵐ[volume.restrict (Icc 0 s)] (fun u : ℝ => (v - u) ^ (-p - 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact Real.rpow_nonneg (sub_nonneg.mpr (hu.2.trans hsv.le)) _
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hs]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_reflected_rpow_eq hp' hs hsv]
  have htail : 0 ≤ (v - 0) ^ (-(p + 1)) :=
    Real.rpow_nonneg (sub_nonneg.mpr (hs.trans hsv.le)) _
  have hhead : 0 ≤ (v - s) ^ (-(p + 1)) := Real.rpow_nonneg (sub_nonneg.mpr hsv.le) _
  calc
    _ ≤ (v - s) ^ (-(p + 1)) / (p + 1) :=
      div_le_div_of_nonneg_right (sub_le_self _ htail) (by linarith only [hp])
    _ ≤ (v - s) ^ (-(p + 1)) := div_le_self hhead (by linarith only [hp])
    _ = _ := by rw [add_comm p 1]

/-- Integrating the lower outer endpoint of the full kernel is bounded by
the landed ordered density. The exact discarded factor `1/(1+p)` is at
most one for `p ≥ 0`; the bound is uniform in all endpoints and inputs. -/
theorem stab_ordered_kernel_slice_le {p T v : ℝ} {K J : ℝ → ℝ≥0∞}
    (hp : 0 ≤ p) (hK : Measurable K) (hJ : Measurable J)
    (hv : 0 ≤ v) (hvT : v ≤ T) :
    (∫⁻ u in Icc 0 v, stabOrderedKernel p K J u v) ≤
      orderedKernelDensity p T K J univ v := by
  let H := fun s => ∫⁻ w in Icc s v, ENNReal.ofReal ((w - s) ^ p) * K s * J w
  have hH : Measurable H := measurable_ordered_inner p v hK hJ
  have hweight : Measurable (fun u : ℝ => ENNReal.ofReal ((v - u) ^ (-p - 2))) := by
    fun_prop
  have hswap := lintegral_lintegral_swap_triangle (a := 0) (b := v)
    (F := fun q => ENNReal.ofReal ((v - q.1) ^ (-p - 2)) * H q.2)
    (by fun_prop)
  have heq : (∫⁻ u in Icc 0 v, stabOrderedKernel p K J u v) =
      ∫⁻ s in Icc 0 v, ∫⁻ u in Icc 0 s,
        ENNReal.ofReal ((v - u) ^ (-p - 2)) * H s := by
    rw [← hswap]
    apply lintegral_congr
    intro u
    rw [stabOrderedKernel, stab_ordered_inner_swap hK hJ]
    dsimp only [Prod.fst, Prod.snd]
    exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
  rw [heq, stab_ordered_density_eq_triangle hK hJ hv hvT]
  have hne : ∀ᵐ s : ℝ, s ≠ v := by simp [ae_iff, measure_singleton]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with s hs hne
  have hsv : s < v := lt_of_le_of_ne hs.2 hne
  calc
    _ = (∫⁻ u in Icc 0 s, ENNReal.ofReal ((v - u) ^ (-p - 2))) * H s :=
      lintegral_mul_const'' _ hweight.aemeasurable
    _ ≤ ENNReal.ofReal ((v - s) ^ (-(1 + p))) * H s :=
      mul_le_mul' (lintegral_lower_outer_power_le hp hs.1 hsv) le_rfl
    _ = ∫⁻ w in Icc s v, K s * J w *
        ENNReal.ofReal (orderedPowerKernel p s w v) := by
      dsimp only [H]
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro w
      have hpow : (v - s) ^ (-(1 + p)) * (w - s) ^ p =
          orderedPowerKernel p s w v := by
        rw [orderedPowerKernel, Real.rpow_neg (sub_nonneg.mpr hsv.le)]
        ring
      calc
        _ = (ENNReal.ofReal ((v - s) ^ (-(1 + p))) *
            ENNReal.ofReal ((w - s) ^ p)) * K s * J w := by ac_rfl
        _ = _ := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (sub_nonneg.mpr hsv.le) _), hpow]
          ac_rfl

/-- The complete ordered area kernel has mass at most `(1/p) ‖K‖₁ ‖J‖₁`.
The constant depends only on `p > 0`, uniformly in the interval and inputs.
Infinite input masses are permitted; no source integrability is assumed. -/
theorem stab_ordered_kernel_area {p T : ℝ} {K J : ℝ → ℝ≥0∞}
    (hp : 0 < p) (hK : Measurable K) (hJ : Measurable J) :
    (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, stabOrderedKernel p K J u v) ≤
      ENNReal.ofReal (1 / p) * (∫⁻ s in Icc 0 T, K s) * (∫⁻ w in Icc 0 T, J w) := by
  apply (setLIntegral_mono' measurableSet_Icc
    (fun v hv => stab_ordered_kernel_slice_le hp.le hK hJ hv.1 hv.2)).trans
  exact lintegral_orderedKernelDensity_univ_le hp hK.aemeasurable hJ.aemeasurable

end EmcsfAcExtension.Local
