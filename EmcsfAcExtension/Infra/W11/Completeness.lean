module

public import EmcsfAcExtension.Infra.W11.Distance

/-!
# Completeness of the representative interval W¹¹ distance

The endpoint values converge in `ℂ` and the derivatives converge in `L¹`.
Integrating their limits constructs the AC limit. The variation identity then
upgrades the derivative convergence to the representative distance and uniform
convergence, as required at `charged_SF_new_version.tex:L6450–L6459`.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace EmcsfAcExtension.W11

/-- The variation distance of AC curves is the L¹ distance of their derivatives.
The equality has no constants and is uniform in both curves and the interval. -/
theorem variation_sub_eq_integral {a b : ℝ} {f g : ℝ → ℂ} (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    (eVariationOn (f - g) (Icc a b)).toReal =
      ∫ x in a..b, ‖deriv f x - deriv g x‖ := by
  rw [(hf.sub hg).toReal_eVariationOn_eq_integral_norm_deriv hab]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hf.ae_differentiableAt_of_mem_uIcc,
    hg.ae_differentiableAt_of_mem_uIcc] with x hfx hgx hx
  rw [((hfx (uIoc_subset_uIcc hx)).hasDerivAt.sub
    (hgx (uIoc_subset_uIcc hx)).hasDerivAt).deriv]

private theorem norm_l1_sub {a b : ℝ} {g h : ℝ → ℂ} (hab : a ≤ b)
    (hg : Integrable g (volume.restrict (Ioc a b)))
    (hh : Integrable h (volume.restrict (Ioc a b))) :
    ‖hg.toL1 g - hh.toL1 h‖ = ∫ x in a..b, ‖g x - h x‖ := by
  rw [← Integrable.toL1_sub, L1.norm_of_fun_eq_integral_norm,
    intervalIntegral.integral_of_le hab]
  rfl

/-- A sequence Cauchy in the representative interval distance has an AC limit in
that distance, and converges uniformly. No bound on the sequence is assumed.
All coefficients in the norm and uniform estimate are the universal constant one. -/
theorem exists_ac_limit_of_cauchy {a b : ℝ} {F : ℕ → ℝ → ℂ} (hab : a ≤ b)
    (hF : ∀ n, AbsolutelyContinuousOnInterval (F n) a b)
    (hC : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      intervalDist a b (F n) (F m) < ε) :
    ∃ f : ℝ → ℂ, AbsolutelyContinuousOnInterval f a b ∧
      Tendsto (fun n => intervalDist a b (F n) f) atTop (𝓝 0) ∧
      TendstoUniformlyOn F f atTop (Icc a b) ∧
      Tendsto (fun n => (eVariationOn (F n - f) (Icc a b)).toReal) atTop (𝓝 0) := by
  have hD n : IntervalIntegrable (deriv (F n)) volume a b :=
    (hF n).intervalIntegrable_deriv_complex
  have hDi n : Integrable (deriv (F n)) (volume.restrict (Ioc a b)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 (hD n)
  let G : ℕ → Lp ℂ 1 (volume.restrict (Ioc a b)) := fun n => (hDi n).toL1 (deriv (F n))
  have hGeq n m : ‖G n - G m‖ = (eVariationOn (F n - F m) (Icc a b)).toReal := by
    rw [norm_l1_sub hab (hDi n) (hDi m), variation_sub_eq_integral hab (hF n) (hF m)]
  have hGC : CauchySeq G := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    refine ⟨N, fun n hn m hm => ?_⟩
    rw [dist_eq_norm, hGeq]
    exact lt_of_le_of_lt (le_add_of_nonneg_left (norm_nonneg _)) (hN n hn m hm)
  obtain ⟨gL, hgL⟩ := cauchySeq_tendsto_of_complete hGC
  let g : ℝ → ℂ := gL
  have hgi : Integrable g (volume.restrict (Ioc a b)) := L1.integrable_coeFn gL
  have hg : IntervalIntegrable g volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hgi
  have hGlim : Tendsto (fun n => ∫ x in a..b, ‖deriv (F n) x - g x‖) atTop (𝓝 0) := by
    have heq n : (∫ x in a..b, ‖deriv (F n) x - g x‖) = ‖G n - gL‖ := by
      rw [← norm_l1_sub hab (hDi n) hgi]
      change ‖G n - hgi.toL1 (gL : ℝ → ℂ)‖ = ‖G n - gL‖
      rw [Integrable.toL1_coeFn]
    simpa only [heq] using (tendsto_iff_norm_sub_tendsto_zero.1 hgL)
  have hVC : CauchySeq (fun n => F n a) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    refine ⟨N, fun n hn m hm => ?_⟩
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (le_add_of_nonneg_right ENNReal.toReal_nonneg) (hN n hn m hm)
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hVC
  let f : ℝ → ℂ := fun x => z + ∫ t in a..x, g t
  have hfa : f a = z := by simp [f]
  have hfac : AbsolutelyContinuousOnInterval f a b :=
    ((LipschitzWith.const z).lipschitzOnWith.absolutelyContinuousOnInterval).fun_add
      (hg.absolutelyContinuousOnInterval_intervalIntegral_normed left_mem_uIcc)
  have hvar n : eVariationOn (F n - f) (Icc a b) =
      ENNReal.ofReal (∫ x in a..b, ‖deriv (F n) x - g x‖) := by
    apply ((hD n).sub hg).eVariationOn_eq_integral_norm_of_eq_integral hab
    intro x hx
    have hsub : uIcc a x ⊆ uIcc a b := by
      rw [uIcc_of_le hx.1, uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl hx.2
    rw [Pi.sub_apply, Pi.sub_apply, hfa,
      intervalIntegral.integral_sub ((hD n).mono_set hsub) (hg.mono_set hsub),
      ((hF n).mono hsub).integral_deriv_eq_sub_complex]
    dsimp only [f]
    abel
  have hvlim : Tendsto (fun n => (eVariationOn (F n - f) (Icc a b)).toReal)
      atTop (𝓝 0) := by
    have heq n : (eVariationOn (F n - f) (Icc a b)).toReal =
        ∫ x in a..b, ‖deriv (F n) x - g x‖ := by
      rw [hvar, ENNReal.toReal_ofReal
        (intervalIntegral.integral_nonneg hab (fun _ _ => norm_nonneg _))]
    simpa only [heq] using hGlim
  have hlim : Tendsto (fun n => intervalDist a b (F n) f) atTop (𝓝 0) := by
    simpa only [intervalDist_def, hfa, zero_add] using!
      (tendsto_iff_norm_sub_tendsto_zero.1 hz).add hvlim
  refine ⟨f, hfac, hlim, ?_, hvlim⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(tendsto_order.1 hlim).2 ε hε] with n hn x hx
  rw [dist_comm, dist_eq_norm]
  exact (norm_sub_le_intervalDist ((hF n).boundedVariationOn_Icc hab)
    (hfac.boundedVariationOn_Icc hab) hx).trans_lt hn

end EmcsfAcExtension.W11
