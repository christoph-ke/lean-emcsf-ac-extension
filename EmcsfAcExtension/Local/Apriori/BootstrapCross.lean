module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.BootstrapCrossPointwise
import EmcsfAcExtension.Local.Apriori.BootstrapVariationAux
import EmcsfAcExtension.Local.Apriori.GeometryTVCross
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Apriori.AreaJAux
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Opposite-family normalized scalar variations

The small scalar ratios multiply the cross expansion variation, and the
electric drift integrates to the square of the charged scale. This supplies
the ordinary opposite-family clauses of `SmoothBounds` without a uniform
initial derivative assumption.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

/-- Both opposite-family normalized scalar variations have a universal
finite bound. The positive thresholds and constant precede every datum,
depend only on the fixed box, and are uniform in higher initial derivatives.
The estimate uses the ordinary incoming partial of `a` and outgoing partial
of `b`, with the gauge term retained. -/
theorem normalized_cross_variations : ∃ ε₀ δ₀ C : ℝ,
    0 < ε₀ ∧ 0 < δ₀ ∧ 0 < C ∧
    ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e T ε M S h → ε ≤ ε₀ → |e| * (T / 2) * M ≤ δ₀ →
      (∀ v ∈ Icc 0 T, eVariationOn (fun u => S.a u v) (Icc 0 v) ≤ ENNReal.ofReal C) ∧
      (∀ u ∈ Icc 0 T, eVariationOn (S.b u) (Icc u T) ≤ ENNReal.ofReal C) := by
  obtain ⟨ε₁, δ₁, Cx, hε₁, hδ₁, hCx, hcross⟩ := cross_expansion_variation
  obtain ⟨Ce, hCe, hpoint⟩ := normalized_cross_partial_bounds
  refine ⟨min ε₁ 1, min δ₁ 1, 16 * Cx + 4 * Ce,
    lt_min hε₁ (by norm_num), lt_min hδ₁ (by norm_num), by positivity, ?_⟩
  intro e T ε M S h hset hε hδ
  have hε0 := hset.eps_nonneg
  have he1 := hε.trans (min_le_right _ _)
  have hd0 : 0 ≤ |e| * (T / 2) * M := by have := hset.pos; have := hset.one_le_M; positivity
  have hd2 : (|e| * (T / 2) * M) ^ 2 ≤ 1 := by
    nlinarith only [hd0, hδ.trans (min_le_right δ₁ 1)]
  have hscale : Ce * e ^ 2 * M ^ 2 * ε * T ^ 2 ≤ 4 * Ce * ε := by
    have hi := mul_le_mul_of_nonneg_right hd2 (show 0 ≤ 4 * Ce * ε by positivity)
    simp only [mul_pow, sq_abs] at hi
    nlinarith only [hi]
  have hε3 : ε ^ 3 ≤ 1 := by
    calc
      ε ^ 3 ≤ (1 : ℝ) ^ 3 := pow_le_pow_left₀ hε0 he1 3
      _ = 1 := by norm_num
  have hfinal {X : ℝ} (hX : X ≤ 16 * ε * (Cx * ε ^ 2) + 4 * Ce * ε) :
      X ≤ 16 * Cx + 4 * Ce := by
    have h1 := mul_le_mul_of_nonneg_left hε3 (show 0 ≤ 16 * Cx by positivity)
    have h2 := mul_le_mul_of_nonneg_left he1 (show 0 ≤ 4 * Ce by positivity)
    nlinarith only [hX, h1, h2]
  have hc := hcross e T ε M S h hset (hε.trans (min_le_left _ _))
    (hδ.trans (min_le_left _ _))
  have hB0 : 0 ≤ Ce * e ^ 2 * M ^ 2 * ε * T := by have := hset.pos; positivity
  constructor
  · intro v hv
    have hs : MapsTo (fun x : ℝ => (x, v)) (Icc 0 v) (triangle 0 T) :=
      fun x hx => ⟨hx.1, hx.2, hv.2⟩
    have ca : ContinuousOn (fun x => pdU (triangle 0 T) S.a x v) (Icc 0 v) :=
      (continuousOn_pdU hset.c1.c1_a (uniqueDiffOn_triangle hset.pos)).comp
        (continuous_id.prodMk continuous_const).continuousOn hs
    have cl : ContinuousOn (fun x => pdU (triangle 0 T) S.lam x v) (Icc 0 v) :=
      (continuousOn_pdU hset.c1.c1_lam (uniqueDiffOn_triangle hset.pos)).comp
        (continuous_id.prodMk continuous_const).continuousOn hs
    have ia := (ca.intervalIntegrable_of_Icc (μ := volume) hv.1).norm
    have il := (cl.intervalIntegrable_of_Icc (μ := volume) hv.1).norm
    have hcV := (hc 0 v le_rfl hv.1 hv.2).2
    rw [variation_in_eq_integral_partial hset.c1.c1_lam le_rfl hv.1 hv.2] at hcV
    have hlam : (∫ x in 0..v, ‖pdU (triangle 0 T) S.lam x v‖) ≤ Cx * ε ^ 2 :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hcV
    have hbound : (fun x => ‖pdU (triangle 0 T) S.a x v‖) ≤ᵐ[volume.restrict (Icc 0 v)]
        (fun x => 16 * ε * ‖pdU (triangle 0 T) S.lam x v‖ +
          Ce * e ^ 2 * M ^ 2 * ε * T) := by
      have hn : ∀ᵐ x : ℝ, x ≠ v := by simp [ae_iff, measure_singleton]
      filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hn] with x hx hne
      have hp := hs hx
      have hb := (hpoint e T ε M S h hset x v hp (lt_of_le_of_ne hx.2 hne)).1
      have hr : S.r x v ≤ T := (Area.radius_bounds hset hx.1 hx.2 hv.2).2.trans
        (by linarith only [hx.1, hv.2])
      rw [Real.norm_eq_abs]
      exact hb.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hr (by positivity)))
    have hi := intervalIntegral.integral_mono_ae_restrict hv.1 ia
      ((il.const_mul (16 * ε)).add intervalIntegrable_const) hbound
    rw [intervalIntegral.integral_add (il.const_mul (16 * ε)) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
      sub_zero, smul_eq_mul] at hi
    have hL := mul_le_mul_of_nonneg_left hlam (show 0 ≤ 16 * ε by positivity)
    have hE := (mul_le_mul_of_nonneg_right hv.2 hB0).trans (by
      convert hscale using 1
      ring)
    rw [variation_in_eq_integral_partial hset.c1.c1_a le_rfl hv.1 hv.2]
    apply ENNReal.ofReal_le_ofReal
    exact hfinal (by linarith only [hi, hL, hE])
  · intro u hu
    have hs : MapsTo (fun x : ℝ => (u, x)) (Icc u T) (triangle 0 T) :=
      fun x hx => ⟨hu.1, hx.1, hx.2⟩
    have cb : ContinuousOn (fun x => pdV (triangle 0 T) S.b u x) (Icc u T) :=
      (continuousOn_pdV hset.c1.c1_b (uniqueDiffOn_triangle hset.pos)).comp
        (continuous_const.prodMk continuous_id).continuousOn hs
    have cn : ContinuousOn (pdV (triangle 0 T) S.nu u) (Icc u T) :=
      (continuousOn_pdV hset.c1.c1_nu (uniqueDiffOn_triangle hset.pos)).comp
        (continuous_const.prodMk continuous_id).continuousOn hs
    have ib := (cb.intervalIntegrable_of_Icc (μ := volume) hu.2).norm
    have inorm := (cn.intervalIntegrable_of_Icc (μ := volume) hu.2).norm
    have hcV := (hc u T hu.1 hu.2 le_rfl).1
    rw [variation_out_eq_integral_partial hset.c1.c1_nu hu.1 hu.2 le_rfl] at hcV
    have hnu : (∫ x in u..T, ‖pdV (triangle 0 T) S.nu u x‖) ≤ Cx * ε ^ 2 :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hcV
    have hbound : (fun x => ‖pdV (triangle 0 T) S.b u x‖) ≤ᵐ[volume.restrict (Icc u T)]
        (fun x => 16 * ε * ‖pdV (triangle 0 T) S.nu u x‖ +
          Ce * e ^ 2 * M ^ 2 * ε * T) := by
      have hn : ∀ᵐ x : ℝ, x ≠ u := by simp [ae_iff, measure_singleton]
      filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hn] with x hx hne
      have hp := hs hx
      have hb := (hpoint e T ε M S h hset u x hp (lt_of_le_of_ne hx.1 hne.symm)).2
      have hr : S.r u x ≤ T := (Area.radius_bounds hset hu.1 hx.1 hx.2).2.trans
        (by linarith only [hu.1, hx.2])
      rw [Real.norm_eq_abs]
      exact hb.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hr (by positivity)))
    have hi := intervalIntegral.integral_mono_ae_restrict hu.2 ib
      ((inorm.const_mul (16 * ε)).add intervalIntegrable_const) hbound
    rw [intervalIntegral.integral_add (inorm.const_mul (16 * ε)) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at hi
    have hL := mul_le_mul_of_nonneg_left hnu (show 0 ≤ 16 * ε by positivity)
    have hE := (mul_le_mul_of_nonneg_right (show T - u ≤ T by linarith only [hu.1]) hB0).trans
      (by convert hscale using 1; ring)
    rw [variation_out_eq_integral_partial hset.c1.c1_b hu.1 hu.2 le_rfl]
    apply ENNReal.ofReal_le_ofReal
    exact hfinal (by linarith only [hi, hL, hE])

end EmcsfAcExtension.Local
