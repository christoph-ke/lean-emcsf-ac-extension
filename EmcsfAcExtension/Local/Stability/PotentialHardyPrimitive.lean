module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.MomentsSections
import EmcsfAcExtension.Infra.Mixed.MomentKernel

/-! # A positive primitive Hardy estimate on a classical radius

The exact factor 1/2 applies to any continuous positive forcing. This
form also handles charge differences before a supremum loses the axis
vanishing of the scalar ratios.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- A full axis-to-point primitive with forcing `C λ r f` has weighted
Hardy cost `(C/2) ∫ (λ/r) f`. The coefficient `1/2` is exact, uniform in
all field parameters, the section and forcing, with no finiteness premise.
-/
theorem stab_charge_primitive_hardy_of_c1_bound
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {u v C : ℝ}
    {f q : ℝ → ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T)
    (hC : 0 ≤ C) (hf : ContinuousOn f (Icc u v)) (hf0 : ∀ s ∈ Icc u v, 0 ≤ f s)
    (hprimitive : ∀ t ∈ Icc u v,
      |q t| ≤ C * ∫ s in u..t, S.lam u s * S.r u s * f s) :
    (∫⁻ t in Icc u v, ENNReal.ofReal (S.lam u t * |q t| / S.r u t ^ 3)) ≤
      ENNReal.ofReal (C / 2) * ∫⁻ t in Icc u v, ENNReal.ofReal (S.lam u t / S.r u t * f t) := by
  classical
  let R := (Icc u v).indicator (S.r u)
  let W := (Icc u v).indicator (S.lam u)
  let X := (Icc u v).indicator f
  let F := fun s => ENNReal.ofReal (W s / R s * X s)
  let Z := fun t => ENNReal.ofReal (|q t| / S.r u t ^ 2)
  have hmap : MapsTo (fun s : ℝ => (u, s)) (Icc u v) (triangle 0 T) :=
    fun s hs => ⟨hu, hs.1, hs.2.trans hvT⟩
  have cr : ContinuousOn (S.r u) (Icc u v) := hset.c1.c1_r.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cl : ContinuousOn (S.lam u) (Icc u v) := hset.c1.c1_lam.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cx : ContinuousOn f (Icc u v) := hf
  have hR : Measurable R := by
    dsimp only [R]
    rw [← Set.piecewise_eq_indicator]
    exact cr.measurable_piecewise continuousOn_const measurableSet_Icc
  have hW : Measurable W := by
    dsimp only [W]
    rw [← Set.piecewise_eq_indicator]
    exact cl.measurable_piecewise continuousOn_const measurableSet_Icc
  have hX : Measurable X := by
    dsimp only [X]
    rw [← Set.piecewise_eq_indicator]
    exact cx.measurable_piecewise continuousOn_const measurableSet_Icc
  have hF : Measurable F := ENNReal.measurable_ofReal.comp ((hW.div hR).mul hX)
  have hlocal (t : ℝ) (ht : t ∈ Icc u v) :
      R t = S.r u t ∧ W t = S.lam u t ∧ X t = f t := by
    simp only [R, W, X, indicator_of_mem ht, and_self]
  have hr0 (t : ℝ) (ht : t ∈ Icc u v) : 0 ≤ S.r u t := by
    rcases ht.1.eq_or_lt with rfl | hut
    · rw [(hset.c1.axis u ⟨hu, le_rfl, huv.trans hvT⟩).1]
    · exact (hset.c1.r_pos (u, t) (hmap ht) hut).le
  have hE : 0 ≤ C := hC
  have hr : AbsolutelyContinuousOnInterval (S.r u) u v := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le huv]
    exact hset.c1.c1_r.comp (contDiffOn_const.prodMk contDiffOn_id) hmap
  have hm : MonotoneOn (S.r u) (Icc u v) := by
    intro s hs t ht hst
    exact (stab_radius_section_order hset hu hs.1 hst (ht.2.trans hvT)).1
  have hd : ∀ᵐ t ∂volume.restrict (Icc u v), deriv (S.r u) t = W t := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hdt := hasDerivWithinAt_uncurry_triangle_v hset.c1.c1_r
      (hmap ⟨ht.1.le, ht.2.le⟩)
    change HasDerivWithinAt (S.r u) (pdV (triangle 0 T) S.r u t) (Icc u T) t at hdt
    rw [(hset.c1.eq_v (u, t) (hmap ⟨ht.1.le, ht.2.le⟩) ht.1).1] at hdt
    rw [(hlocal t ⟨ht.1.le, ht.2.le⟩).2.1]
    exact (hdt.hasDerivAt (Icc_mem_nhds ht.1 (ht.2.trans_le hvT))).deriv
  have hZ : ∀ t ∈ Icc u v, Z t ≤ ENNReal.ofReal (C) *
      ∫⁻ s in Icc u t, ENNReal.ofReal ((S.r u s / S.r u t) ^ (2 : ℝ)) * F s := by
    intro t ht
    rcases ht.1.eq_or_lt with rfl | hut
    · dsimp only [Z]
      rw [(hset.c1.axis u ⟨hu, le_rfl, huv.trans hvT⟩).1]
      norm_num
    have hrt := hset.c1.r_pos (u, t) (hmap ht) hut
    have cN : ContinuousOn (fun s => S.lam u s * S.r u s *
        f s) (Icc u v) := by
      simpa only [Pi.mul_apply] using! (cl.mul cr).mul cx
    have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hut.le).mp
      ((cN.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc (μ := volume) hut.le)
    have hn : ∀ᵐ s ∂volume.restrict (Icc u t), 0 ≤
        S.lam u s * S.r u s * f s / S.r u t ^ 2 := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact div_nonneg (mul_nonneg
        (mul_nonneg (hset.c1.lam_pos (u, s) (hmap ⟨hs.1, hs.2.trans ht.2⟩)).le
          (hr0 s ⟨hs.1, hs.2.trans ht.2⟩)) (hf0 s ⟨hs.1, hs.2.trans ht.2⟩)) (sq_nonneg _)
    have heq : (∫⁻ s in Icc u t, ENNReal.ofReal ((S.r u s / S.r u t) ^ (2 : ℝ)) * F s) =
        ENNReal.ofReal ((∫ s in u..t, S.lam u s * S.r u s *
          f s) / S.r u t ^ 2) := by
      calc
        _ = ∫⁻ s in Icc u t, ENNReal.ofReal (S.lam u s * S.r u s *
            f s / S.r u t ^ 2) := by
          apply setLIntegral_congr_fun measurableSet_Icc
          intro s hs
          dsimp only [F]
          rw [(hlocal s ⟨hs.1, hs.2.trans ht.2⟩).1,
            (hlocal s ⟨hs.1, hs.2.trans ht.2⟩).2.1,
            (hlocal s ⟨hs.1, hs.2.trans ht.2⟩).2.2,
            Real.rpow_two, ← ENNReal.ofReal_mul (sq_nonneg _)]
          congr 1
          by_cases hrs : S.r u s = 0
          · simp only [hrs, zero_div, zero_pow (by norm_num : 2 ≠ 0), div_zero, zero_mul,
              mul_zero]
          · field_simp
        _ = _ := by
          rw [← ofReal_integral_eq_lintegral_ofReal (hi.div_const _) hn,
            integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hut.le,
            intervalIntegral.integral_div]
    rw [heq, ← ENNReal.ofReal_mul hE]
    apply ENNReal.ofReal_le_ofReal
    simpa only [mul_div_assoc] using
      div_le_div_of_nonneg_right (hprimitive t ht)
        (sq_nonneg (S.r u t))
  have hhardy := Mixed.lintegral_weighted_le_of_radial_moment
    huv (by norm_num : (0 : ℝ) < 2) hE hr hm
    (fun t ht => hset.c1.r_pos (u, t) (hmap ⟨ht.1.le, ht.2⟩) ht.1)
    hW (fun t ht => by rw [(hlocal t ht).2.1]; exact (hset.c1.lam_pos _ (hmap ht)).le)
    hF hd hZ
  have hfirst : (∫⁻ t in Icc u v, ENNReal.ofReal
      (S.lam u t * |q t| / S.r u t ^ 3)) ≤
        ENNReal.ofReal (C / 2) * ∫⁻ t in Icc u v, ENNReal.ofReal
          (S.lam u t / S.r u t * f t) := by
    convert hhardy using 1
    · apply setLIntegral_congr_fun measurableSet_Icc
      intro t ht
      dsimp only [Z]
      rw [(hlocal t ht).2.1]
      rw [← ENNReal.ofReal_mul
        (div_nonneg (hset.c1.lam_pos _ (hmap ht)).le (hr0 t ht))]
      congr 1
      ring
    · congr 1
      apply setLIntegral_congr_fun measurableSet_Icc
      intro t ht
      dsimp only [F]
      rw [(hlocal t ht).1, (hlocal t ht).2.1, (hlocal t ht).2.2]
  exact hfirst

end EmcsfAcExtension.Local
