module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.AssemblyMoments
import EmcsfAcExtension.Local.Stability.MomentsSections
import EmcsfAcExtension.Local.Calculus.C1ToSolution2
import EmcsfAcExtension.Local.Calculus.RelativeCharge
import EmcsfAcExtension.Infra.Mixed.MomentKernel

/-! # The charge Hardy integral from the regular axis

The outgoing Maxwell primitive is retained through the singular
integration in charged_SF_new_version.tex:L5494–5498 and approved internal project record (Q4).
The radial moment kernel with exponent two supplies the exact factor
`1/2` before any integrability conclusion is used.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local

variable {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}

/-- The outgoing Maxwell primitive retains the scalar oscillation under
its radial integral. Its exact coefficient one is universal, including
zero coupling; no division by charge or scalar background is used. -/
theorem stab_charge_primitive_norm_le (hset : StabSetting e T ε M A S h)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    |S.Q u v| ≤ |e| * M * ∫ s in u..v,
      S.lam u s * S.r u s * ‖S.theta u s / (S.lam u s : ℂ)‖ := by
  have hmap : MapsTo (fun s : ℝ => (u, s)) (Icc u v) (triangle 0 T) :=
    fun s hs => ⟨hu, hs.1, hs.2.trans hvT⟩
  have cl : ContinuousOn (S.lam u) (Icc u v) := hset.c1.c1_lam.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cr : ContinuousOn (S.r u) (Icc u v) := hset.c1.c1_r.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cp : ContinuousOn (S.phi u) (Icc u v) := hset.c1.c1_phi.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cx : ContinuousOn (fun s => S.theta u s / (S.lam u s : ℂ)) (Icc u v) :=
    (stab_out_ratio_c1 hset.c1).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have ci : ContinuousOn (fun s => S.lam u s * S.r u s *
      (starRingEnd ℂ (S.phi u s) * (S.theta u s / (S.lam u s : ℂ))).im) (Icc u v) := by
    simpa only [Function.comp_apply, Pi.mul_apply] using!
      (cl.mul cr).mul (Complex.continuous_im.comp_continuousOn
        ((Complex.continuous_conj.comp_continuousOn cp).mul cx))
  have cn : ContinuousOn (fun s => S.lam u s * S.r u s *
      ‖S.theta u s / (S.lam u s : ℂ)‖) (Icc u v) := by
    simpa only [Pi.mul_apply] using! (cl.mul cr).mul cx.norm
  have hbound : ∀ s ∈ Icc u v,
      |S.lam u s * S.r u s *
        (starRingEnd ℂ (S.phi u s) * (S.theta u s / (S.lam u s : ℂ))).im| ≤
      M * (S.lam u s * S.r u s * ‖S.theta u s / (S.lam u s : ℂ)‖) := by
    intro s hs
    have hr0 : 0 ≤ S.r u s := by
      rcases hs.1.eq_or_lt with rfl | hus
      · rw [(hset.c1.axis u ⟨hu, le_rfl, huv.trans hvT⟩).1]
      · exact (hset.c1.r_pos (u, s) (hmap hs) hus).le
    have hlr : 0 ≤ S.lam u s * S.r u s :=
      mul_nonneg (hset.c1.lam_pos (u, s) (hmap hs)).le hr0
    have hp := (hset.box.2 (u, s) (hmap hs)).2.2.2.2.2.2
    rw [abs_mul, abs_of_nonneg hlr]
    calc
      _ ≤ (S.lam u s * S.r u s) *
          (‖S.phi u s‖ * ‖S.theta u s / (S.lam u s : ℂ)‖) := by
        apply mul_le_mul_of_nonneg_left _ hlr
        simpa only [norm_mul, Complex.norm_conj] using
          Complex.abs_im_le_norm
            (starRingEnd ℂ (S.phi u s) * (S.theta u s / (S.lam u s : ℂ)))
      _ ≤ (S.lam u s * S.r u s) *
          (M * ‖S.theta u s / (S.lam u s : ℂ)‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hp (norm_nonneg _)) hlr
      _ = _ := by ring
  have hi := intervalIntegral.integral_mono_on huv
    ((ci.intervalIntegrable_of_Icc (μ := volume) huv).norm)
    ((cn.intervalIntegrable_of_Icc (μ := volume) huv).const_mul M) (by
      intro s hs
      simpa only [Real.norm_eq_abs] using hbound s hs)
  have hseg : outSeg u u v ⊆ triangle 0 T := by
    rintro ⟨a, b⟩ ⟨rfl, hs⟩
    exact hmap hs
  rw [Stab.oscillatory_charge_constraint (hset.c1.toIsSolution hset.pos) huv hseg,
    abs_mul, abs_neg, ← Real.norm_eq_abs]
  have hn := intervalIntegral.norm_integral_le_integral_norm huv (μ := volume)
    (f := fun s => S.lam u s * S.r u s *
      (starRingEnd ℂ (S.phi u s) * (S.theta u s / (S.lam u s : ℂ))).im)
  rw [intervalIntegral.integral_const_mul] at hi
  exact (mul_le_mul_of_nonneg_left (hn.trans hi) (abs_nonneg e)).trans_eq (by
    rw [Real.norm_eq_abs]
    ring)

/-- Classical helper for `restart-sec-bv-stability-independent#charge-radial-Hardy-bound`.
The full axis-to-point outgoing charge Hardy integral has exact coefficient
`1/2`, uniformly in every parameter and the solution. The second estimate
has universal coefficient `8/3` and uses the standing scalar moment bound.
Integrability at the axis follows from these nonnegative integral bounds.
This lemma has the classical `StabSetting` scope; it does not close the
broader characteristic-AC form of the graph node. -/
theorem Stab.charge_radial_hardy_bound (hset : StabSetting e T ε M A S h)
    (hε : ε ^ 2 ≤ 1 / 4) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    (∫⁻ t in Icc u v, ENNReal.ofReal
      (S.lam u t * |S.Q u t| / S.r u t ^ 3)) ≤
        ENNReal.ofReal (|e| * M / 2) * ∫⁻ t in Icc u v, ENNReal.ofReal
          (S.lam u t / S.r u t * ‖S.theta u t / (S.lam u t : ℂ)‖) ∧
    (∫⁻ t in Icc u v, ENNReal.ofReal
      (S.lam u t * |S.Q u t| / S.r u t ^ 3)) ≤
        ENNReal.ofReal ((8 / 3) * |e| * M) *
          ∫⁻ s in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S) s := by
  classical
  let R := (Icc u v).indicator (S.r u)
  let W := (Icc u v).indicator (S.lam u)
  let X := (Icc u v).indicator (fun s => S.theta u s / (S.lam u s : ℂ))
  let F := fun s => ENNReal.ofReal (W s / R s * ‖X s‖)
  let Z := fun t => ENNReal.ofReal (|S.Q u t| / S.r u t ^ 2)
  have hmap : MapsTo (fun s : ℝ => (u, s)) (Icc u v) (triangle 0 T) :=
    fun s hs => ⟨hu, hs.1, hs.2.trans hvT⟩
  have cr : ContinuousOn (S.r u) (Icc u v) := hset.c1.c1_r.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cl : ContinuousOn (S.lam u) (Icc u v) := hset.c1.c1_lam.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cx : ContinuousOn (fun s => S.theta u s / (S.lam u s : ℂ)) (Icc u v) :=
    (stab_out_ratio_c1 hset.c1).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
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
  have hF : Measurable F := ENNReal.measurable_ofReal.comp ((hW.div hR).mul hX.norm)
  have hlocal (t : ℝ) (ht : t ∈ Icc u v) :
      R t = S.r u t ∧ W t = S.lam u t ∧ X t = S.theta u t / (S.lam u t : ℂ) := by
    simp only [R, W, X, indicator_of_mem ht, and_self]
  have hr0 (t : ℝ) (ht : t ∈ Icc u v) : 0 ≤ S.r u t := by
    rcases ht.1.eq_or_lt with rfl | hut
    · rw [(hset.c1.axis u ⟨hu, le_rfl, huv.trans hvT⟩).1]
    · exact (hset.c1.r_pos (u, t) (hmap ht) hut).le
  have hE : 0 ≤ |e| * M := mul_nonneg (abs_nonneg _) ((by norm_num : (0 : ℝ) ≤ 1).trans hset.box.1)
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
  have hZ : ∀ t ∈ Icc u v, Z t ≤ ENNReal.ofReal (|e| * M) *
      ∫⁻ s in Icc u t, ENNReal.ofReal ((S.r u s / S.r u t) ^ (2 : ℝ)) * F s := by
    intro t ht
    rcases ht.1.eq_or_lt with rfl | hut
    · dsimp only [Z]
      rw [(hset.c1.axis u ⟨hu, le_rfl, huv.trans hvT⟩).1]
      norm_num
    have hrt := hset.c1.r_pos (u, t) (hmap ht) hut
    have cN : ContinuousOn (fun s => S.lam u s * S.r u s *
        ‖S.theta u s / (S.lam u s : ℂ)‖) (Icc u v) := by
      simpa only [Pi.mul_apply] using! (cl.mul cr).mul cx.norm
    have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hut.le).mp
      ((cN.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc (μ := volume) hut.le)
    have hn : ∀ᵐ s ∂volume.restrict (Icc u t), 0 ≤
        S.lam u s * S.r u s * ‖S.theta u s / (S.lam u s : ℂ)‖ / S.r u t ^ 2 := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact div_nonneg (mul_nonneg
        (mul_nonneg (hset.c1.lam_pos (u, s) (hmap ⟨hs.1, hs.2.trans ht.2⟩)).le
          (hr0 s ⟨hs.1, hs.2.trans ht.2⟩)) (norm_nonneg _)) (sq_nonneg _)
    have heq : (∫⁻ s in Icc u t, ENNReal.ofReal ((S.r u s / S.r u t) ^ (2 : ℝ)) * F s) =
        ENNReal.ofReal ((∫ s in u..t, S.lam u s * S.r u s *
          ‖S.theta u s / (S.lam u s : ℂ)‖) / S.r u t ^ 2) := by
      calc
        _ = ∫⁻ s in Icc u t, ENNReal.ofReal (S.lam u s * S.r u s *
            ‖S.theta u s / (S.lam u s : ℂ)‖ / S.r u t ^ 2) := by
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
      div_le_div_of_nonneg_right (stab_charge_primitive_norm_le hset hu hut.le (ht.2.trans hvT))
        (sq_nonneg (S.r u t))
  have hhardy := Mixed.lintegral_weighted_le_of_radial_moment
    huv (by norm_num : (0 : ℝ) < 2) hE hr hm
    (fun t ht => hset.c1.r_pos (u, t) (hmap ⟨ht.1.le, ht.2⟩) ht.1)
    hW (fun t ht => by rw [(hlocal t ht).2.1]; exact (hset.c1.lam_pos _ (hmap ht)).le)
    hF hd hZ
  have hfirst : (∫⁻ t in Icc u v, ENNReal.ofReal
      (S.lam u t * |S.Q u t| / S.r u t ^ 3)) ≤
        ENNReal.ofReal (|e| * M / 2) * ∫⁻ t in Icc u v, ENNReal.ofReal
          (S.lam u t / S.r u t * ‖S.theta u t / (S.lam u t : ℂ)‖) := by
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
  refine ⟨hfirst, hfirst.trans ?_⟩
  have hlin := stab_out_hardy hset hε hu (huv.trans hvT)
  rw [restrict_Ioc_eq_restrict_Icc] at hlin
  apply (mul_le_mul' le_rfl ((lintegral_mono_set (Icc_subset_Icc_right hvT)).trans hlin)).trans_eq
  rw [← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg hE (by norm_num))]
  congr 2
  ring

end EmcsfAcExtension.Local
