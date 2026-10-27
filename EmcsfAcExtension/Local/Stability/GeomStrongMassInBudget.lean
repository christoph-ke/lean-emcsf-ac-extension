module

public import EmcsfAcExtension.Local.Stability.GeomStrongMassInRaw
import EmcsfAcExtension.Local.Stability.ChargeDifferenceIndividual
import EmcsfAcExtension.Local.Stability.GeometryDifferenceWeights
import EmcsfAcExtension.Local.Stability.AssemblyMoments

/-! # Incoming mass source budgets

The incoming radius-square primitive and matching scalar Hardy bound
control the two terms in the normalized mass source through the axis.
All constants are numerical or depend only on the displayed envelope
constant, uniformly in the minimum radius and derivative suprema.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The incoming radius-square primitive has its exact coefficient `1/2`.
No size condition or derivative bound is used. -/
theorem stab_in_weight_radius_sq_lintegral
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    (∫⁻ t in Icc u v, ENNReal.ofReal (-S.nu t v / S.r t v * S.r t v ^ 2)) =
      ENNReal.ofReal (S.r u v ^ 2 / 2) := by
  have hmap : MapsTo (fun t : ℝ => (t, v)) (Icc u v) (triangle 0 T) :=
    fun t ht => ⟨hu.trans ht.1, ht.2, hvT⟩
  have cr := hset.c1.c1_r.continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn hmap
  have cn := hset.c1.c1_nu.continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn hmap
  have cF : ContinuousOn (fun t => -S.nu t v * S.r t v) (Icc u v) := cn.neg.mul cr
  have hi := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv cF
  have hder : ∀ t ∈ Ioo u v, HasDerivAt (fun s => -(S.r s v ^ 2) / 2)
      (-S.nu t v * S.r t v) t := by
    intro t ht
    have hp : (t, v) ∈ triangle 0 T := ⟨hu.trans ht.1.le, ht.2.le, hvT⟩
    have hd := hasDerivWithinAt_uncurry_triangle_u hset.c1.c1_r hp
    change HasDerivWithinAt (fun s => S.r s v) (pdU (triangle 0 T) S.r t v) (Icc 0 v) t at hd
    rw [(hset.c1.eq_u _ hp ht.2).1] at hd
    convert (((hd.hasDerivAt (Icc_mem_nhds (hu.trans_lt ht.1) ht.2)).pow 2).neg.div_const 2) using
        1; ring
  have hm := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv
    ((cr.pow 2).neg.div_const 2) hder hi
  change (∫ t in u..v, -S.nu t v * S.r t v) =
    -(S.r v v ^ 2) / 2 - -(S.r u v ^ 2) / 2 at hm
  rw [(hset.c1.axis v ⟨hu.trans huv, le_rfl, hvT⟩).1] at hm
  have hr0 : ∀ t ∈ Icc u v, 0 ≤ S.r t v := by
    intro t ht
    have hb := (stab_radius_bounds hset (hu.trans ht.1) ht.2 hvT).1
    exact (div_nonneg (sub_nonneg.mpr ht.2) (by norm_num)).trans hb
  calc
    _ = ∫⁻ t in Icc u v, ENNReal.ofReal (-S.nu t v * S.r t v) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro t ht
      by_cases hr : S.r t v = 0
      · simp only [hr, div_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
      · field_simp
    _ = ENNReal.ofReal (∫ t in Icc u v, -S.nu t v * S.r t v) := by
      apply (ofReal_integral_eq_lintegral_ofReal
        ((intervalIntegrable_iff_integrableOn_Icc_of_le huv).1 hi) ?_).symm
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact mul_nonneg (neg_pos.mpr (hset.c1.nu_neg _ (hmap ht))).le (hr0 t ht)
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le huv, hm]
      congr 1
      ring

/-- The second solution's incoming linear scalar Hardy budget in the
first solution's radial measure. The literal coefficient `256` is
universal; dependence on the envelope is the displayed factor `A`. -/
theorem stab_in_mixed_hardy_le
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (hA : 0 < A) (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : ε ^ 2 ≤ 1 / 4)
    {v : ℝ} (hv : 0 ≤ v) (hvT : v ≤ T) :
    (∫⁻ u in Icc 0 v, ENNReal.ofReal (-S₁.nu u v / S₁.r u v *
      ‖S₂.xi u v / (S₂.nu u v : ℂ)‖)) ≤ ENNReal.ofReal (256 * A * ε) := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hAε : 0 ≤ A * ε := mul_nonneg hA.le hε0
  have hm : (∫⁻ u in Icc 0 v, ENNReal.ofReal (-S₁.nu u v / S₁.r u v *
      ‖S₂.xi u v / (S₂.nu u v : ℂ)‖)) ≤
      16 * ∫⁻ u in Icc 0 v, ENNReal.ofReal (-S₂.nu u v / S₂.r u v *
        ‖S₂.xi u v / (S₂.nu u v : ℂ)‖) := by
    rw [← lintegral_const_mul' 16 _ (by norm_num)]
    apply setLIntegral_mono' measurableSet_Icc
    intro u hu
    rcases hu.2.eq_or_lt with rfl | huv
    · rw [(h₁s.c1.axis u ⟨hu.1, le_rfl, hvT⟩).1, div_zero, zero_mul,
        ENNReal.ofReal_zero]
      exact bot_le
    · have hh := mul_le_mul_of_nonneg_right
        (stab_in_weight_le_sixteen h₁s h₂s hu.1 huv hvT)
        (norm_nonneg (S₂.xi u v / (S₂.nu u v : ℂ)))
      simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16),
        ENNReal.ofReal_ofNat, mul_assoc] using ENNReal.ofReal_le_ofReal hh
  have hh := stab_in_hardy h₂s hε hv hvT
  have he := (le_add_of_nonneg_left bot_le).trans h₂s.env
  apply (hm.trans (mul_le_mul' le_rfl (hh.trans (mul_le_mul' le_rfl he)))).trans
  rw [← ENNReal.ofReal_ofNat 16, ← mul_assoc,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16 * (16 / 3))]
  apply ENNReal.ofReal_le_ofReal
  nlinarith only [hAε]

end EmcsfAcExtension.Local
