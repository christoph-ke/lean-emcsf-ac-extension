module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassIndividual
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassMeasure
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassBudgets
import EmcsfAcExtension.Local.Stability.GeometryDifferenceWeights
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Individual and mixed weighted mass budgets

The normalized constraint is integrated with its positive radial
damping. This proves a weighted mass estimate through the axis, rather
than inferring one from a pointwise bound.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The individual outgoing mass source has budget
`(256 A + 32 σ) ε²`. All coefficients are universal, and the displayed
parameters are the only dependence of this source estimate. -/
theorem stab_out_mass_source_budget
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hA : 0 < A) (hset : StabSetting e T ε M A S h) (hε : ε ^ 2 ≤ 1 / 4)
    {u : ℝ} (hu : 0 ≤ u) (huT : u ≤ T) :
    (∫⁻ t in Icc u T, ENNReal.ofReal (S.lam u t / S.r u t *
      (‖S.theta u t / (S.lam u t : ℂ)‖ ^ 2 + S.Q u t ^ 2 / S.r u t ^ 2))) ≤
        ENNReal.ofReal ((256 * A + 32 * sigma e M T) * ε ^ 2) := by
  rw [← restrict_Ioc_eq_restrict_Icc]
  let f := fun t => S.lam u t / S.r u t * ‖S.theta u t / (S.lam u t : ℂ)‖ ^ 2
  let g := fun t => S.lam u t / S.r u t * (S.Q u t ^ 2 / S.r u t ^ 2)
  have hmap : MapsTo (fun t : ℝ => (u, t)) (Ioc u T) (triangle 0 T) :=
    fun t ht => ⟨hu, ht.1.le, ht.2⟩
  have cL := hset.c1.c1_lam.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cR := hset.c1.c1_r.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cX := (stab_out_ratio_c1 hset.c1).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cf : ContinuousOn f (Ioc u T) :=
    (cL.div cR (fun t ht => (hset.c1.r_pos (u, t) (hmap ht) ht.1).ne')).mul
      (cX.norm.pow 2)
  have heq : (∫⁻ t in Ioc u T, ENNReal.ofReal (S.lam u t / S.r u t *
      (‖S.theta u t / (S.lam u t : ℂ)‖ ^ 2 + S.Q u t ^ 2 / S.r u t ^ 2))) =
      (∫⁻ t in Ioc u T, ENNReal.ofReal (f t)) +
        ∫⁻ t in Ioc u T, ENNReal.ofReal (g t) := by
    have af : AEMeasurable (fun t => ENNReal.ofReal (f t)) (volume.restrict (Ioc u T)) := by
      simpa only [Function.comp_def] using! ENNReal.continuous_ofReal.measurable.comp_aemeasurable
        (cf.aemeasurable measurableSet_Ioc)
    rw [← lintegral_add_left' (f := fun t => ENNReal.ofReal (f t))
      (g := fun t => ENNReal.ofReal (g t)) af]
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro t ht
    have hl := (hset.c1.lam_pos (u, t) (hmap ht)).le
    have hr := (hset.c1.r_pos (u, t) (hmap ht) ht.1).le
    dsimp only [f, g]
    rw [mul_add, ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [heq, restrict_Ioc_eq_restrict_Icc]
  apply (add_le_add (stab_out_mixed_quadratic_le hset hset hε hu huT)
    (stab_out_mixed_em_le hset hset hu huT)).trans_eq
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  dsimp only [sigma]
  simp only [mul_pow, sq_abs]
  ring

/-- The second solution's absolute mass ratio is integrable in the
first solution's outgoing radial measure, with universal coefficient
`16` multiplying the individual source budget. -/
theorem stab_out_mixed_mass_le
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (hA : 0 < A) (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : ε ^ 2 ≤ 1 / 4)
    {u : ℝ} (hu : 0 ≤ u) (huT : u ≤ T) :
    (∫⁻ t in Icc u T, ENNReal.ofReal (S₁.lam u t / S₁.r u t * |S₂.mu u t|)) ≤
      ENNReal.ofReal (16 * ((256 * A + 32 * sigma e M T) * ε ^ 2)) := by
  rcases huT.eq_or_lt with rfl | huT
  · simp
  · have hmass := (stab_out_mass_source_comparison h₂s hu huT le_rfl).2
    rw [restrict_Ioc_eq_restrict_Icc] at hmass
    have hbudget := hmass.trans (stab_out_mass_source_budget hA h₂s hε hu huT.le)
    have hi : (∫⁻ t in Icc u T, ENNReal.ofReal (S₁.lam u t / S₁.r u t * |S₂.mu u t|)) ≤
        ENNReal.ofReal 16 * ∫⁻ t in Icc u T,
          ENNReal.ofReal (S₂.lam u t / S₂.r u t * |S₂.mu u t|) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      rcases ht.1.eq_or_lt with rfl | hut
      · simp only [(h₁s.c1.axis u ⟨hu, le_rfl, huT.le⟩).1,
          div_zero, zero_mul, ENNReal.ofReal_zero]
        exact bot_le
      · rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]
        apply ENNReal.ofReal_le_ofReal
        have hh := mul_le_mul_of_nonneg_right
          (stab_out_weight_le_sixteen h₁s h₂s hu hut ht.2) (abs_nonneg (S₂.mu u t))
        nlinarith only [hh]
    apply hi.trans
    apply (mul_le_mul' le_rfl hbudget).trans_eq
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]

end EmcsfAcExtension.Local
