module

public import EmcsfAcExtension.Local.Stability.GeomStrongMassInMeasure
import EmcsfAcExtension.Local.Stability.FluxDifferenceRegularity
import EmcsfAcExtension.Local.Stability.MomentsSections
import EmcsfAcExtension.Local.Stability.GeometryDifferenceWeights
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Individual incoming mass Hardy budgets

The damped incoming constraint and its own scalar and electromagnetic
source budgets give derivative-independent weighted mass bounds.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- Incoming quadratic scalar flux in the comparison radial measure.
The coefficient `256` is universal; the envelope dependence is `A`.
All solution parameters and derivative suprema are uniform. -/
theorem stab_in_mixed_quadratic_le
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (hA : 0 < A) (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : ε ^ 2 ≤ 1 / 4)
    {v : ℝ} (hv : 0 ≤ v) (hvT : v ≤ T) :
    (∫⁻ t in Icc 0 v, ENNReal.ofReal (-S₁.nu t v / S₁.r t v *
      ‖S₂.xi t v / (S₂.nu t v : ℂ)‖ ^ 2)) ≤ ENNReal.ofReal (256 * A * ε ^ 2) := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hi : (∫⁻ t in Icc 0 v, ENNReal.ofReal (-S₁.nu t v / S₁.r t v *
      ‖S₂.xi t v / (S₂.nu t v : ℂ)‖ ^ 2)) ≤ ENNReal.ofReal ε *
      ∫⁻ t in Icc 0 v, ENNReal.ofReal (-S₁.nu t v / S₁.r t v *
        ‖S₂.xi t v / (S₂.nu t v : ℂ)‖) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' measurableSet_Icc
    intro t ht
    have hp : (t, v) ∈ triangle 0 T := ⟨ht.1, ht.2, hvT⟩
    have hr0 : 0 ≤ S₁.r t v := (div_nonneg (sub_nonneg.mpr ht.2) (by norm_num)).trans
      (stab_radius_bounds h₁s ht.1 ht.2 hvT).1
    have hw := div_nonneg (neg_pos.mpr (h₁s.c1.nu_neg _ hp)).le hr0
    have hy := (le_add_of_nonneg_left (norm_nonneg (S₂.theta t v / (S₂.lam t v : ℂ)))).trans
      (h₂s.box.2 (t, v) hp).2.2.2.2.2.1
    rw [← ENNReal.ofReal_mul hε0]
    apply ENNReal.ofReal_le_ofReal
    have hh := mul_le_mul_of_nonneg_right hy (norm_nonneg (S₂.xi t v / (S₂.nu t v : ℂ)))
    have hh' := mul_le_mul_of_nonneg_left hh hw
    nlinarith only [hh']
  apply (hi.trans (mul_le_mul' le_rfl
    (stab_in_mixed_hardy_le hA h₁s h₂s hε hv hvT))).trans_eq
  rw [← ENNReal.ofReal_mul hε0]
  congr 1
  ring

/-- The individual incoming mass source has budget
`(256 A + 32 σ) ε²`. All coefficients are universal, and the displayed
parameters are the only dependence of this source estimate. -/
theorem stab_in_mass_source_budget
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hA : 0 < A) (hset : StabSetting e T ε M A S h) (hε : ε ^ 2 ≤ 1 / 4)
    {v : ℝ} (hv : 0 ≤ v) (hvT : v ≤ T) :
    (∫⁻ t in Icc 0 v, ENNReal.ofReal ((-S.nu t v) / S.r t v *
      (‖S.xi t v / (S.nu t v : ℂ)‖ ^ 2 + S.Q t v ^ 2 / S.r t v ^ 2))) ≤
        ENNReal.ofReal ((256 * A + 32 * sigma e M T) * ε ^ 2) := by
  rw [← restrict_Ico_eq_restrict_Icc]
  let f := fun t => (-S.nu t v) / S.r t v * ‖S.xi t v / (S.nu t v : ℂ)‖ ^ 2
  let g := fun t => (-S.nu t v) / S.r t v * (S.Q t v ^ 2 / S.r t v ^ 2)
  have hmap : MapsTo (fun t : ℝ => (t, v)) (Ico 0 v) (triangle 0 T) :=
    fun t ht => ⟨ht.1, ht.2.le, hvT⟩
  have cL := hset.c1.c1_nu.continuousOn.neg.comp
    (continuous_id.prodMk continuous_const).continuousOn hmap
  have cR := hset.c1.c1_r.continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn hmap
  have cX := (stab_in_ratio_c1 hset.c1).continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn hmap
  have cf : ContinuousOn f (Ico 0 v) :=
    (cL.div cR (fun t ht => (hset.c1.r_pos (t, v) (hmap ht) ht.2).ne')).mul
      (cX.norm.pow 2)
  have heq : (∫⁻ t in Ico 0 v, ENNReal.ofReal ((-S.nu t v) / S.r t v *
      (‖S.xi t v / (S.nu t v : ℂ)‖ ^ 2 + S.Q t v ^ 2 / S.r t v ^ 2))) =
      (∫⁻ t in Ico 0 v, ENNReal.ofReal (f t)) +
        ∫⁻ t in Ico 0 v, ENNReal.ofReal (g t) := by
    have af : AEMeasurable (fun t => ENNReal.ofReal (f t)) (volume.restrict (Ico 0 v)) := by
      simpa only [Function.comp_def] using! ENNReal.continuous_ofReal.measurable.comp_aemeasurable
        (cf.aemeasurable measurableSet_Ico)
    rw [← lintegral_add_left' (f := fun t => ENNReal.ofReal (f t))
      (g := fun t => ENNReal.ofReal (g t)) af]
    apply setLIntegral_congr_fun measurableSet_Ico
    intro t ht
    have hl := (neg_pos.mpr (hset.c1.nu_neg (t, v) (hmap ht))).le
    have hr := (hset.c1.r_pos (t, v) (hmap ht) ht.2).le
    dsimp only [f, g]
    rw [mul_add, ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [heq, restrict_Ico_eq_restrict_Icc]
  apply (add_le_add (stab_in_mixed_quadratic_le hA hset hset hε hv hvT)
    (stab_in_mixed_em_le hset hset hv hvT)).trans_eq
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  dsimp only [sigma]
  simp only [mul_pow, sq_abs]
  ring

/-- The second solution's absolute mass ratio is integrable in the
first solution's incoming radial measure, with universal coefficient
`16` multiplying the individual source budget. -/
theorem stab_in_mixed_mass_le
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (hA : 0 < A) (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : ε ^ 2 ≤ 1 / 4)
    {v : ℝ} (hv : 0 ≤ v) (hvT : v ≤ T) :
    (∫⁻ t in Icc 0 v, ENNReal.ofReal ((-S₁.nu t v) / S₁.r t v * |S₂.mu t v|)) ≤
      ENNReal.ofReal (16 * ((256 * A + 32 * sigma e M T) * ε ^ 2)) := by
  rcases hv.eq_or_lt with rfl | hv
  · simp
  · have hmass := stab_in_mass_source_comparison h₂s le_rfl hv hvT
    have hbudget := hmass.trans (stab_in_mass_source_budget hA h₂s hε hv.le hvT)
    have hi : (∫⁻ t in Icc 0 v, ENNReal.ofReal ((-S₁.nu t v) / S₁.r t v * |S₂.mu t v|)) ≤
        ENNReal.ofReal 16 * ∫⁻ t in Icc 0 v,
          ENNReal.ofReal ((-S₂.nu t v) / S₂.r t v * |S₂.mu t v|) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      rcases ht.2.eq_or_lt with rfl | htv
      · simp only [(h₁s.c1.axis t ⟨ht.1, le_rfl, hvT⟩).1,
          div_zero, zero_mul, ENNReal.ofReal_zero]
        exact bot_le
      · rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]
        apply ENNReal.ofReal_le_ofReal
        have hh := mul_le_mul_of_nonneg_right
          (stab_in_weight_le_sixteen h₁s h₂s ht.1 htv hvT) (abs_nonneg (S₂.mu t v))
        nlinarith only [hh]
    apply hi.trans
    apply (mul_le_mul' le_rfl hbudget).trans_eq
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]

end EmcsfAcExtension.Local
