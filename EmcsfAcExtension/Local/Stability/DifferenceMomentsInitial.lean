module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.DifferenceMomentsInitialForcing
import EmcsfAcExtension.Local.Stability.DifferenceMomentsRaw
import EmcsfAcExtension.Local.Stability.DifferenceMomentsHardyRaw

/-! # Initial-cone radial comparison with local mass feedback

The common initial radius gauge removes the moving radial-weight
error. The point and Hardy comparisons therefore retain only the
initial mass-ratio bound, which will be absorbed on that cone.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- On the initial cone, both the radial ratio difference and its
Hardy integral are bounded by `8Δj+32AεU`, provided its mass-ratio
difference is bounded by `U`. Numerical coefficients are universal;
only the displayed `A` dependence remains in this conditional helper. -/
theorem stab_initial_ratio_le_of_mass_bound
    {e T ε M A U : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (hA : 0 < A) (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : 3 * ε ^ 2 ≤ 1 / 2) (hU : 0 ≤ U)
    (hmass : ∀ v ∈ Icc 0 T, |S₁.mu 0 v - S₂.mu 0 v| ≤ U) :
    (∀ v ∈ Icc 0 T, ENNReal.ofReal
      ‖S₁.theta 0 v / (S₁.lam 0 v : ℂ) - S₂.theta 0 v / (S₂.lam 0 v : ℂ)‖ ≤
        ENNReal.ofReal (8 * (jDist T S₁ S₂).toReal + 32 * A * ε * U)) ∧
      (∫⁻ t in Icc 0 T, ENNReal.ofReal (S₁.lam 0 t / S₁.r 0 t *
        ‖S₁.theta 0 t / (S₁.lam 0 t : ℂ) - S₂.theta 0 t / (S₂.lam 0 t : ℂ)‖)) ≤
          ENNReal.ofReal (8 * (jDist T S₁ S₂).toReal + 32 * A * ε * U) := by
  let q := fun t =>
    jC1 (triangle 0 T) S₁ 0 t / ((1 - S₁.mu 0 t : ℝ) : ℂ) -
    jC1 (triangle 0 T) S₂ 0 t / ((1 - S₂.mu 0 t : ℝ) : ℂ) -
    (S₁.lam 0 t / S₁.r 0 t - S₂.lam 0 t / S₂.r 0 t) •
      (S₂.theta 0 t / (S₂.lam 0 t : ℂ) - ‖S₂.theta 0 t / (S₂.lam 0 t : ℂ)‖ ^ 2 •
        (S₂.theta 0 t / (S₂.lam 0 t : ℂ)))
  have hε1 : ε ≤ 1 := by nlinarith only [hε, sq_nonneg (ε - 1)]
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hbudget := stab_initial_forcing_le_of_mass_bound hA h₁s h₂s hε1 hU hmass
  change (∫⁻ t in Icc 0 T, ENNReal.ofReal ‖q t‖) ≤ _ at hbudget
  constructor
  · intro v hv
    rcases hv.1.eq_or_lt with rfl | hv0
    · rw [stab_out_ratio_axis h₁s ⟨le_rfl, h₁s.pos.le⟩,
        stab_out_ratio_axis h₂s ⟨le_rfl, h₂s.pos.le⟩,
        sub_self, norm_zero, ENNReal.ofReal_zero]
      exact bot_le
    · have hm := stab_out_difference_moment_raw h₁s h₂s hε le_rfl hv0 hv.2
      apply hm.trans
      apply le_trans ?_ (hbudget.trans (ENNReal.ofReal_le_ofReal (by
        have hJ := ENNReal.toReal_nonneg (a := jDist T S₁ S₂)
        have hh : 0 ≤ A * ε * U := by positivity
        nlinarith only [hJ, hh])))
      apply le_trans ?_ (lintegral_mono_set (show Ioc (0 : ℝ) v ⊆ Icc 0 T from
        fun t ht => ⟨ht.1.le, ht.2.trans hv.2⟩))
      apply setLIntegral_mono' measurableSet_Ioc
      intro t ht
      apply ENNReal.ofReal_le_ofReal
      have hr := h₁s.c1.r_pos (0, v) ⟨le_rfl, hv0.le, hv.2⟩ hv0
      have hrt := h₁s.c1.r_pos (0, t) ⟨le_rfl, ht.1.le, ht.2.trans hv.2⟩ ht.1
      have hpow := Real.rpow_le_one (div_nonneg hrt.le hr.le)
        ((div_le_one hr).mpr (stab_radius_section_order h₁s le_rfl ht.1.le ht.2 hv.2).1)
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow (norm_nonneg (q t))
  · have hh := stab_out_difference_hardy_raw h₁s h₂s hε le_rfl h₁s.pos le_rfl
    rw [restrict_Ioc_eq_restrict_Icc] at hh
    apply hh.trans
    apply (mul_le_mul' le_rfl hbudget).trans_eq
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring

end EmcsfAcExtension.Local
