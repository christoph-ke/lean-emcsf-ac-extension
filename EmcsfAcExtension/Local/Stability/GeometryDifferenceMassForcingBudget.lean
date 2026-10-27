module

public import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassForcing
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassIndividualBudget
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassIntegration
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassBudgets
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassMeasure
import EmcsfAcExtension.Local.Stability.MomentsSections
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Integrated outgoing normalized mass difference forcing

Every singular source is integrated in the first solution's radial
measure. The scalar and individual mass terms have proved Hardy
budgets, and the electromagnetic square difference remains explicit.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The raw outgoing mass forcing has the scalar difference Hardy
cost, the absolute electromagnetic cost, and an `ε²G` remainder.
The numerical coefficients are universal; the only envelope dependence
is the displayed factor `A`. This is prior to charge projection. -/
theorem stab_out_mass_forcing_budget
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (hA : 0 < A) (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : ε ^ 2 ≤ 1 / 4)
    (hσ : sigma e M T ≤ 1) {u : ℝ} (hu : 0 ≤ u) (huT : u ≤ T) :
    (∫⁻ t in Icc u T, ENNReal.ofReal |massDifferenceForcing S₁ S₂ u t|) ≤
      ENNReal.ofReal (2 * ε) * (∫⁻ t in Icc u T, ENNReal.ofReal (S₁.lam u t / S₁.r u t *
        ‖S₁.theta u t / (S₁.lam u t : ℂ) - S₂.theta u t / (S₂.lam u t : ℂ)‖)) +
      (∫⁻ t in Icc u T, ENNReal.ofReal (S₁.lam u t / S₁.r u t *
        |S₁.Q u t ^ 2 / S₁.r u t ^ 2 - S₂.Q u t ^ 2 / S₂.r u t ^ 2|)) +
      ENNReal.ofReal ((87040 * A + 10880) * ε ^ 2 * (geomDist T S₁ S₂).toReal) := by
  rw [← restrict_Ioc_eq_restrict_Icc]
  let w := fun t => S₁.lam u t / S₁.r u t
  let x₁ := fun t => S₁.theta u t / (S₁.lam u t : ℂ)
  let x₂ := fun t => S₂.theta u t / (S₂.lam u t : ℂ)
  let E₁ := fun t => S₁.Q u t ^ 2 / S₁.r u t ^ 2
  let E₂ := fun t => S₂.Q u t ^ 2 / S₂.r u t ^ 2
  let d := fun t => w t * ‖x₁ t - x₂ t‖
  let c := fun t => w t * |E₁ t - E₂ t|
  let x := fun t => w t * ‖x₂ t‖ ^ 2
  let f := fun t => w t * E₂ t
  let m := fun t => w t * |S₂.mu u t|
  let G := (geomDist T S₁ S₂).toReal
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hσ0 : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hmap : MapsTo (fun t : ℝ => (u, t)) (Ioc u T) (triangle 0 T) :=
    fun t ht => ⟨hu, ht.1.le, ht.2⟩
  have cL := h₁s.c1.c1_lam.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cR₁ := h₁s.c1.c1_r.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cR₂ := h₂s.c1.c1_r.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cQ₁ := h₁s.c1.c1_Q.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cQ₂ := h₂s.c1.c1_Q.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cX₁ : ContinuousOn x₁ (Ioc u T) := (stab_out_ratio_c1 h₁s.c1).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cX₂ : ContinuousOn x₂ (Ioc u T) := (stab_out_ratio_c1 h₂s.c1).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cw : ContinuousOn w (Ioc u T) := cL.div cR₁
    (fun t ht => (h₁s.c1.r_pos (u, t) (hmap ht) ht.1).ne')
  have ce₁ : ContinuousOn E₁ (Ioc u T) := (cQ₁.pow 2).div (cR₁.pow 2)
    (fun t ht => pow_ne_zero 2 (h₁s.c1.r_pos (u, t) (hmap ht) ht.1).ne')
  have ce₂ : ContinuousOn E₂ (Ioc u T) := (cQ₂.pow 2).div (cR₂.pow 2)
    (fun t ht => pow_ne_zero 2 (h₂s.c1.r_pos (u, t) (hmap ht) ht.1).ne')
  have ad : AEMeasurable (fun t => ENNReal.ofReal (d t))
      (volume.restrict (Ioc u T)) := by
    simpa only [Function.comp_def, d] using!
      ENNReal.continuous_ofReal.measurable.comp_aemeasurable
        ((cw.mul (cX₁.sub cX₂).norm).aemeasurable (μ := volume) measurableSet_Ioc)
  have ac : AEMeasurable (fun t => ENNReal.ofReal (c t))
      (volume.restrict (Ioc u T)) := by
    simpa only [Function.comp_def, c] using!
      ENNReal.continuous_ofReal.measurable.comp_aemeasurable
        ((cw.mul (ce₁.sub ce₂).abs).aemeasurable (μ := volume) measurableSet_Ioc)
  have ax : AEMeasurable (fun t => ENNReal.ofReal (x t))
      (volume.restrict (Ioc u T)) := by
    simpa only [Function.comp_def, x] using!
      ENNReal.continuous_ofReal.measurable.comp_aemeasurable
        ((cw.mul (cX₂.norm.pow 2)).aemeasurable (μ := volume) measurableSet_Ioc)
  have af : AEMeasurable (fun t => ENNReal.ofReal (f t))
      (volume.restrict (Ioc u T)) := by
    simpa only [Function.comp_def, f] using!
      ENNReal.continuous_ofReal.measurable.comp_aemeasurable
        ((cw.mul ce₂).aemeasurable (μ := volume) measurableSet_Ioc)
  have hi := stab_mass_lintegral_le_of_forcing
    (F := fun t => ENNReal.ofReal |massDifferenceForcing S₁ S₂ u t|)
    (d := fun t => ENNReal.ofReal (d t)) (c := fun t => ENNReal.ofReal (c t))
    (x := fun t => ENNReal.ofReal (x t)) (e := fun t => ENNReal.ofReal (f t))
    (m := fun t => ENNReal.ofReal (m t))
    (a := ENNReal.ofReal (2 * ε)) (b := ENNReal.ofReal (20 * G))
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top ad ac ax af (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have hw0 : 0 ≤ w t := div_nonneg (h₁s.c1.lam_pos (u, t) (hmap ht)).le
        (h₁s.c1.r_pos (u, t) (hmap ht) ht.1).le
      have hd0 : 0 ≤ d t := mul_nonneg hw0 (norm_nonneg _)
      have hc0 : 0 ≤ c t := mul_nonneg hw0 (abs_nonneg _)
      have hx0 : 0 ≤ x t := mul_nonneg hw0 (sq_nonneg _)
      have hf0 : 0 ≤ f t := by dsimp only [f, E₂]; positivity
      have hm0 : 0 ≤ m t := mul_nonneg hw0 (abs_nonneg _)
      have hp : |massDifferenceForcing S₁ S₂ u t| ≤
          (2 * ε) * d t + c t + (20 * G) * (x t + f t + m t) := by
        convert stab_out_mass_difference_forcing_le h₁s h₂s hu ht.1 ht.2 using 1
        dsimp only [d, c, x, f, m, w, x₁, x₂, E₁, E₂, G]
        ring
      apply (ENNReal.ofReal_le_ofReal hp).trans_eq
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) hc0,
        ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * ε),
        ENNReal.ofReal_mul (by positivity : 0 ≤ 20 * G),
        ENNReal.ofReal_add (add_nonneg hx0 hf0) hm0,
        ENNReal.ofReal_add hx0 hf0])
  have hxB := stab_out_mixed_quadratic_le h₁s h₂s hε hu huT
  have hfB := stab_out_mixed_em_le h₁s h₂s hu huT
  have hmB := stab_out_mixed_mass_le hA h₁s h₂s hε hu huT
  rw [← restrict_Ioc_eq_restrict_Icc] at hxB hfB hmB
  apply hi.trans
  apply add_le_add le_rfl
  apply (mul_le_mul' le_rfl (add_le_add (add_le_add hxB hfB) hmB)).trans
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 20 * G)]
  apply ENNReal.ofReal_le_ofReal
  have hσscale := mul_le_mul_of_nonneg_right hσ (sq_nonneg ε)
  have hem : 8 * (|e| * M * ε) ^ 2 * T ^ 2 = 32 * sigma e M T * ε ^ 2 := by
    dsimp only [sigma]
    simp only [mul_pow, sq_abs]
    ring
  rw [hem]
  have hh : 256 * A * ε ^ 2 + 32 * sigma e M T * ε ^ 2 +
      16 * ((256 * A + 32 * sigma e M T) * ε ^ 2) ≤
      (4352 * A + 544) * ε ^ 2 := by nlinarith only [hσscale]
  have hfinal := mul_le_mul_of_nonneg_left hh (show 0 ≤ 20 * G by positivity)
  dsimp only [G] at hfinal ⊢
  nlinarith only [hfinal]

end EmcsfAcExtension.Local
