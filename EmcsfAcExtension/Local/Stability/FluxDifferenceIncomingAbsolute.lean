module

public import EmcsfAcExtension.Local.Stability.FluxDifference
import EmcsfAcExtension.Local.Stability.GeometryDifferenceWeights
import EmcsfAcExtension.Local.Stability.MomentsQuadratic
import EmcsfAcExtension.Local.Stability.FluxDifferenceRegularity
import EmcsfAcExtension.Local.Stability.DifferenceMomentsIncomingComparison

/-! # Absolute incoming quadratic flux comparison

The difference of the exact optical exponents is controlled by the
weighted radial difference and the individual quadratic Hardy budget.
Mass feedback is retained through the radial difference term.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The absolute incoming quadratic flux difference is at most `2ε` times
the weighted radial difference plus `5120 A ε² G`. All numerical
coefficients are universal, before the pair and all parameters; only
the displayed factor `A` carries envelope dependence. -/
theorem stab_in_quadratic_flux_lintegral_raw
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (_hA : 0 < A) (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : ε ^ 2 ≤ 1 / 4)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    (∫⁻ s in Icc u v, ENNReal.ofReal
      |-S₁.nu s v / S₁.r s v * ‖S₁.xi s v / (S₁.nu s v : ℂ)‖ ^ 2 -
        -S₂.nu s v / S₂.r s v * ‖S₂.xi s v / (S₂.nu s v : ℂ)‖ ^ 2|) ≤
      ENNReal.ofReal (2 * ε) * (∫⁻ s in Icc 0 v,
        ENNReal.ofReal (-S₁.nu s v / S₁.r s v *
          ‖S₁.xi s v / (S₁.nu s v : ℂ) - S₂.xi s v / (S₂.nu s v : ℂ)‖)) +
      ENNReal.ofReal (5120 * A * ε ^ 2 * (geomDist T S₁ S₂).toReal) := by
  let B := fun s => -S₁.nu s v / S₁.r s v
  let x₁ := fun s => S₁.xi s v / (S₁.nu s v : ℂ)
  let x₂ := fun s => S₂.xi s v / (S₂.nu s v : ℂ)
  let d := fun s => B s * ‖x₁ s - x₂ s‖
  let h := fun s => B s * ‖x₂ s‖ ^ 2
  let G := (geomDist T S₁ S₂).toReal
  have huT := huv.le.trans hvT
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi u u / (S₂.nu u u : ℂ)))).trans
      (h₂s.box.2 (u, u) ⟨hu, le_rfl, huT⟩).2.2.2.2.2.1)
  have hmap : MapsTo (fun s : ℝ => (s, v)) (Icc 0 v) (triangle 0 T) :=
    fun s hs => ⟨hs.1, hs.2, hvT⟩
  have cL := h₁s.c1.c1_nu.continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn hmap |>.neg
  have cR := h₁s.c1.c1_r.continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn hmap
  have cX₁ : ContinuousOn x₁ (Icc 0 v) := (stab_in_ratio_c1 h₁s.c1).continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn hmap
  have cX₂ : ContinuousOn x₂ (Icc 0 v) := (stab_in_ratio_c1 h₂s.c1).continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn hmap
  have aB : AEMeasurable B (volume.restrict (Icc 0 v)) :=
    (cL.aemeasurable measurableSet_Icc).div (cR.aemeasurable measurableSet_Icc)
  have ad : AEMeasurable (fun s => ENNReal.ofReal (d s)) (volume.restrict (Icc 0 v)) :=
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      (aB.mul ((cX₁.sub cX₂).norm.aemeasurable measurableSet_Icc))
  have hpoint : ∀ᵐ s ∂volume.restrict (Icc u v),
      0 ≤ d s ∧ 0 ≤ h s ∧
      |-S₁.nu s v / S₁.r s v * ‖x₁ s‖ ^ 2 -
        -S₂.nu s v / S₂.r s v * ‖x₂ s‖ ^ 2| ≤ (2 * ε) * d s + (20 * G) * h s := by
    have hne : ∀ᵐ s : ℝ, s ≠ v := by simp [ae_iff, measure_singleton]
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with s hs hsu
    have hsv : s < v := lt_of_le_of_ne hs.2 hsu
    have hp : (s, v) ∈ triangle 0 T := ⟨hu.trans hs.1, hsv.le, hvT⟩
    have hB : 0 ≤ B s := div_nonneg (neg_pos.mpr (h₁s.c1.nu_neg (s, v) hp)).le
      (h₁s.c1.r_pos (s, v) hp hsv).le
    exact ⟨mul_nonneg hB (norm_nonneg _), mul_nonneg hB (sq_nonneg _),
      stab_in_quadratic_flux_sub_le h₁s h₂s (hu.trans hs.1) hsv hvT⟩
  have hi : (∫⁻ s in Icc u v, ENNReal.ofReal
      |-S₁.nu s v / S₁.r s v * ‖x₁ s‖ ^ 2 - -S₂.nu s v / S₂.r s v * ‖x₂ s‖ ^ 2|) ≤
      ENNReal.ofReal (2 * ε) * (∫⁻ s in Icc u v, ENNReal.ofReal (d s)) +
        ENNReal.ofReal (20 * G) * (∫⁻ s in Icc u v, ENNReal.ofReal (h s)) := by
    have hm : (∫⁻ s in Icc u v, ENNReal.ofReal
        |-S₁.nu s v / S₁.r s v * ‖x₁ s‖ ^ 2 - -S₂.nu s v / S₂.r s v * ‖x₂ s‖ ^ 2|) ≤
        ∫⁻ s in Icc u v, ENNReal.ofReal (2 * ε) * ENNReal.ofReal (d s) +
          ENNReal.ofReal (20 * G) * ENNReal.ofReal (h s) := by
      apply lintegral_mono_ae
      filter_upwards [hpoint] with s hs
      apply (ENNReal.ofReal_le_ofReal hs.2.2).trans_eq
      rw [ENNReal.ofReal_add (mul_nonneg (mul_nonneg (by norm_num) hε0) hs.1)
        (mul_nonneg (mul_nonneg (by norm_num) ENNReal.toReal_nonneg) hs.2.1),
        ENNReal.ofReal_mul (mul_nonneg (by norm_num) hε0),
        ENNReal.ofReal_mul (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)]
    apply hm.trans_eq
    rw [lintegral_add_left' (ad.mono_measure
      (Measure.restrict_mono (Icc_subset_Icc_left hu) le_rfl) |>.const_mul _),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hquad : (∫⁻ s in Icc 0 v, ENNReal.ofReal (h s)) ≤
      ENNReal.ofReal (256 * A * ε ^ 2) := by
    have hq := stab_in_hardy_quadratic_of_identity h₂s
      (fun u v hu huv hvT => stab_in_reconstruction_smul h₂s.c1 hu huv hvT)
      hε (hu.trans huv.le) hvT
    have hcost : ENNReal.ofReal ((16 / 3 : ℝ) * ε) ≤ ENNReal.ofReal (16 * ε) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by norm_num) hε0)
    have henv : (∫⁻ s in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S₂) s) ≤
        ENNReal.ofReal (A * ε) := (le_add_of_nonneg_left bot_le).trans h₂s.env
    have hqm := hq.trans (mul_le_mul hcost henv bot_le bot_le)
    have hmix : (∫⁻ s in Icc 0 v, ENNReal.ofReal (h s)) ≤
        ENNReal.ofReal 16 * ∫⁻ s in Icc 0 v, ENNReal.ofReal
          (-S₂.nu s v / S₂.r s v * ‖x₂ s‖ ^ 2) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      have hne : ∀ᵐ s : ℝ, s ≠ v := by simp [ae_iff, measure_singleton]
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with s hs hsu
      have hsv : s < v := lt_of_le_of_ne hs.2 hsu
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]
      apply ENNReal.ofReal_le_ofReal
      simpa only [h, B, mul_assoc] using mul_le_mul_of_nonneg_right
        (stab_in_weight_le_sixteen h₁s h₂s hs.1 hsv hvT) (sq_nonneg ‖x₂ s‖)
    apply hmix.trans
    apply (mul_le_mul' le_rfl hqm).trans_eq
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 16 * (16 * ε))]
    congr 1
    ring
  apply hi.trans
  apply add_le_add
  · exact mul_le_mul' le_rfl (lintegral_mono_set (Icc_subset_Icc_left hu))
  · apply le_trans (mul_le_mul' le_rfl
      ((lintegral_mono_set (Icc_subset_Icc_left hu)).trans hquad))
    rw [← ENNReal.ofReal_mul (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)]
    apply ENNReal.ofReal_le_ofReal
    apply le_of_eq
    ring


/-- The incoming optical exponent difference is bounded by the raw
weighted incoming difference and `5120Aε²G`. The coefficients `2` and
`5120` are universal, with all envelope dependence displayed explicitly. -/
theorem stab_in_optical_exponent_sub_le
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (hA : 0 < A) (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : ε ^ 2 ≤ 1 / 4)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ENNReal.ofReal |(∫ s in u..v, -S₁.nu s v / S₁.r s v *
        ‖S₁.xi s v / (S₁.nu s v : ℂ)‖ ^ 2) -
      (∫ s in u..v, -S₂.nu s v / S₂.r s v *
        ‖S₂.xi s v / (S₂.nu s v : ℂ)‖ ^ 2)| ≤
      ENNReal.ofReal (2 * ε) * (∫⁻ s in Icc 0 v,
        ENNReal.ofReal (-S₁.nu s v / S₁.r s v *
          ‖S₁.xi s v / (S₁.nu s v : ℂ) - S₂.xi s v / (S₂.nu s v : ℂ)‖)) +
      ENNReal.ofReal (5120 * A * ε ^ 2 * (geomDist T S₁ S₂).toReal) := by
  have hmap : MapsTo (fun s : ℝ => (s, v)) (Icc u v) (triangle 0 T) :=
    fun s hs => ⟨hu.trans hs.1, hs.2, hvT⟩
  have cF₁ := (stab_in_quadratic_flux_continuous h₁s).comp
    (continuous_id.prodMk continuous_const).continuousOn hmap
  have cF₂ := (stab_in_quadratic_flux_continuous h₂s).comp
    (continuous_id.prodMk continuous_const).continuousOn hmap
  have iF₁ : IntervalIntegrable (fun s => -S₁.nu s v / S₁.r s v *
      ‖S₁.xi s v / (S₁.nu s v : ℂ)‖ ^ 2) volume u v := by
    simpa only [Function.comp_def] using!
      ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv.le cF₁
  have iF₂ : IntervalIntegrable (fun s => -S₂.nu s v / S₂.r s v *
      ‖S₂.xi s v / (S₂.nu s v : ℂ)‖ ^ 2) volume u v := by
    simpa only [Function.comp_def] using!
      ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv.le cF₂
  rw [← intervalIntegral.integral_sub iF₁ iF₂, ← Real.norm_eq_abs, ofReal_norm,
    intervalIntegral.integral_of_le huv.le]
  apply (enorm_integral_le_lintegral_enorm _).trans
  rw [restrict_Ioc_eq_restrict_Icc]
  simpa only [← ofReal_norm, Real.norm_eq_abs] using!
    stab_in_quadratic_flux_lintegral_raw hA h₁s h₂s hε hu huv hvT

end EmcsfAcExtension.Local
