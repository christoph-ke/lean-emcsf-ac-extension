module

public import EmcsfAcExtension.Local.Stability.FluxDifference
import EmcsfAcExtension.Local.Stability.FluxDifferenceRegularity
import EmcsfAcExtension.Local.Stability.GeometryDifferenceWeights
import EmcsfAcExtension.Local.Stability.MomentsQuadratic
import EmcsfAcExtension.Local.Calculus.RadialIdentity

/-! # Absolute integral of the outgoing optical flux difference

The difference of the exact optical exponents is controlled by the
weighted radial difference and the individual quadratic Hardy budget.
Mass feedback is retained through the radial difference term.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem integral_difference_le_aux {f g d h : ℝ → ℝ} {a b c k : ℝ}
    (hab : a ≤ b) (hc : 0 ≤ c) (hk : 0 ≤ k)
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b)
    (hd : AEMeasurable (fun s => ENNReal.ofReal (d s)) (volume.restrict (Icc a b)))
    (hpoint : ∀ᵐ s ∂volume.restrict (Icc a b),
      0 ≤ d s ∧ 0 ≤ h s ∧ |f s - g s| ≤ c * d s + k * h s) :
    ENNReal.ofReal |(∫ s in a..b, f s) - ∫ s in a..b, g s| ≤
      ENNReal.ofReal c * (∫⁻ s in Icc a b, ENNReal.ofReal (d s)) +
      ENNReal.ofReal k * (∫⁻ s in Icc a b, ENNReal.ofReal (h s)) := by
  rw [← intervalIntegral.integral_sub hf hg, ← Real.norm_eq_abs, ofReal_norm,
    intervalIntegral.integral_of_le hab]
  apply (enorm_integral_le_lintegral_enorm (fun s => f s - g s)).trans
  rw [restrict_Ioc_eq_restrict_Icc]
  have hm : (∫⁻ s in Icc a b, ‖f s - g s‖ₑ) ≤
      ∫⁻ s in Icc a b, ENNReal.ofReal c * ENNReal.ofReal (d s) +
        ENNReal.ofReal k * ENNReal.ofReal (h s) := by
    apply lintegral_mono_ae
    filter_upwards [hpoint] with s hs
    rw [← ofReal_norm, Real.norm_eq_abs]
    apply (ENNReal.ofReal_le_ofReal hs.2.2).trans_eq
    rw [ENNReal.ofReal_add (mul_nonneg hc hs.1) (mul_nonneg hk hs.2.1),
      ENNReal.ofReal_mul hc, ENNReal.ofReal_mul hk]
  apply hm.trans_eq
  rw [lintegral_add_left' (hd.const_mul _),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The outgoing optical exponent difference is at most `2ε` times
the weighted radial difference plus `5120 A ε² G`. All numerical
coefficients are universal, before the pair and all parameters; only
the displayed factor `A` carries envelope dependence. -/
theorem stab_out_optical_exponent_sub_le
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (_hA : 0 < A) (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : ε ^ 2 ≤ 1 / 4)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ENNReal.ofReal |(∫ s in u..v, S₁.lam u s / S₁.r u s *
        ‖S₁.theta u s / (S₁.lam u s : ℂ)‖ ^ 2) -
      (∫ s in u..v, S₂.lam u s / S₂.r u s *
        ‖S₂.theta u s / (S₂.lam u s : ℂ)‖ ^ 2)| ≤
      ENNReal.ofReal (2 * ε) * (∫⁻ s in Icc u T,
        ENNReal.ofReal (S₁.lam u s / S₁.r u s *
          ‖S₁.theta u s / (S₁.lam u s : ℂ) - S₂.theta u s / (S₂.lam u s : ℂ)‖)) +
      ENNReal.ofReal (5120 * A * ε ^ 2 * (geomDist T S₁ S₂).toReal) := by
  let B := fun s => S₁.lam u s / S₁.r u s
  let x₁ := fun s => S₁.theta u s / (S₁.lam u s : ℂ)
  let x₂ := fun s => S₂.theta u s / (S₂.lam u s : ℂ)
  let d := fun s => B s * ‖x₁ s - x₂ s‖
  let h := fun s => B s * ‖x₂ s‖ ^ 2
  let G := (geomDist T S₁ S₂).toReal
  have huT := huv.le.trans hvT
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi u u / (S₂.nu u u : ℂ)))).trans
      (h₂s.box.2 (u, u) ⟨hu, le_rfl, huT⟩).2.2.2.2.2.1)
  have hmap : MapsTo (fun s : ℝ => (u, s)) (Icc u T) (triangle 0 T) :=
    fun s hs => ⟨hu, hs.1, hs.2⟩
  have cL := h₁s.c1.c1_lam.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cR := h₁s.c1.c1_r.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cX₁ : ContinuousOn x₁ (Icc u T) := (stab_out_ratio_c1 h₁s.c1).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cX₂ : ContinuousOn x₂ (Icc u T) := (stab_out_ratio_c1 h₂s.c1).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have aB : AEMeasurable B (volume.restrict (Icc u T)) :=
    (cL.aemeasurable measurableSet_Icc).div (cR.aemeasurable measurableSet_Icc)
  have ad : AEMeasurable (fun s => ENNReal.ofReal (d s)) (volume.restrict (Icc u T)) :=
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      (aB.mul ((cX₁.sub cX₂).norm.aemeasurable measurableSet_Icc))
  have cF₁ := (stab_out_quadratic_flux_continuous h₁s).comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cF₂ := (stab_out_quadratic_flux_continuous h₂s).comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have hF₁ := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv.le
    (cF₁.mono (Icc_subset_Icc_right hvT))
  have hF₂ := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv.le
    (cF₂.mono (Icc_subset_Icc_right hvT))
  have hpoint : ∀ᵐ s ∂volume.restrict (Icc u v),
      0 ≤ d s ∧ 0 ≤ h s ∧
      |S₁.lam u s / S₁.r u s * ‖x₁ s‖ ^ 2 -
        S₂.lam u s / S₂.r u s * ‖x₂ s‖ ^ 2| ≤ (2 * ε) * d s + (20 * G) * h s := by
    have hne : ∀ᵐ s : ℝ, s ≠ u := by simp [ae_iff, measure_singleton]
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with s hs hsu
    have hus : u < s := lt_of_le_of_ne hs.1 hsu.symm
    have hp : (u, s) ∈ triangle 0 T := ⟨hu, hus.le, hs.2.trans hvT⟩
    have hB : 0 ≤ B s := div_nonneg (h₁s.c1.lam_pos (u, s) hp).le
      (h₁s.c1.r_pos (u, s) hp hus).le
    exact ⟨mul_nonneg hB (norm_nonneg _), mul_nonneg hB (sq_nonneg _),
      stab_out_quadratic_flux_sub_le h₁s h₂s hu hus (hs.2.trans hvT)⟩
  have hi := integral_difference_le_aux huv.le (mul_nonneg (by norm_num) hε0)
    (mul_nonneg (by norm_num) ENNReal.toReal_nonneg) hF₁ hF₂
    (ad.mono_measure (Measure.restrict_mono (Icc_subset_Icc_right hvT) le_rfl)) hpoint
  have hquad : (∫⁻ s in Icc u T, ENNReal.ofReal (h s)) ≤
      ENNReal.ofReal (256 * A * ε ^ 2) := by
    have hq := stab_out_hardy_quadratic_of_identity h₂s (fun u v hu huv hvT => by
      apply (stab_out_reconstruction h₂s.c1 hu huv hvT).congr_deriv
      simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_sub,
        Complex.ofReal_one, Complex.ofReal_pow]) hε hu huT
    rw [restrict_Ioc_eq_restrict_Icc] at hq
    have hcost : ENNReal.ofReal ((16 / 3 : ℝ) * ε) ≤ ENNReal.ofReal (16 * ε) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by norm_num) hε0)
    have henv : (∫⁻ s in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S₂) s) ≤
        ENNReal.ofReal (A * ε) := (le_add_of_nonneg_right bot_le).trans h₂s.env
    have hqm := hq.trans (mul_le_mul hcost henv bot_le bot_le)
    have hmix : (∫⁻ s in Icc u T, ENNReal.ofReal (h s)) ≤
        ENNReal.ofReal 16 * ∫⁻ s in Icc u T, ENNReal.ofReal
          (S₂.lam u s / S₂.r u s * ‖x₂ s‖ ^ 2) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      have hne : ∀ᵐ s : ℝ, s ≠ u := by simp [ae_iff, measure_singleton]
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with s hs hsu
      have hus : u < s := lt_of_le_of_ne hs.1 hsu.symm
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]
      apply ENNReal.ofReal_le_ofReal
      simpa only [h, B, mul_assoc] using mul_le_mul_of_nonneg_right
        (stab_out_weight_le_sixteen h₁s h₂s hu hus hs.2) (sq_nonneg ‖x₂ s‖)
    apply hmix.trans
    apply (mul_le_mul' le_rfl hqm).trans_eq
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 16 * (16 * ε))]
    congr 1
    ring
  apply hi.trans
  apply add_le_add
  · exact mul_le_mul' le_rfl (lintegral_mono_set (Icc_subset_Icc_right hvT))
  · apply le_trans (mul_le_mul' le_rfl
      ((lintegral_mono_set (Icc_subset_Icc_right hvT)).trans hquad))
    rw [← ENNReal.ofReal_mul (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)]
    apply ENNReal.ofReal_le_ofReal
    apply le_of_eq
    ring

end EmcsfAcExtension.Local
