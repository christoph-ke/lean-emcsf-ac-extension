module

public import EmcsfAcExtension.Local.Stability.FieldDifferenceAxis
import EmcsfAcExtension.Local.Stability.FieldDifferenceForcing
import EmcsfAcExtension.Local.Stability.DifferenceMomentsMixedHardy
import EmcsfAcExtension.Local.Calculus.Normalized
import EmcsfAcExtension.Infra.Calculus.PartialsC1

/-! # Scalar field comparison before inserting radial absorption

The axis value and outgoing scalar FTC give the raw field estimate.
Only the actual scalar partials are integrated in the exact identity;
singular radial weights occur inside nonnegative majorants.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The scalar difference is controlled by the vertex difference,
outgoing derivative distance, weighted radial difference and `5120AεG`.
All numerical coefficients are universal and all envelope dependence is
explicit, before all other parameters and the pair. -/
theorem stab_field_difference_raw
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : ε ^ 2 ≤ 1 / 4)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    ENNReal.ofReal ‖S₁.phi u v - S₂.phi u v‖ ≤
      ENNReal.ofReal ‖h₁ 0 - h₂ 0‖ + jDist T S₁ S₂ +
      (∫⁻ s in Icc u T, ENNReal.ofReal (S₁.lam u s / S₁.r u s *
        ‖S₁.theta u s / (S₁.lam u s : ℂ) - S₂.theta u s / (S₂.lam u s : ℂ)‖)) +
      ENNReal.ofReal (5120 * A * ε * (geomDist T S₁ S₂).toReal) := by
  let f : ℝ → ℂ := fun s => S₁.phi u s - S₂.phi u s
  let g : ℝ → ℂ := fun s => pdV (triangle 0 T) S₁.phi u s - pdV (triangle 0 T) S₂.phi u s
  let B := fun s => S₁.lam u s / S₁.r u s
  let x₁ := fun s => S₁.theta u s / (S₁.lam u s : ℂ)
  let x₂ := fun s => S₂.theta u s / (S₂.lam u s : ℂ)
  let d := fun s => B s * ‖x₁ s - x₂ s‖
  let h := fun s => B s * ‖x₂ s‖
  let G := (geomDist T S₁ S₂).toReal
  have hmap : MapsTo (fun s : ℝ => (u, s)) (Icc u v) (triangle 0 T) :=
    fun s hs => ⟨hu, hs.1, hs.2.trans hvT⟩
  have cf : ContinuousOn f (Icc u v) := by
    simpa only [f, Function.comp_def] using!
      (h₁s.c1.c1_phi.continuousOn.sub h₂s.c1.c1_phi.continuousOn).comp
        (continuous_const.prodMk continuous_id).continuousOn hmap
  have cg : ContinuousOn g (Icc u v) := by
    simpa only [g, Function.comp_def] using!
      ((continuousOn_partial_v h₁s.c1.c1_phi (uniqueDiffOn_triangle h₁s.pos)).sub
        (continuousOn_partial_v h₂s.c1.c1_phi (uniqueDiffOn_triangle h₂s.pos))).comp
          (continuous_const.prodMk continuous_id).continuousOn hmap
  have hd : ∀ s ∈ Ioo u v, HasDerivAt f (g s) s := by
    intro s hs
    exact ((hasDerivWithinAt_v_aux h₁s.c1.c1_phi hu hs.1.le (hs.2.le.trans hvT)).sub
      (hasDerivWithinAt_v_aux h₂s.c1.c1_phi hu hs.1.le (hs.2.le.trans hvT))).hasDerivAt
        (Icc_mem_nhds hs.1 (hs.2.trans_le hvT))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv cf hd
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv cg)
  have heq : f v = f u + ∫ s in u..v, g s := by rw [hi]; abel
  have cL := h₁s.c1.c1_lam.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cR := h₁s.c1.c1_r.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cX₁ : ContinuousOn x₁ (Icc u v) := (stab_out_ratio_c1 h₁s.c1).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cX₂ : ContinuousOn x₂ (Icc u v) := (stab_out_ratio_c1 h₂s.c1).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have aB : AEMeasurable B (volume.restrict (Icc u v)) :=
    (cL.aemeasurable measurableSet_Icc).div (cR.aemeasurable measurableSet_Icc)
  have ad : AEMeasurable (fun s => ENNReal.ofReal (d s)) (volume.restrict (Icc u v)) :=
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      (aB.mul ((cX₁.sub cX₂).norm.aemeasurable measurableSet_Icc))
  have hI : ENNReal.ofReal ‖∫ s in u..v, g s‖ ≤
      (∫⁻ s in Icc u T, ENNReal.ofReal (d s)) + ENNReal.ofReal (5120 * A * ε * G) := by
    rw [ofReal_norm, intervalIntegral.integral_of_le huv]
    apply (enorm_integral_le_lintegral_enorm g).trans
    rw [restrict_Ioc_eq_restrict_Icc]
    have hmaj : (∫⁻ s in Icc u v, ‖g s‖ₑ) ≤ ∫⁻ s in Icc u v,
        ENNReal.ofReal (d s) + ENNReal.ofReal (20 * G) * ENNReal.ofReal (h s) := by
      have hne : ∀ᵐ s : ℝ, s ≠ u := by simp [ae_iff, measure_singleton]
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with s hs hsu
      have hus : u < s := lt_of_le_of_ne hs.1 hsu.symm
      have hp := hmap hs
      have hB : 0 ≤ B s := div_nonneg (h₁s.c1.lam_pos (u, s) hp).le
        (h₁s.c1.r_pos (u, s) hp hus).le
      rw [← ofReal_norm]
      have hb := stab_out_scalar_partial_sub_le h₁s h₂s hu hus (hs.2.trans hvT)
      apply (ENNReal.ofReal_le_ofReal hb).trans_eq
      rw [ENNReal.ofReal_add (mul_nonneg hB (norm_nonneg _))
        (mul_nonneg (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)
          (mul_nonneg hB (norm_nonneg _))),
        ENNReal.ofReal_mul (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)]
    apply hmaj.trans
    rw [lintegral_add_left' ad, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply add_le_add
    · exact lintegral_mono_set (Icc_subset_Icc_right hvT)
    · have hm := stab_out_mixed_hardy_le h₁s h₂s hε hu (huv.trans hvT)
      apply le_trans (mul_le_mul' le_rfl
        ((lintegral_mono_set (Icc_subset_Icc_right hvT)).trans hm))
      rw [← ENNReal.ofReal_mul (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)]
      apply ENNReal.ofReal_le_ofReal
      apply le_of_eq
      ring
  change ENNReal.ofReal ‖f v‖ ≤ _
  rw [heq]
  calc
    _ ≤ ENNReal.ofReal ‖f u‖ + ENNReal.ofReal ‖∫ s in u..v, g s‖ := by
      rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (norm_add_le _ _)
    _ ≤ (ENNReal.ofReal ‖h₁ 0 - h₂ 0‖ + jDist T S₁ S₂) +
        ((∫⁻ s in Icc u T, ENNReal.ofReal (d s)) +
          ENNReal.ofReal (5120 * A * ε * G)) :=
      add_le_add (stab_axis_scalar_difference_le h₁s h₂s ⟨hu, huv.trans hvT⟩) hI
    _ = _ := by ring

end EmcsfAcExtension.Local
