module

public import EmcsfAcExtension.Local.Stability.GeomStrongCrossAlgebra
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassIndividualBudget
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassMeasure
import EmcsfAcExtension.Local.Stability.GeomStrongMassInIndividualBudget
import EmcsfAcExtension.Local.Stability.GeomStrongMassInMeasure
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Integrating the cross-source comparison

All four weighted source terms are measurable even when their totalized
axis values are used. The separate oriented budgets make the estimates
uniform on complete sections.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- Integrate a cross-source product subtraction with exact coefficients.
This analytic helper introduces no integrability or finiteness premise
for the source being estimated. All numerical coefficients are universal.
-/
theorem stab_cross_source_lintegral_of_bound {μ : Measure ℝ}
    {w m₁ m₂ q₁ q₂ f : ℝ → ℝ} {B : ℝ}
    (aw : AEMeasurable w μ) (am₁ : AEMeasurable m₁ μ) (am₂ : AEMeasurable m₂ μ)
    (aq₁ : AEMeasurable q₁ μ) (aq₂ : AEMeasurable q₂ μ)
    (hw : ∀ᵐ t ∂μ, 0 ≤ w t) (hq₂ : ∀ᵐ t ∂μ, 0 ≤ q₂ t) (hB : 0 ≤ B)
    (hf : ∀ᵐ t ∂μ, |f t| ≤ 4 * w t * |m₁ t - m₂ t| +
      4 * w t * |q₁ t - q₂ t| + B * w t * (|m₂ t| + q₂ t)) :
    (∫⁻ t, ENNReal.ofReal |f t| ∂μ) ≤
      4 * (∫⁻ t, ENNReal.ofReal (w t * |m₁ t - m₂ t|) ∂μ) +
      4 * (∫⁻ t, ENNReal.ofReal (w t * |q₁ t - q₂ t|) ∂μ) +
      ENNReal.ofReal B * ((∫⁻ t, ENNReal.ofReal (w t * |m₂ t|) ∂μ) +
        ∫⁻ t, ENNReal.ofReal (w t * q₂ t) ∂μ) := by
  let F := fun t => ENNReal.ofReal (w t * |m₁ t - m₂ t|)
  let G := fun t => ENNReal.ofReal (w t * |q₁ t - q₂ t|)
  let H := fun t => ENNReal.ofReal (w t * |m₂ t|)
  let K := fun t => ENNReal.ofReal (w t * q₂ t)
  have aF : AEMeasurable F μ := ENNReal.measurable_ofReal.comp_aemeasurable
    (aw.mul (am₁.sub am₂).abs)
  have aG : AEMeasurable G μ := ENNReal.measurable_ofReal.comp_aemeasurable
    (aw.mul (aq₁.sub aq₂).abs)
  have aH : AEMeasurable H μ := ENNReal.measurable_ofReal.comp_aemeasurable (aw.mul am₂.abs)
  have hp : ∀ᵐ t ∂μ, ENNReal.ofReal |f t| ≤
      4 * F t + 4 * G t + ENNReal.ofReal B * (H t + K t) := by
    filter_upwards [hf, hw, hq₂] with t ht hwt hqt
    apply (ENNReal.ofReal_le_ofReal ht).trans_eq
    dsimp only [F, G, H, K]
    rw [show B * w t * (|m₂ t| + q₂ t) =
      B * (w t * |m₂ t| + w t * q₂ t) by ring]
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul hB, ENNReal.ofReal_add (by positivity) (by positivity)]
    rw [show 4 * w t * |m₁ t - m₂ t| = 4 * (w t * |m₁ t - m₂ t|) by ring,
      show 4 * w t * |q₁ t - q₂ t| = 4 * (w t * |q₁ t - q₂ t|) by ring,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num only [ENNReal.ofReal_ofNat]
  apply (lintegral_mono_ae hp).trans_eq
  have a4F : AEMeasurable (fun t => (4 : ℝ≥0∞) * F t) μ := aemeasurable_const.mul aF
  have a4G : AEMeasurable (fun t => (4 : ℝ≥0∞) * G t) μ := aemeasurable_const.mul aG
  rw [lintegral_add_left' (f := fun t => 4 * F t + 4 * G t)
    (g := fun t => ENNReal.ofReal B * (H t + K t)) (a4F.add a4G),
    lintegral_add_left' (f := fun t => 4 * F t) (g := fun t => 4 * G t) a4F,
    lintegral_const_mul' 4 F (by norm_num),
    lintegral_const_mul' 4 G (by norm_num),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_add_left' (f := H) (g := K) aH]


/-- The outgoing cross source has its two weighted difference costs,
plus the individual mass/electromagnetic budget. All numerical constants
are universal; the displayed `A, σ, ε, G, U` are the only dependencies. -/
theorem stab_out_cross_source_integral_c1
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (hA : 0 < A) (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : ε ^ 2 ≤ 1 / 4)
    {u : ℝ} (hu : u ∈ Icc 0 T) :
    (∫⁻ t in Icc u T, ENNReal.ofReal |S₁.rUV u t - S₂.rUV u t|) ≤
      4 * (∫⁻ t in Icc u T, ENNReal.ofReal (S₁.lam u t / S₁.r u t *
        |S₁.mu u t - S₂.mu u t|)) +
      4 * (∫⁻ t in Icc u T, ENNReal.ofReal (S₁.lam u t / S₁.r u t *
        |S₁.Q u t ^ 2 / S₁.r u t ^ 2 - S₂.Q u t ^ 2 / S₂.r u t ^ 2|)) +
      ENNReal.ofReal ((84 * (geomDist T S₁ S₂).toReal +
        16 * (supDist T S₁.mu S₂.mu).toReal) *
          (4096 * A + 544 * sigma e M T) * ε ^ 2) := by
  let w := fun t => S₁.lam u t / S₁.r u t
  let q₁ := fun t => S₁.Q u t ^ 2 / S₁.r u t ^ 2
  let q₂ := fun t => S₂.Q u t ^ 2 / S₂.r u t ^ 2
  let B := 84 * (geomDist T S₁ S₂).toReal + 16 * (supDist T S₁.mu S₂.mu).toReal
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hσ : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hmap : MapsTo (fun t : ℝ => (u, t)) (Icc u T) (triangle 0 T) :=
    fun t ht => ⟨hu.1, ht.1, ht.2⟩
  have aW : AEMeasurable w (volume.restrict (Icc u T)) :=
    ((h₁s.c1.c1_lam.continuousOn).comp
      (continuous_const.prodMk continuous_id).continuousOn hmap).aemeasurable (μ := volume)
          measurableSet_Icc |>.div
        ((h₁s.c1.c1_r.continuousOn.comp
          (continuous_const.prodMk continuous_id).continuousOn hmap).aemeasurable (μ := volume)
              measurableSet_Icc)
  have aM₁ := ((continuousOn_mu_aux h₁s.pos h₁s.c1).comp
    (continuous_const.prodMk continuous_id).continuousOn hmap).aemeasurable (μ := volume)
        measurableSet_Icc
  have aM₂ := ((continuousOn_mu_aux h₂s.pos h₂s.c1).comp
    (continuous_const.prodMk continuous_id).continuousOn hmap).aemeasurable (μ := volume)
        measurableSet_Icc
  have aQ₁ : AEMeasurable q₁ (volume.restrict (Icc u T)) :=
    (((h₁s.c1.c1_Q.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hmap).aemeasurable (μ := volume)
          measurableSet_Icc).pow_const 2).div
      (((h₁s.c1.c1_r.continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn hmap).aemeasurable (μ := volume)
            measurableSet_Icc).pow_const 2)
  have aQ₂ : AEMeasurable q₂ (volume.restrict (Icc u T)) :=
    (((h₂s.c1.c1_Q.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hmap).aemeasurable (μ := volume)
          measurableSet_Icc).pow_const 2).div
      (((h₂s.c1.c1_r.continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn hmap).aemeasurable (μ := volume)
            measurableSet_Icc).pow_const 2)
  have hn : ∀ᵐ t : ℝ, t ≠ u := by simp [ae_iff, measure_singleton]
  have hW : ∀ᵐ t ∂volume.restrict (Icc u T), 0 ≤ w t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hn] with t ht hne
    have hp := hmap ht
    have haxis := lt_of_le_of_ne ht.1 hne.symm
    exact div_nonneg (h₁s.c1.lam_pos _ hp).le (h₁s.c1.r_pos _ hp haxis).le
  have hpoint : ∀ᵐ t ∂volume.restrict (Icc u T),
      |S₁.rUV u t - S₂.rUV u t| ≤
        4 * w t * |S₁.mu u t - S₂.mu u t| +
        4 * w t * |q₁ t - q₂ t| + B * w t * (|S₂.mu u t| + q₂ t) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hn] with t ht hne
    have haxis := lt_of_le_of_ne ht.1 hne.symm
    exact (stab_cross_source_difference_le_c1 h₁s h₂s hu.1 haxis ht.2).1
  have hraw := stab_cross_source_lintegral_of_bound aW aM₁ aM₂ aQ₁ aQ₂ hW
    (ae_of_all _ (fun t => div_nonneg (sq_nonneg _) (sq_nonneg _))) hB hpoint
  have hm := stab_out_mixed_mass_le hA h₁s h₂s hε hu.1 hu.2
  have he := stab_out_mixed_em_le h₁s h₂s hu.1 hu.2
  have heq : 8 * (|e| * M * ε) ^ 2 * T ^ 2 = 32 * sigma e M T * ε ^ 2 := by
    dsimp only [sigma]
    rw [mul_pow, mul_pow, sq_abs]
    ring
  have hbudget : (∫⁻ t in Icc u T, ENNReal.ofReal (w t * |S₂.mu u t|)) +
      (∫⁻ t in Icc u T, ENNReal.ofReal (w t * q₂ t)) ≤
        ENNReal.ofReal ((4096 * A + 544 * sigma e M T) * ε ^ 2) := by
    apply (add_le_add hm he).trans_eq
    rw [heq, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  apply (hraw.trans (add_le_add le_rfl (mul_le_mul' le_rfl hbudget))).trans_eq
  rw [← ENNReal.ofReal_mul hB]
  congr 2
  dsimp only [B]
  ring

/-- The ingoing cross source has its two weighted difference costs,
plus the individual mass/electromagnetic budget. All numerical constants
are universal; the displayed `A, σ, ε, G, U` are the only dependencies. -/
theorem stab_in_cross_source_integral_c1
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (hA : 0 < A) (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : ε ^ 2 ≤ 1 / 4)
    {v : ℝ} (hv : v ∈ Icc 0 T) :
    (∫⁻ t in Icc 0 v, ENNReal.ofReal |S₁.rUV t v - S₂.rUV t v|) ≤
      4 * (∫⁻ t in Icc 0 v, ENNReal.ofReal (-S₁.nu t v / S₁.r t v *
        |S₁.mu t v - S₂.mu t v|)) +
      4 * (∫⁻ t in Icc 0 v, ENNReal.ofReal (-S₁.nu t v / S₁.r t v *
        |S₁.Q t v ^ 2 / S₁.r t v ^ 2 - S₂.Q t v ^ 2 / S₂.r t v ^ 2|)) +
      ENNReal.ofReal ((84 * (geomDist T S₁ S₂).toReal +
        16 * (supDist T S₁.mu S₂.mu).toReal) *
          (4096 * A + 544 * sigma e M T) * ε ^ 2) := by
  let w := fun t => -S₁.nu t v / S₁.r t v
  let q₁ := fun t => S₁.Q t v ^ 2 / S₁.r t v ^ 2
  let q₂ := fun t => S₂.Q t v ^ 2 / S₂.r t v ^ 2
  let B := 84 * (geomDist T S₁ S₂).toReal + 16 * (supDist T S₁.mu S₂.mu).toReal
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hσ : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hmap : MapsTo (fun t : ℝ => (t, v)) (Icc 0 v) (triangle 0 T) :=
    fun t ht => ⟨ht.1, ht.2, hv.2⟩
  have aW : AEMeasurable w (volume.restrict (Icc 0 v)) :=
    ((h₁s.c1.c1_nu.continuousOn.neg).comp
      (continuous_id.prodMk continuous_const).continuousOn hmap).aemeasurable (μ := volume)
          measurableSet_Icc |>.div
        ((h₁s.c1.c1_r.continuousOn.comp
          (continuous_id.prodMk continuous_const).continuousOn hmap).aemeasurable (μ := volume)
              measurableSet_Icc)
  have aM₁ := ((continuousOn_mu_aux h₁s.pos h₁s.c1).comp
    (continuous_id.prodMk continuous_const).continuousOn hmap).aemeasurable (μ := volume)
        measurableSet_Icc
  have aM₂ := ((continuousOn_mu_aux h₂s.pos h₂s.c1).comp
    (continuous_id.prodMk continuous_const).continuousOn hmap).aemeasurable (μ := volume)
        measurableSet_Icc
  have aQ₁ : AEMeasurable q₁ (volume.restrict (Icc 0 v)) :=
    (((h₁s.c1.c1_Q.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn hmap).aemeasurable (μ := volume)
          measurableSet_Icc).pow_const 2).div
      (((h₁s.c1.c1_r.continuousOn.comp
        (continuous_id.prodMk continuous_const).continuousOn hmap).aemeasurable (μ := volume)
            measurableSet_Icc).pow_const 2)
  have aQ₂ : AEMeasurable q₂ (volume.restrict (Icc 0 v)) :=
    (((h₂s.c1.c1_Q.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn hmap).aemeasurable (μ := volume)
          measurableSet_Icc).pow_const 2).div
      (((h₂s.c1.c1_r.continuousOn.comp
        (continuous_id.prodMk continuous_const).continuousOn hmap).aemeasurable (μ := volume)
            measurableSet_Icc).pow_const 2)
  have hn : ∀ᵐ t : ℝ, t ≠ v := by simp [ae_iff, measure_singleton]
  have hW : ∀ᵐ t ∂volume.restrict (Icc 0 v), 0 ≤ w t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hn] with t ht hne
    have hp := hmap ht
    have haxis := lt_of_le_of_ne ht.2 hne
    exact div_nonneg (neg_pos.mpr (h₁s.c1.nu_neg _ hp)).le (h₁s.c1.r_pos _ hp haxis).le
  have hpoint : ∀ᵐ t ∂volume.restrict (Icc 0 v),
      |S₁.rUV t v - S₂.rUV t v| ≤
        4 * w t * |S₁.mu t v - S₂.mu t v| +
        4 * w t * |q₁ t - q₂ t| + B * w t * (|S₂.mu t v| + q₂ t) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hn] with t ht hne
    have haxis := lt_of_le_of_ne ht.2 hne
    exact (stab_cross_source_difference_le_c1 h₁s h₂s ht.1 haxis hv.2).2
  have hraw := stab_cross_source_lintegral_of_bound aW aM₁ aM₂ aQ₁ aQ₂ hW
    (ae_of_all _ (fun t => div_nonneg (sq_nonneg _) (sq_nonneg _))) hB hpoint
  have hm := stab_in_mixed_mass_le hA h₁s h₂s hε hv.1 hv.2
  have he := stab_in_mixed_em_le h₁s h₂s hv.1 hv.2
  have heq : 8 * (|e| * M * ε) ^ 2 * T ^ 2 = 32 * sigma e M T * ε ^ 2 := by
    dsimp only [sigma]
    rw [mul_pow, mul_pow, sq_abs]
    ring
  have hbudget : (∫⁻ t in Icc 0 v, ENNReal.ofReal (w t * |S₂.mu t v|)) +
      (∫⁻ t in Icc 0 v, ENNReal.ofReal (w t * q₂ t)) ≤
        ENNReal.ofReal ((4096 * A + 544 * sigma e M T) * ε ^ 2) := by
    apply (add_le_add hm he).trans_eq
    rw [heq, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  apply (hraw.trans (add_le_add le_rfl (mul_le_mul' le_rfl hbudget))).trans_eq
  rw [← ENNReal.ofReal_mul hB]
  congr 2
  dsimp only [B]
  ring

end EmcsfAcExtension.Local
