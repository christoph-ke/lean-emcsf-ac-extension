module

public import EmcsfAcExtension.Local.Stability.W11Derivatives
import EmcsfAcExtension.Local.Stability.MomentsFieldMeasurable
import EmcsfAcExtension.Local.Stability.AssemblyMoments

/-! # Integrated characteristic derivative differences

The cubic reconstruction is integrated in the correct orientation before
closing the main comparison. All singular terms retain their Hardy weights.
The axis is removed only as a singleton of zero Lebesgue measure.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem four_term_integral_aux {μ : Measure ℝ}
    {f a b c d : ℝ → ℝ} {A B C D : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ha : AEMeasurable a μ) (hb : AEMeasurable b μ) (hc : AEMeasurable c μ)
    (h : ∀ᵐ t ∂μ, 0 ≤ a t ∧ 0 ≤ b t ∧ 0 ≤ c t ∧ 0 ≤ d t ∧
      f t ≤ A * a t + B * b t + C * c t + D * d t) :
    (∫⁻ t, ENNReal.ofReal (f t) ∂μ) ≤
      ENNReal.ofReal A * (∫⁻ t, ENNReal.ofReal (a t) ∂μ) +
      ENNReal.ofReal B * (∫⁻ t, ENNReal.ofReal (b t) ∂μ) +
      ENNReal.ofReal C * (∫⁻ t, ENNReal.ofReal (c t) ∂μ) +
      ENNReal.ofReal D * (∫⁻ t, ENNReal.ofReal (d t) ∂μ) := by
  have ha' : AEMeasurable (fun t => ENNReal.ofReal A * ENNReal.ofReal (a t)) μ :=
    (ENNReal.measurable_ofReal.comp_aemeasurable ha).const_mul _
  have hb' : AEMeasurable (fun t => ENNReal.ofReal B * ENNReal.ofReal (b t)) μ :=
    (ENNReal.measurable_ofReal.comp_aemeasurable hb).const_mul _
  have hc' : AEMeasurable (fun t => ENNReal.ofReal C * ENNReal.ofReal (c t)) μ :=
    (ENNReal.measurable_ofReal.comp_aemeasurable hc).const_mul _
  apply (lintegral_mono_ae (show ∀ᵐ t ∂μ, ENNReal.ofReal (f t) ≤
      ENNReal.ofReal A * ENNReal.ofReal (a t) +
      ENNReal.ofReal B * ENNReal.ofReal (b t) +
      ENNReal.ofReal C * ENNReal.ofReal (c t) +
      ENNReal.ofReal D * ENNReal.ofReal (d t) from by
    filter_upwards [h] with t ht
    rcases ht with ⟨ha0, hb0, hc0, hd0, ht⟩
    apply (ENNReal.ofReal_le_ofReal ht).trans_eq
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul hA, ENNReal.ofReal_mul hB,
      ENNReal.ofReal_mul hC, ENNReal.ofReal_mul hD])).trans_eq
  have hab : AEMeasurable (fun t => ENNReal.ofReal A * ENNReal.ofReal (a t) +
      ENNReal.ofReal B * ENNReal.ofReal (b t)) μ := ha'.add hb'
  have habc : AEMeasurable (fun t => ENNReal.ofReal A * ENNReal.ofReal (a t) +
      ENNReal.ofReal B * ENNReal.ofReal (b t) + ENNReal.ofReal C * ENNReal.ofReal (c t)) μ :=
    hab.add hc'
  rw [lintegral_add_left' habc, lintegral_add_left' hab, lintegral_add_left' ha']
  repeat rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Integrated outgoing reconstruction difference, with universal coefficients
`4`, `16`, `3`, `20`. The mass distance and two Hardy budgets are explicit;
there is no dependence on a minimum radius or derivative supremum. -/
theorem stab_out_derivative_difference_lintegral_raw
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) {u : ℝ}
    (hu : 0 ≤ u) (_hvT : u ≤ T) :
    (∫⁻ t in Icc u T, ‖pdV (triangle 0 T) S₁.a u t - pdV (triangle 0 T) S₂.a u t‖ₑ) ≤
      4 * jDist T S₁ S₂ +
      ENNReal.ofReal (16 * (supDist T S₁.mu S₂.mu).toReal) *
        (∫⁻ t in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S₂) t) +
      ENNReal.ofReal (3 * ε ^ 2) * (∫⁻ t in Icc u T, ENNReal.ofReal
        (S₁.lam u t / S₁.r u t * ‖S₁.theta u t / (S₁.lam u t : ℂ) - S₂.theta u t / (S₂.lam u t :
            ℂ)‖)) +
      ENNReal.ofReal (20 * (geomDist T S₁ S₂).toReal * ε ^ 2) *
        (∫⁻ t in Icc u T, ENNReal.ofReal (S₁.lam u t / S₁.r u t * ‖S₂.theta u t / (S₂.lam u t :
            ℂ)‖)) := by
  let a := fun t => ‖jC1 (triangle 0 T) S₁ u t - jC1 (triangle 0 T) S₂ u t‖
  let b := fun t => ‖jC1 (triangle 0 T) S₂ u t‖
  let c := fun t => S₁.lam u t / S₁.r u t * ‖S₁.theta u t / (S₁.lam u t : ℂ) - S₂.theta u t /
      (S₂.lam u t : ℂ)‖
  let d := fun t => S₁.lam u t / S₁.r u t * ‖S₂.theta u t / (S₂.lam u t : ℂ)‖
  have hmap : MapsTo (fun t : ℝ => (u, t)) (Icc u T) (triangle 0 T) :=
    fun t ht => ⟨hu, ht.1, ht.2⟩
  have hj₁ : AEMeasurable (fun t => jC1 (triangle 0 T) S₁ u t) (volume.restrict (Icc u T)) := by
    apply ((stab_jC1_borel h₁s).comp (measurable_const.prodMk measurable_id)).aemeasurable.congr
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact indicator_of_mem (hmap ht) _
  have hj₂ : AEMeasurable (fun t => jC1 (triangle 0 T) S₂ u t) (volume.restrict (Icc u T)) := by
    apply ((stab_jC1_borel h₂s).comp (measurable_const.prodMk measurable_id)).aemeasurable.congr
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact indicator_of_mem (hmap ht) _
  have cX₁ := (stab_out_ratio_c1 h₁s.c1).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cX₂ := (stab_out_ratio_c1 h₂s.c1).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cL := h₁s.c1.c1_lam.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cR := h₁s.c1.c1_r.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have hc : AEMeasurable c (volume.restrict (Icc u T)) :=
    (cL.aemeasurable measurableSet_Icc |>.div (cR.aemeasurable measurableSet_Icc)).mul
      ((cX₁.sub cX₂).norm.aemeasurable measurableSet_Icc)
  have hpoint : ∀ᵐ t ∂volume.restrict (Icc u T),
      0 ≤ a t ∧ 0 ≤ b t ∧ 0 ≤ c t ∧ 0 ≤ d t ∧
      ‖pdV (triangle 0 T) S₁.a u t - pdV (triangle 0 T) S₂.a u t‖ ≤
        4 * a t + (16 * (supDist T S₁.mu S₂.mu).toReal) * b t +
        (3 * ε ^ 2) * c t + (20 * (geomDist T S₁ S₂).toReal * ε ^ 2) * d t := by
    have hn : ∀ᵐ t : ℝ, t ≠ u := by simp [ae_iff, measure_singleton]
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hn] with t ht htn
    have huv := lt_of_le_of_ne ht.1 htn.symm
    have hw : 0 ≤ S₁.lam u t / S₁.r u t := div_nonneg (h₁s.c1.lam_pos _ (hmap ht)).le
      (h₁s.c1.r_pos _ (hmap ht) huv).le
    exact ⟨norm_nonneg _, norm_nonneg _, mul_nonneg hw (norm_nonneg _),
      mul_nonneg hw (norm_nonneg _),
      stab_out_derivative_difference_pointwise h₁s h₂s hu huv ht.2⟩
  have hraw := four_term_integral_aux (by norm_num : (0 : ℝ) ≤ 4)
    (by positivity : 0 ≤ 16 * (supDist T S₁.mu S₂.mu).toReal)
    (by positivity : 0 ≤ 3 * ε ^ 2)
    (by positivity : 0 ≤ 20 * (geomDist T S₁ S₂).toReal * ε ^ 2)
    (hj₁.sub hj₂ |>.norm) hj₂.norm hc hpoint
  have hj : (∫⁻ t in Icc u T, ENNReal.ofReal (a t)) ≤ jDist T S₁ S₂ := by
    apply (setLIntegral_mono' measurableSet_Icc (fun t ht => ?_)).trans
      (lintegral_mono_set (Icc_subset_Icc_left hu))
    rw [ofReal_norm]
    exact enorm_le_normEnvelope
      (fun x y => jC1 (triangle 0 T) S₁ x y - jC1 (triangle 0 T) S₂ x y) ⟨hu, ht.1⟩
  have hb : (∫⁻ t in Icc u T, ENNReal.ofReal (b t)) ≤
      ∫⁻ t in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S₂) t := by
    apply (setLIntegral_mono' measurableSet_Icc (fun t ht => ?_)).trans
      (lintegral_mono_set (Icc_subset_Icc_left hu))
    rw [ofReal_norm]
    exact enorm_le_normEnvelope (jC1 (triangle 0 T) S₂) ⟨hu, ht.1⟩
  have hh := hraw.trans (add_le_add (add_le_add (add_le_add
    (mul_le_mul' le_rfl hj) (mul_le_mul' le_rfl hb)) le_rfl) le_rfl)
  simpa only [ofReal_norm, ENNReal.ofReal_ofNat] using hh

/-- Integrated incoming reconstruction difference, with universal coefficients
`4`, `16`, `3`, `20`. The mass distance and two Hardy budgets are explicit;
there is no dependence on a minimum radius or derivative supremum. -/
theorem stab_in_derivative_difference_lintegral_raw
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) {v : ℝ}
    (_hu : 0 ≤ v) (hvT : v ≤ T) :
    (∫⁻ t in Icc 0 v, ‖(pdU (triangle 0 T) S₁.b t v + Complex.I * e * S₁.A t v * S₁.b t v) - (pdU
        (triangle 0 T) S₂.b t v + Complex.I * e * S₂.A t v * S₂.b t v)‖ₑ) ≤
      4 * kDist e T S₁ S₂ +
      ENNReal.ofReal (16 * (supDist T S₁.mu S₂.mu).toReal) *
        (∫⁻ t in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S₂) t) +
      ENNReal.ofReal (3 * ε ^ 2) * (∫⁻ t in Icc 0 v, ENNReal.ofReal
        (-S₁.nu t v / S₁.r t v * ‖S₁.xi t v / (S₁.nu t v : ℂ) - S₂.xi t v / (S₂.nu t v : ℂ)‖)) +
      ENNReal.ofReal (20 * (geomDist T S₁ S₂).toReal * ε ^ 2) *
        (∫⁻ t in Icc 0 v, ENNReal.ofReal (-S₁.nu t v / S₁.r t v * ‖S₂.xi t v / (S₂.nu t v : ℂ)‖)) :=
            by
  let a := fun t => ‖kC1 e (triangle 0 T) S₁ t v - kC1 e (triangle 0 T) S₂ t v‖
  let b := fun t => ‖kC1 e (triangle 0 T) S₂ t v‖
  let c := fun t => -S₁.nu t v / S₁.r t v * ‖S₁.xi t v / (S₁.nu t v : ℂ) - S₂.xi t v / (S₂.nu t v :
      ℂ)‖
  let d := fun t => -S₁.nu t v / S₁.r t v * ‖S₂.xi t v / (S₂.nu t v : ℂ)‖
  have hmap : MapsTo (fun t : ℝ => (t, v)) (Icc 0 v) (triangle 0 T) :=
    fun t ht => ⟨ht.1, ht.2, hvT⟩
  have hj₁ : AEMeasurable (fun t => kC1 e (triangle 0 T) S₁ t v) (volume.restrict (Icc 0 v)) := by
    apply ((stab_kC1_borel h₁s).comp (measurable_id.prodMk measurable_const)).aemeasurable.congr
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact indicator_of_mem (hmap ht) _
  have hj₂ : AEMeasurable (fun t => kC1 e (triangle 0 T) S₂ t v) (volume.restrict (Icc 0 v)) := by
    apply ((stab_kC1_borel h₂s).comp (measurable_id.prodMk measurable_const)).aemeasurable.congr
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact indicator_of_mem (hmap ht) _
  have cX₁ := (stab_in_ratio_c1 h₁s.c1).continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn hmap
  have cX₂ := (stab_in_ratio_c1 h₂s.c1).continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn hmap
  have cL := h₁s.c1.c1_nu.continuousOn.neg.comp
    (continuous_id.prodMk continuous_const).continuousOn hmap
  have cR := h₁s.c1.c1_r.continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn hmap
  have hc : AEMeasurable c (volume.restrict (Icc 0 v)) :=
    (cL.aemeasurable measurableSet_Icc |>.div (cR.aemeasurable measurableSet_Icc)).mul
      ((cX₁.sub cX₂).norm.aemeasurable measurableSet_Icc)
  have hpoint : ∀ᵐ t ∂volume.restrict (Icc 0 v),
      0 ≤ a t ∧ 0 ≤ b t ∧ 0 ≤ c t ∧ 0 ≤ d t ∧
      ‖(pdU (triangle 0 T) S₁.b t v + Complex.I * e * S₁.A t v * S₁.b t v) - (pdU (triangle 0 T)
          S₂.b t v + Complex.I * e * S₂.A t v * S₂.b t v)‖ ≤
        4 * a t + (16 * (supDist T S₁.mu S₂.mu).toReal) * b t +
        (3 * ε ^ 2) * c t + (20 * (geomDist T S₁ S₂).toReal * ε ^ 2) * d t := by
    have hn : ∀ᵐ t : ℝ, t ≠ v := by simp [ae_iff, measure_singleton]
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hn] with t ht htn
    have huv := lt_of_le_of_ne ht.2 htn
    have hw : 0 ≤ -S₁.nu t v / S₁.r t v := div_nonneg (neg_pos.mpr (h₁s.c1.nu_neg _ (hmap ht))).le
      (h₁s.c1.r_pos _ (hmap ht) huv).le
    exact ⟨norm_nonneg _, norm_nonneg _, mul_nonneg hw (norm_nonneg _),
      mul_nonneg hw (norm_nonneg _),
      stab_in_derivative_difference_pointwise h₁s h₂s ht.1 huv hvT⟩
  have hraw := four_term_integral_aux (by norm_num : (0 : ℝ) ≤ 4)
    (by positivity : 0 ≤ 16 * (supDist T S₁.mu S₂.mu).toReal)
    (by positivity : 0 ≤ 3 * ε ^ 2)
    (by positivity : 0 ≤ 20 * (geomDist T S₁ S₂).toReal * ε ^ 2)
    (hj₁.sub hj₂ |>.norm) hj₂.norm hc hpoint
  have hj : (∫⁻ t in Icc 0 v, ENNReal.ofReal (a t)) ≤ kDist e T S₁ S₂ := by
    apply (setLIntegral_mono' measurableSet_Icc (fun t ht => ?_)).trans
      (lintegral_mono_set (Icc_subset_Icc_right hvT))
    rw [ofReal_norm]
    exact le_iSup₂_of_le v ⟨ht.2, hvT⟩ le_rfl
  have hb : (∫⁻ t in Icc 0 v, ENNReal.ofReal (b t)) ≤
      ∫⁻ t in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S₂) t := by
    apply (setLIntegral_mono' measurableSet_Icc (fun t ht => ?_)).trans
      (lintegral_mono_set (Icc_subset_Icc_right hvT))
    rw [ofReal_norm]
    exact le_iSup₂_of_le v ⟨ht.2, hvT⟩ le_rfl
  have hh := hraw.trans (add_le_add (add_le_add (add_le_add
    (mul_le_mul' le_rfl hj) (mul_le_mul' le_rfl hb)) le_rfl) le_rfl)
  simpa only [ofReal_norm, ENNReal.ofReal_ofNat] using hh

end EmcsfAcExtension.Local
