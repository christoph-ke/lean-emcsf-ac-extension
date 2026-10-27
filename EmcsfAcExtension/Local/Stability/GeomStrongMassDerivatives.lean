module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Stability.GeomStrongMassForcing
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassRaw
import EmcsfAcExtension.Local.Stability.GeomStrongMassInRaw
import EmcsfAcExtension.Local.Stability.MomentsSections
import EmcsfAcExtension.Local.Calculus.Raychaudhuri
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassAlgebra

/-! # Classical mass derivative differences through the axis

The exact damped difference equation gives an L¹ derivative bound by
three times its absolute forcing. Its weighted damping term is controlled
by the proved radial mass Hardy comparison, in each own orientation.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The outgoing mass derivative difference is bounded by three times
its exact absolute forcing. The coefficient `3` is universal, with no
minimum-radius or derivative-supremum dependence. -/
theorem stab_out_mass_derivative_lintegral_le_forcing_c1
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : ε ^ 2 ≤ 1)
    {u : ℝ} (hu : u ∈ Icc 0 T) :
    (∫⁻ t in Icc u T, ‖deriv (S₁.mu u) t - deriv (S₂.mu u) t‖ₑ) ≤
      3 * ∫⁻ t in Icc u T, ENNReal.ofReal |massDifferenceForcing S₁ S₂ u t| := by
  let q := fun t => massDifferenceForcing S₁ S₂ u t
  let w := fun t => S₁.lam u t / S₁.r u t
  let x₁ := fun t => S₁.theta u t / (S₁.lam u t : ℂ)
  let x₂ := fun t => S₂.theta u t / (S₂.lam u t : ℂ)
  let d := fun t => w t * (1 + ‖x₁ t‖ ^ 2)
  have hmap : MapsTo (fun t : ℝ => (u, t)) (Icc u T) (triangle 0 T) :=
    fun t ht => ⟨hu.1, ht.1, ht.2⟩
  have aL₁ := ((h₁s.c1.c1_lam.continuousOn).comp
    (continuous_const.prodMk continuous_id).continuousOn hmap).aemeasurable (μ := volume)
        measurableSet_Icc
  have aL₂ := ((h₂s.c1.c1_lam.continuousOn).comp
    (continuous_const.prodMk continuous_id).continuousOn hmap).aemeasurable (μ := volume)
        measurableSet_Icc
  have aR₁ := ((h₁s.c1.c1_r.continuousOn).comp
    (continuous_const.prodMk continuous_id).continuousOn hmap).aemeasurable (μ := volume)
        measurableSet_Icc
  have aR₂ := ((h₂s.c1.c1_r.continuousOn).comp
    (continuous_const.prodMk continuous_id).continuousOn hmap).aemeasurable (μ := volume)
        measurableSet_Icc
  have aQ₁ := ((h₁s.c1.c1_Q.continuousOn).comp
    (continuous_const.prodMk continuous_id).continuousOn hmap).aemeasurable (μ := volume)
        measurableSet_Icc
  have aQ₂ := ((h₂s.c1.c1_Q.continuousOn).comp
    (continuous_const.prodMk continuous_id).continuousOn hmap).aemeasurable (μ := volume)
        measurableSet_Icc
  have aX₁ := ((stab_out_ratio_c1 h₁s.c1).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap).aemeasurable (μ := volume)
        measurableSet_Icc
  have aX₂ := ((stab_out_ratio_c1 h₂s.c1).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap).aemeasurable (μ := volume)
        measurableSet_Icc
  have aμ₂ := ((continuousOn_mu_aux h₂s.pos h₂s.c1).comp
    (continuous_const.prodMk continuous_id).continuousOn hmap).aemeasurable (μ := volume)
        measurableSet_Icc
  have aw₁ := aL₁.div aR₁
  have aw₂ := aL₂.div aR₂
  have ae₁ := (aQ₁.pow_const 2).div (aR₁.pow_const 2)
  have ae₂ := (aQ₂.pow_const 2).div (aR₂.pow_const 2)
  have aq : AEMeasurable q (volume.restrict (Icc u T)) :=
    (aw₁.mul ((aemeasurable_const.sub aμ₂).mul
      ((aX₁.norm.pow_const 2).sub (aX₂.norm.pow_const 2)) |>.add (ae₁.sub ae₂))).add
        ((aw₁.sub aw₂).mul (((aemeasurable_const.sub aμ₂).mul (aX₂.norm.pow_const 2)).add ae₂ |>.sub
            aμ₂))
  have aq' : AEMeasurable (fun t => ENNReal.ofReal |q t|) (volume.restrict (Icc u T)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable aq.abs
  have hpoint : ∀ᵐ t ∂volume.restrict (Icc u T),
      ‖deriv (S₁.mu u) t - deriv (S₂.mu u) t‖ₑ ≤
        ENNReal.ofReal |q t| + 2 * ENNReal.ofReal (w t * |S₁.mu u t - S₂.mu u t|) := by
    have hna : ∀ᵐ t : ℝ, t ≠ u := by simp [ae_iff, measure_singleton]
    have hnb : ∀ᵐ t : ℝ, t ≠ T := by simp [ae_iff, measure_singleton]
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hna,
      ae_restrict_of_ae hnb] with t ht hta htb
    have hleft : u < t := lt_of_le_of_ne ht.1 hta.symm
    have hright : t < T := lt_of_le_of_ne ht.2 htb
    have hp := hmap ht
    have hw : 0 ≤ w t := div_nonneg
      (h₁s.c1.lam_pos _ hp).le
      (h₁s.c1.r_pos _ hp hleft).le
    have hx := (le_add_of_nonneg_right
      (norm_nonneg (S₁.xi u t / (S₁.nu u t : ℂ)))).trans
        (h₁s.box.2 _ hp).2.2.2.2.2.1
    have hx2 : ‖x₁ t‖ ^ 2 ≤ 1 := (pow_le_pow_left₀ (norm_nonneg _) hx 2).trans hε
    have hd : 0 ≤ d t := by dsimp only [d]; positivity
    have hd2 : d t ≤ 2 * w t := by
      dsimp only [d]
      nlinarith only [mul_le_mul_of_nonneg_left hx2 hw]
    have hh₁ := (Stab.outgoing_mu_derivative_identity
      h₁s.c1 hu.1 hleft hright.le).hasDerivAt
        (Icc_mem_nhds hleft hright)
    have hh₂ := (Stab.outgoing_mu_derivative_identity
      h₂s.c1 hu.1 hleft hright.le).hasDerivAt
        (Icc_mem_nhds hleft hright)
    have heq : deriv (S₁.mu u) t - deriv (S₂.mu u) t =
        (q t - d t * (S₁.mu u t - S₂.mu u t)) := by
      rw [hh₁.deriv, hh₂.deriv]
      dsimp only [q, d, w, x₁, massDifferenceForcing]
      ring
    rw [← ofReal_norm, Real.norm_eq_abs, heq]
    have hb : |q t - d t * (S₁.mu u t - S₂.mu u t)| ≤
        |q t| + 2 * (w t * |S₁.mu u t - S₂.mu u t|) := by
      apply (abs_sub _ _).trans
      rw [abs_mul, abs_of_nonneg hd]
      have hh := mul_le_mul_of_nonneg_right hd2 (abs_nonneg (S₁.mu u t - S₂.mu u t))
      linarith only [hh]
    apply (ENNReal.ofReal_le_ofReal hb).trans_eq
    rw [ENNReal.ofReal_add (abs_nonneg _) (by positivity),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  have hi := lintegral_mono_ae hpoint
  rw [lintegral_add_left' aq', lintegral_const_mul' 2 _ (by norm_num)] at hi
  rcases hu.2.eq_or_lt with rfl | huT
  · simp
  · have hraw := (stab_out_mass_difference_raw h₁s h₂s hu.1 huT le_rfl).2
    rw [restrict_Ioc_eq_restrict_Icc] at hraw
    apply (hi.trans (add_le_add le_rfl (mul_le_mul' le_rfl hraw))).trans_eq
    ring

/-- The incoming mass derivative difference is bounded by three times
its exact absolute forcing. The coefficient `3` is universal, with no
minimum-radius or derivative-supremum dependence. -/
theorem stab_in_mass_derivative_lintegral_le_forcing_c1
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : ε ^ 2 ≤ 1)
    {v : ℝ} (hv : v ∈ Icc 0 T) :
    (∫⁻ t in Icc 0 v, ‖deriv (fun s => S₁.mu s v) t - deriv (fun s => S₂.mu s v) t‖ₑ) ≤
      3 * ∫⁻ t in Icc 0 v, ENNReal.ofReal |massDifferenceForcingIn S₁ S₂ t v| := by
  let q := fun t => massDifferenceForcingIn S₁ S₂ t v
  let w := fun t => -S₁.nu t v / S₁.r t v
  let x₁ := fun t => S₁.xi t v / (S₁.nu t v : ℂ)
  let x₂ := fun t => S₂.xi t v / (S₂.nu t v : ℂ)
  let d := fun t => w t * (1 + ‖x₁ t‖ ^ 2)
  have hmap : MapsTo (fun t : ℝ => (t, v)) (Icc 0 v) (triangle 0 T) :=
    fun t ht => ⟨ht.1, ht.2, hv.2⟩
  have aL₁ := ((h₁s.c1.c1_nu.continuousOn.neg).comp
    (continuous_id.prodMk continuous_const).continuousOn hmap).aemeasurable (μ := volume)
        measurableSet_Icc
  have aL₂ := ((h₂s.c1.c1_nu.continuousOn.neg).comp
    (continuous_id.prodMk continuous_const).continuousOn hmap).aemeasurable (μ := volume)
        measurableSet_Icc
  have aR₁ := ((h₁s.c1.c1_r.continuousOn).comp
    (continuous_id.prodMk continuous_const).continuousOn hmap).aemeasurable (μ := volume)
        measurableSet_Icc
  have aR₂ := ((h₂s.c1.c1_r.continuousOn).comp
    (continuous_id.prodMk continuous_const).continuousOn hmap).aemeasurable (μ := volume)
        measurableSet_Icc
  have aQ₁ := ((h₁s.c1.c1_Q.continuousOn).comp
    (continuous_id.prodMk continuous_const).continuousOn hmap).aemeasurable (μ := volume)
        measurableSet_Icc
  have aQ₂ := ((h₂s.c1.c1_Q.continuousOn).comp
    (continuous_id.prodMk continuous_const).continuousOn hmap).aemeasurable (μ := volume)
        measurableSet_Icc
  have aX₁ := ((stab_in_ratio_c1 h₁s.c1).continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn hmap).aemeasurable (μ := volume)
        measurableSet_Icc
  have aX₂ := ((stab_in_ratio_c1 h₂s.c1).continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn hmap).aemeasurable (μ := volume)
        measurableSet_Icc
  have aμ₂ := ((continuousOn_mu_aux h₂s.pos h₂s.c1).comp
    (continuous_id.prodMk continuous_const).continuousOn hmap).aemeasurable (μ := volume)
        measurableSet_Icc
  have aw₁ := aL₁.div aR₁
  have aw₂ := aL₂.div aR₂
  have ae₁ := (aQ₁.pow_const 2).div (aR₁.pow_const 2)
  have ae₂ := (aQ₂.pow_const 2).div (aR₂.pow_const 2)
  have aq : AEMeasurable q (volume.restrict (Icc 0 v)) :=
    (aw₁.mul ((aemeasurable_const.sub aμ₂).mul
      ((aX₁.norm.pow_const 2).sub (aX₂.norm.pow_const 2)) |>.add (ae₁.sub ae₂))).add
        ((aw₁.sub aw₂).mul (((aemeasurable_const.sub aμ₂).mul (aX₂.norm.pow_const 2)).add ae₂ |>.sub
            aμ₂))
  have aq' : AEMeasurable (fun t => ENNReal.ofReal |q t|) (volume.restrict (Icc 0 v)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable aq.abs
  have hpoint : ∀ᵐ t ∂volume.restrict (Icc 0 v),
      ‖deriv (fun s => S₁.mu s v) t - deriv (fun s => S₂.mu s v) t‖ₑ ≤
        ENNReal.ofReal |q t| + 2 * ENNReal.ofReal (w t * |S₁.mu t v - S₂.mu t v|) := by
    have hna : ∀ᵐ t : ℝ, t ≠ 0 := by simp [ae_iff, measure_singleton]
    have hnb : ∀ᵐ t : ℝ, t ≠ v := by simp [ae_iff, measure_singleton]
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hna,
      ae_restrict_of_ae hnb] with t ht hta htb
    have hleft : 0 < t := lt_of_le_of_ne ht.1 hta.symm
    have hright : t < v := lt_of_le_of_ne ht.2 htb
    have hp := hmap ht
    have hw : 0 ≤ w t := div_nonneg
      (neg_pos.mpr (h₁s.c1.nu_neg _ hp)).le
      (h₁s.c1.r_pos _ hp hright).le
    have hx := (le_add_of_nonneg_left
      (norm_nonneg (S₁.theta t v / (S₁.lam t v : ℂ)))).trans
        (h₁s.box.2 _ hp).2.2.2.2.2.1
    have hx2 : ‖x₁ t‖ ^ 2 ≤ 1 := (pow_le_pow_left₀ (norm_nonneg _) hx 2).trans hε
    have hd : 0 ≤ d t := by dsimp only [d]; positivity
    have hd2 : d t ≤ 2 * w t := by
      dsimp only [d]
      nlinarith only [mul_le_mul_of_nonneg_left hx2 hw]
    have hh₁ := (Stab.incoming_mu_derivative_identity_c1
      h₁s.c1 hleft.le hright hv.2).hasDerivAt
        (Icc_mem_nhds hleft hright)
    have hh₂ := (Stab.incoming_mu_derivative_identity_c1
      h₂s.c1 hleft.le hright hv.2).hasDerivAt
        (Icc_mem_nhds hleft hright)
    have heq : deriv (fun s => S₁.mu s v) t - deriv (fun s => S₂.mu s v) t =
        -(q t - d t * (S₁.mu t v - S₂.mu t v)) := by
      rw [hh₁.deriv, hh₂.deriv]
      dsimp only [q, d, w, x₁, massDifferenceForcingIn]
      ring
    rw [← ofReal_norm, Real.norm_eq_abs, heq, abs_neg]
    have hb : |q t - d t * (S₁.mu t v - S₂.mu t v)| ≤
        |q t| + 2 * (w t * |S₁.mu t v - S₂.mu t v|) := by
      apply (abs_sub _ _).trans
      rw [abs_mul, abs_of_nonneg hd]
      have hh := mul_le_mul_of_nonneg_right hd2 (abs_nonneg (S₁.mu t v - S₂.mu t v))
      linarith only [hh]
    apply (ENNReal.ofReal_le_ofReal hb).trans_eq
    rw [ENNReal.ofReal_add (abs_nonneg _) (by positivity),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  have hi := lintegral_mono_ae hpoint
  rw [lintegral_add_left' aq', lintegral_const_mul' 2 _ (by norm_num)] at hi
  rcases hv.1.eq_or_lt with rfl | hv0
  · simp
  · have hraw := stab_in_mass_difference_raw h₁s h₂s le_rfl hv0 hv.2
    apply (hi.trans (add_le_add le_rfl (mul_le_mul' le_rfl hraw))).trans_eq
    ring

/-- [internal]
The smooth-input local estimate for
`restart-sec-bv-stability-independent#mass-derivatives-strong`.
Both ordinary characteristic mass-ratio derivatives are compared strongly
in L¹, uniformly over their sections. Threshold and constant depend only
on `A` and its uniform main constant `C₀`, before all data, field parameters,
solutions, derivative suprema and minimum radii. -/
theorem Stab.mass_derivatives_strong_of_main_lipschitz_c1
    (A C₀ : ℝ) (hA : 0 < A) (hC₀ : 0 < C₀) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        jDist T S₁ S₂ + kDist e T S₁ S₂ + geomDist T S₁ S₂ ≤
          ENNReal.ofReal (C₀ * dataDist h₁ h₂ T) →
        (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T,
          ‖deriv (S₁.mu u) v - deriv (S₂.mu u) v‖ₑ) +
        (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
          ‖deriv (fun s => S₁.mu s v) u - deriv (fun s => S₂.mu s v) u‖ₑ) ≤
            ENNReal.ofReal (C * dataDist h₁ h₂ T) := by
  obtain ⟨η, C, hη, hC, hForcing⟩ :=
    stab_mass_forcing_difference_of_main_lipschitz A C₀ hA hC₀
  refine ⟨min η (1 / 4), 3 * C, lt_min hη (by norm_num), by positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall hmain
  have hσ : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hε : ε ^ 2 ≤ 1 := by
    have hh := ((le_add_of_nonneg_right hσ).trans hsmall).trans (min_le_right _ _)
    linarith only [hh]
  have hq := hForcing T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
    (hsmall.trans (min_le_left _ _)) hmain
  have ho : (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T,
      ‖deriv (S₁.mu u) v - deriv (S₂.mu u) v‖ₑ) ≤
      3 * (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T,
        ENNReal.ofReal |massDifferenceForcing S₁ S₂ u v|) := by
    apply iSup₂_le
    intro u hu
    exact (stab_out_mass_derivative_lintegral_le_forcing_c1 h₁s h₂s hε hu).trans
      (mul_le_mul' le_rfl (le_iSup₂_of_le u hu le_rfl))
  have hi : (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
      ‖deriv (fun s => S₁.mu s v) u - deriv (fun s => S₂.mu s v) u‖ₑ) ≤
      3 * (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
        ENNReal.ofReal |massDifferenceForcingIn S₁ S₂ u v|) := by
    apply iSup₂_le
    intro v hv
    exact (stab_in_mass_derivative_lintegral_le_forcing_c1 h₁s h₂s hε hv).trans
      (mul_le_mul' le_rfl (le_iSup₂_of_le v hv le_rfl))
  apply (add_le_add ho hi).trans
  rw [← mul_add]
  apply (mul_le_mul' le_rfl hq).trans_eq
  rw [← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

end EmcsfAcExtension.Local
