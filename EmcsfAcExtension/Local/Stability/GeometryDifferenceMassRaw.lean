module

public import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassForcing
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassODE
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassRegularity
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassAlgebra
import EmcsfAcExtension.Local.Stability.MomentsSections
import EmcsfAcExtension.Local.Calculus.Raychaudhuri
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Raw damped normalized mass difference

Both the point and outgoing weighted estimates follow from the same
exact real equation. The forcing will be bounded separately using
the scalar Hardy and normalized charge comparisons.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The normalized mass difference has point and weighted bounds by
its exact absolute forcing, with constant `1` in each estimate. This
helper assumes no mass, charge or stability conclusion. -/
theorem stab_out_mass_difference_raw
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ENNReal.ofReal |S₁.mu u v - S₂.mu u v| ≤
        (∫⁻ t in Ioc u v, ENNReal.ofReal |massDifferenceForcing S₁ S₂ u t|) ∧
      (∫⁻ t in Ioc u v, ENNReal.ofReal
        (S₁.lam u t / S₁.r u t * |S₁.mu u t - S₂.mu u t|)) ≤
        ∫⁻ t in Ioc u v, ENNReal.ofReal |massDifferenceForcing S₁ S₂ u t| := by
  let d := fun t => S₁.lam u t / S₁.r u t *
    (1 + ‖S₁.theta u t / (S₁.lam u t : ℂ)‖ ^ 2)
  have hmap : MapsTo (fun t : ℝ => (u, t)) (Ioc u v) (triangle 0 T) :=
    fun t ht => ⟨hu, ht.1.le, ht.2.trans hvT⟩
  have cL₁ := h₁s.c1.c1_lam.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cL₂ := h₂s.c1.c1_lam.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cR₁ := h₁s.c1.c1_r.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cR₂ := h₂s.c1.c1_r.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cQ₁ := h₁s.c1.c1_Q.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cQ₂ := h₂s.c1.c1_Q.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cX₁ := (stab_out_ratio_c1 h₁s.c1).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cX₂ := (stab_out_ratio_c1 h₂s.c1).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cμ₂ := (continuousOn_mu_aux h₂s.pos h₂s.c1).comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have hr₁ : ∀ t ∈ Ioc u v, S₁.r u t ≠ 0 :=
    fun t ht => (h₁s.c1.r_pos (u, t) (hmap ht) ht.1).ne'
  have hr₂ : ∀ t ∈ Ioc u v, S₂.r u t ≠ 0 :=
    fun t ht => (h₂s.c1.r_pos (u, t) (hmap ht) ht.1).ne'
  have cw₁ := cL₁.div cR₁ hr₁
  have cw₂ := cL₂.div cR₂ hr₂
  have ce₁ := (cQ₁.pow 2).div (cR₁.pow 2) (fun t ht => pow_ne_zero 2 (hr₁ t ht))
  have ce₂ := (cQ₂.pow 2).div (cR₂.pow 2) (fun t ht => pow_ne_zero 2 (hr₂ t ht))
  have cq : ContinuousOn (massDifferenceForcing S₁ S₂ u) (Ioc u v) :=
    (cw₁.mul ((continuousOn_const.sub cμ₂).mul
      ((cX₁.norm.pow 2).sub (cX₂.norm.pow 2)) |>.add (ce₁.sub ce₂))).add
        ((cw₁.sub cw₂).mul (((continuousOn_const.sub cμ₂).mul (cX₂.norm.pow 2)).add ce₂
          |>.sub cμ₂))
  have hw : IntervalIntegrable (S₁.lam u) volume u v := by
    apply ContinuousOn.intervalIntegrable_of_Icc huv.le
    exact h₁s.c1.c1_lam.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨hu, ht.1, ht.2.trans hvT⟩)
  have hw0 : ∀ t ∈ Icc u v, 0 ≤ S₁.lam u t :=
    fun t ht => (h₁s.c1.lam_pos (u, t) ⟨hu, ht.1, ht.2.trans hvT⟩).le
  have haxis : S₁.mu u u - S₂.mu u u = 0 := by
    dsimp only [Fields.mu]
    rw [(h₁s.c1.axis u ⟨hu, le_rfl, huv.le.trans hvT⟩).1,
      (h₂s.c1.axis u ⟨hu, le_rfl, huv.le.trans hvT⟩).1, div_zero, div_zero, sub_self]
  have hd : ∀ t ∈ Ioo u v, S₁.lam u t / (∫ s in u..t, S₁.lam u s) ≤ d t := by
    intro t ht
    rw [stab_radius_out_integral h₁s hu ht.1.le (ht.2.le.trans hvT)]
    have hb : 0 ≤ S₁.lam u t / S₁.r u t := div_nonneg (hw0 t ⟨ht.1.le, ht.2.le⟩)
      (h₁s.c1.r_pos (u, t) ⟨hu, ht.1.le, ht.2.le.trans hvT⟩ ht.1).le
    dsimp only [d]
    nlinarith only [mul_nonneg hb (sq_nonneg ‖S₁.theta u t / (S₁.lam u t : ℂ)‖)]
  have hidentity : ∀ t ∈ Ioo u v,
      HasDerivWithinAt (fun s => S₁.mu u s - S₂.mu u s)
        (massDifferenceForcing S₁ S₂ u t - d t * (S₁.mu u t - S₂.mu u t)) (Icc u v) t := by
    intro t ht
    apply (((Stab.outgoing_mu_derivative_identity h₁s.c1 hu ht.1
      (ht.2.le.trans hvT)).sub (Stab.outgoing_mu_derivative_identity h₂s.c1 hu ht.1
      (ht.2.le.trans hvT))).mono (Icc_subset_Icc_right hvT)).congr_deriv
    exact stab_mass_difference_identity_algebra
  have hf := (stab_mu_out_ac h₁s hu huv.le hvT).sub (stab_mu_out_ac h₂s hu huv.le hvT)
  constructor
  · exact stab_mass_point_of_identity huv.le hw hw0 hf haxis
      (by rw [stab_radius_out_integral h₁s hu huv.le hvT]
          exact h₁s.c1.r_pos (u, v) ⟨hu, huv.le, hvT⟩ huv)
      (cq.abs.aestronglyMeasurable measurableSet_Ioc) hd hidentity
  · have hh := stab_mass_hardy_of_identity huv.le hw hw0 hf haxis
      (cq.abs.aestronglyMeasurable measurableSet_Ioc) hd hidentity
    convert hh using 1
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [stab_radius_out_integral h₁s hu ht.1.le (ht.2.trans hvT)]
    simp only [Pi.sub_apply]

end EmcsfAcExtension.Local
