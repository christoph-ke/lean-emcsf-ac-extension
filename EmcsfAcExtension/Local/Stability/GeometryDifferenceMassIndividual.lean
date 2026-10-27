module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassODE
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassRegularity
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassSign
import EmcsfAcExtension.Local.Stability.MomentsSections
import EmcsfAcExtension.Local.Calculus.Raychaudhuri
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Damped individual mass comparison

The exact normalized constraint controls both the point value and the
singular weighted mass integral by the scalar and electromagnetic
sources. Its AC endpoint is proved from the optical identities.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- Individual normalized mass has both the point and weighted source
bound, with literal constant `1` for each. This conditional source
estimate is uniform in all solution parameters and the endpoint radius. -/
theorem stab_out_mass_source_comparison
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    let q := fun t => S.lam u t / S.r u t *
      (‖S.theta u t / (S.lam u t : ℂ)‖ ^ 2 + S.Q u t ^ 2 / S.r u t ^ 2)
    ENNReal.ofReal |S.mu u v| ≤ (∫⁻ t in Ioc u v, ENNReal.ofReal (q t)) ∧
      (∫⁻ t in Ioc u v, ENNReal.ofReal (S.lam u t / S.r u t * |S.mu u t|)) ≤
        ∫⁻ t in Ioc u v, ENNReal.ofReal (q t) := by
  let q := fun t => S.lam u t / S.r u t *
    (‖S.theta u t / (S.lam u t : ℂ)‖ ^ 2 + S.Q u t ^ 2 / S.r u t ^ 2)
  let d := fun t => S.lam u t / S.r u t *
    (1 + ‖S.theta u t / (S.lam u t : ℂ)‖ ^ 2)
  have hmap : MapsTo (fun t : ℝ => (u, t)) (Ioc u v) (triangle 0 T) :=
    fun t ht => ⟨hu, ht.1.le, ht.2.trans hvT⟩
  have cL := hset.c1.c1_lam.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cR := hset.c1.c1_r.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cQ := hset.c1.c1_Q.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cX := (stab_out_ratio_c1 hset.c1).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have hr : ∀ t ∈ Ioc u v, S.r u t ≠ 0 :=
    fun t ht => (hset.c1.r_pos (u, t) (hmap ht) ht.1).ne'
  have cq : ContinuousOn q (Ioc u v) :=
    (cL.div cR hr).mul ((cX.norm.pow 2).add
      ((cQ.pow 2).div (cR.pow 2) (fun t ht => pow_ne_zero 2 (hr t ht))))
  have hw : IntervalIntegrable (S.lam u) volume u v := by
    apply ContinuousOn.intervalIntegrable_of_Icc huv.le
    exact hset.c1.c1_lam.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨hu, ht.1, ht.2.trans hvT⟩)
  have hw0 : ∀ t ∈ Icc u v, 0 ≤ S.lam u t :=
    fun t ht => (hset.c1.lam_pos (u, t) ⟨hu, ht.1, ht.2.trans hvT⟩).le
  have haxis : S.mu u u = 0 := by
    dsimp only [Fields.mu]
    rw [(hset.c1.axis u ⟨hu, le_rfl, huv.le.trans hvT⟩).1, div_zero]
  have hd : ∀ t ∈ Ioo u v, S.lam u t / (∫ s in u..t, S.lam u s) ≤ d t := by
    intro t ht
    rw [stab_radius_out_integral hset hu ht.1.le (ht.2.le.trans hvT)]
    have hb : 0 ≤ S.lam u t / S.r u t := div_nonneg (hw0 t ⟨ht.1.le, ht.2.le⟩)
      (hset.c1.r_pos (u, t) ⟨hu, ht.1.le, ht.2.le.trans hvT⟩ ht.1).le
    dsimp only [d]
    nlinarith only [mul_nonneg hb (sq_nonneg ‖S.theta u t / (S.lam u t : ℂ)‖)]
  have hidentity : ∀ t ∈ Ioo u v,
      HasDerivWithinAt (S.mu u) (q t - d t * S.mu u t) (Icc u v) t := by
    intro t ht
    apply ((Stab.outgoing_mu_derivative_identity hset.c1 hu ht.1
      (ht.2.le.trans hvT)).mono (Icc_subset_Icc_right hvT)).congr_deriv
    dsimp only [q, d]
    ring
  have hqeq : (∫⁻ t in Ioc u v, ENNReal.ofReal |q t|) =
      ∫⁻ t in Ioc u v, ENNReal.ofReal (q t) := by
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro t ht
    change ENNReal.ofReal |q t| = ENNReal.ofReal (q t)
    rw [abs_of_nonneg (show 0 ≤ q t from by
      dsimp only [q]
      have hl := hw0 t ⟨ht.1.le, ht.2⟩
      have hr0 := (hset.c1.r_pos (u, t) (hmap ht) ht.1).le
      positivity)]
  have hf := stab_mu_out_ac hset hu huv.le hvT
  constructor
  · exact (stab_mass_point_of_identity huv.le hw hw0 hf haxis
      (by rw [stab_radius_out_integral hset hu huv.le hvT]
          exact hset.c1.r_pos (u, v) ⟨hu, huv.le, hvT⟩ huv)
      (cq.abs.aestronglyMeasurable measurableSet_Ioc) hd hidentity).trans_eq hqeq
  · have hh := (stab_mass_hardy_of_identity huv.le hw hw0 hf haxis
      (cq.abs.aestronglyMeasurable measurableSet_Ioc) hd hidentity).trans_eq hqeq
    convert hh using 1
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [stab_radius_out_integral hset hu ht.1.le (ht.2.trans hvT)]

end EmcsfAcExtension.Local
