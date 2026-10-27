module

public import EmcsfAcExtension.Local.Stability.MomentsSections
public import EmcsfAcExtension.Local.Stability.DifferenceMomentsODE
import EmcsfAcExtension.Local.Calculus.RadialIdentity
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Outgoing difference moment with the exact unabsorbed forcing

This intermediate comparison subtracts the two classical reconstruction
equations. Its forcing retains the inverse-gap and moving radial-weight
differences explicitly. The subsequent two-exponent estimate is still
needed to replace that forcing by the label density of the graph node.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The outgoing difference has the `1/2` moment of its exact unabsorbed
forcing. The numerical coefficient is `1`, uniformly in both solutions,
the coupling, background, interval and minimum radius. This intermediate
helper has no graph-node tag: the density estimate remains to be discharged. -/
theorem stab_out_difference_moment_raw
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : 3 * ε ^ 2 ≤ 1 / 2)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    let q := fun s : ℝ =>
      jC1 (triangle 0 T) S₁ u s / ((1 - S₁.mu u s : ℝ) : ℂ) -
      jC1 (triangle 0 T) S₂ u s / ((1 - S₂.mu u s : ℝ) : ℂ) -
      (S₁.lam u s / S₁.r u s - S₂.lam u s / S₂.r u s) •
        (S₂.theta u s / (S₂.lam u s : ℂ) -
          ‖S₂.theta u s / (S₂.lam u s : ℂ)‖ ^ 2 •
            (S₂.theta u s / (S₂.lam u s : ℂ)))
    ENNReal.ofReal ‖S₁.theta u v / (S₁.lam u v : ℂ) -
        S₂.theta u v / (S₂.lam u v : ℂ)‖ ≤
      ∫⁻ s in Ioc u v, ENNReal.ofReal ((S₁.r u s / S₁.r u v) ^ (1 / 2 : ℝ) * ‖q s‖) := by
  let x₁ := fun s : ℝ => S₁.theta u s / (S₁.lam u s : ℂ)
  let x₂ := fun s : ℝ => S₂.theta u s / (S₂.lam u s : ℂ)
  let a₁ := fun s : ℝ => S₁.lam u s / S₁.r u s
  let a₂ := fun s : ℝ => S₂.lam u s / S₂.r u s
  let q := fun s : ℝ =>
    jC1 (triangle 0 T) S₁ u s / ((1 - S₁.mu u s : ℝ) : ℂ) -
    jC1 (triangle 0 T) S₂ u s / ((1 - S₂.mu u s : ℝ) : ℂ) -
    (a₁ s - a₂ s) • (x₂ s - ‖x₂ s‖ ^ 2 • x₂ s)
  change ENNReal.ofReal ‖x₁ v - x₂ v‖ ≤
    ∫⁻ s in Ioc u v, ENNReal.ofReal ((S₁.r u s / S₁.r u v) ^ (1 / 2 : ℝ) * ‖q s‖)
  have hmap : MapsTo (fun s : ℝ => (u, s)) (Ioc u v) (triangle 0 T) :=
    fun s hs => ⟨hu, hs.1.le, hs.2.trans hvT⟩
  have cJ₁ := (continuousOn_jC1_aux h₁s.pos h₁s.c1).comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cJ₂ := (continuousOn_jC1_aux h₂s.pos h₂s.c1).comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cG₁ : ContinuousOn (fun s : ℝ => 1 - S₁.mu u s) (Ioc u v) :=
    continuousOn_const.sub ((continuousOn_mu_aux h₁s.pos h₁s.c1).comp
    (continuous_const.prodMk continuous_id).continuousOn hmap)
  have cG₂ : ContinuousOn (fun s : ℝ => 1 - S₂.mu u s) (Ioc u v) :=
    continuousOn_const.sub ((continuousOn_mu_aux h₂s.pos h₂s.c1).comp
    (continuous_const.prodMk continuous_id).continuousOn hmap)
  have cA₁ : ContinuousOn a₁ (Ioc u v) :=
    (h₁s.c1.c1_lam.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hmap).div
      (h₁s.c1.c1_r.continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn hmap)
      (fun s hs => (h₁s.c1.r_pos (u, s) (hmap hs) hs.1).ne')
  have cA₂ : ContinuousOn a₂ (Ioc u v) :=
    (h₂s.c1.c1_lam.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hmap).div
      (h₂s.c1.c1_r.continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn hmap)
      (fun s hs => (h₂s.c1.r_pos (u, s) (hmap hs) hs.1).ne')
  have cX₂ : ContinuousOn x₂ (Ioc u v) := (stab_out_ratio_c1 h₂s.c1).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cQ : ContinuousOn q (Ioc u v) :=
    ((cJ₁.div (Complex.continuous_ofReal.comp_continuousOn cG₁)
      (fun s hs => Complex.ofReal_ne_zero.mpr
        (h₁s.c1.one_sub_mu_pos (u, s) (hmap hs)).ne')).sub
      (cJ₂.div (Complex.continuous_ofReal.comp_continuousOn cG₂)
        (fun s hs => Complex.ofReal_ne_zero.mpr
          (h₂s.c1.one_sub_mu_pos (u, s) (hmap hs)).ne'))).sub
      ((cA₁.sub cA₂).smul (cX₂.sub ((cX₂.norm.pow 2).smul cX₂)))
  have cL : ContinuousOn (S₁.lam u) (uIcc u v) := by
    rw [uIcc_of_le huv.le]
    exact h₁s.c1.c1_lam.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨hu, hs.1, hs.2.trans hvT⟩)
  have haxis : x₁ u = x₂ u := by
    rw [show x₁ u = 0 from stab_out_ratio_axis h₁s ⟨hu, huv.le.trans hvT⟩,
      show x₂ u = 0 from stab_out_ratio_axis h₂s ⟨hu, huv.le.trans hvT⟩]
  have hidentity : ∀ t ∈ Ioo u v,
      HasDerivWithinAt (fun s => x₁ s - x₂ s)
        (q t - (S₁.lam u t / ∫ s in u..t, S₁.lam u s) •
          ((x₁ t - ‖x₁ t‖ ^ 2 • x₁ t) - (x₂ t - ‖x₂ t‖ ^ 2 • x₂ t)) -
          (0 : ℝ) • (Complex.I * (x₁ t - x₂ t))) (Icc u v) t := by
    intro t ht
    have htT := ht.2.le.trans hvT
    have h₁d : HasDerivWithinAt x₁
        (jC1 (triangle 0 T) S₁ u t / ((1 - S₁.mu u t : ℝ) : ℂ) -
          a₁ t • (x₁ t - ‖x₁ t‖ ^ 2 • x₁ t)) (Icc u T) t := by
      apply (stab_out_reconstruction h₁s.c1 hu ht.1 htT).congr_deriv
      simp only [x₁, a₁, Complex.real_smul,
        Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow]
      ring
    have h₂d : HasDerivWithinAt x₂
        (jC1 (triangle 0 T) S₂ u t / ((1 - S₂.mu u t : ℝ) : ℂ) -
          a₂ t • (x₂ t - ‖x₂ t‖ ^ 2 • x₂ t)) (Icc u T) t := by
      apply (stab_out_reconstruction h₂s.c1 hu ht.1 htT).congr_deriv
      simp only [x₂, a₂, Complex.real_smul,
        Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow]
      ring
    apply ((h₁d.sub h₂d).mono (Icc_subset_Icc_right hvT)).congr_deriv
    rw [stab_radius_out_integral h₁s hu ht.1.le htT]
    dsimp only [q, a₁, a₂]
    simp only [zero_smul, sub_zero, smul_sub, sub_smul]
    abel
  have hi := stab_radial_difference_moment_of_identity (α := fun _ => 0)
    huv.le (by norm_num : (0 : ℝ) < 1 / 2) (by linarith only [hε])
    cL.intervalIntegrable
    (fun s hs => (h₁s.c1.lam_pos (u, s) ⟨hu, hs.1, hs.2.trans hvT⟩).le)
    (stab_out_ratio_ac h₁s hu huv.le hvT) (stab_out_ratio_ac h₂s hu huv.le hvT) haxis
    (fun s hs => (le_add_of_nonneg_right (norm_nonneg
      (S₁.xi u s / (S₁.nu u s : ℂ)))).trans
      (h₁s.box.2 (u, s) ⟨hu, hs.1.le, hs.2.le.trans hvT⟩).2.2.2.2.2.1)
    (fun s hs => (le_add_of_nonneg_right (norm_nonneg
      (S₂.xi u s / (S₂.nu u s : ℂ)))).trans
      (h₂s.box.2 (u, s) ⟨hu, hs.1.le, hs.2.le.trans hvT⟩).2.2.2.2.2.1)
    (by rw [stab_radius_out_integral h₁s hu huv.le hvT]
        exact h₁s.c1.r_pos (u, v) ⟨hu, huv.le, hvT⟩ huv)
    (cQ.norm.aestronglyMeasurable measurableSet_Ioc) hidentity
  apply hi.trans_eq
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro s hs
  dsimp only
  rw [stab_radius_out_integral h₁s hu hs.1.le (hs.2.trans hvT),
    stab_radius_out_integral h₁s hu huv.le hvT]

end EmcsfAcExtension.Local
