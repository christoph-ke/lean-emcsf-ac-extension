module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.DifferenceMomentsMixedHardy
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Local.Calculus.C1ToSolution2

/-! # Radial source budgets for mass comparison

The scalar square uses the linear Hardy budget, while the radius-square
source has the exact area primitive. Both statements include the axis
and retain the scale needed for the electromagnetic term.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The outgoing scalar-square budget in either solution's radial
measure has literal coefficient `256`, with envelope dependence only
through `Aε²`. The estimate is uniform in all remaining parameters. -/
theorem stab_out_mixed_quadratic_le
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : ε ^ 2 ≤ 1 / 4)
    {u : ℝ} (hu : 0 ≤ u) (huT : u ≤ T) :
    (∫⁻ t in Icc u T, ENNReal.ofReal (S₁.lam u t / S₁.r u t *
      ‖S₂.theta u t / (S₂.lam u t : ℂ)‖ ^ 2)) ≤ ENNReal.ofReal (256 * A * ε ^ 2) := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hi : (∫⁻ t in Icc u T, ENNReal.ofReal (S₁.lam u t / S₁.r u t *
      ‖S₂.theta u t / (S₂.lam u t : ℂ)‖ ^ 2)) ≤
      ENNReal.ofReal ε * ∫⁻ t in Icc u T, ENNReal.ofReal
        (S₁.lam u t / S₁.r u t * ‖S₂.theta u t / (S₂.lam u t : ℂ)‖) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' measurableSet_Icc
    intro t ht
    rw [← ENNReal.ofReal_mul hε0]
    apply ENNReal.ofReal_le_ofReal
    have hp : (u, t) ∈ triangle 0 T := ⟨hu, ht.1, ht.2⟩
    have hr : 0 ≤ S₁.r u t := by
      have hb := (stab_radius_bounds h₁s hu ht.1 ht.2).1
      linarith only [hb, ht.1]
    have hB : 0 ≤ S₁.lam u t / S₁.r u t :=
      div_nonneg (h₁s.c1.lam_pos (u, t) hp).le hr
    have hx : ‖S₂.theta u t / (S₂.lam u t : ℂ)‖ ≤ ε :=
      (le_add_of_nonneg_right (norm_nonneg _)).trans (h₂s.box.2 (u, t) hp).2.2.2.2.2.1
    have hh := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hx
        (norm_nonneg (S₂.theta u t / (S₂.lam u t : ℂ)))) hB
    nlinarith only [hh]
  apply hi.trans
  apply (mul_le_mul' le_rfl (stab_out_mixed_hardy_le h₁s h₂s hε hu huT)).trans_eq
  rw [← ENNReal.ofReal_mul hε0]
  congr 1
  ring

/-- The outgoing radius-square radial measure has the exact area
primitive `r²/2`. There is no estimate constant, smallness condition,
or lower radius cutoff. -/
theorem stab_out_weight_radius_sq_lintegral
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    (∫⁻ t in Icc u v, ENNReal.ofReal (S.lam u t / S.r u t * S.r u t ^ 2)) =
      ENNReal.ofReal (S.r u v ^ 2 / 2) := by
  have hseg : outSeg u u v ⊆ triangle 0 T := by
    rintro ⟨a, b⟩ ⟨rfl, hs⟩
    exact ⟨hu, hs.1, hs.2.trans hvT⟩
  have hm := outgoing_radius_moment (hset.c1.toIsSolution hset.pos) huv hseg 1
  simp only [pow_one, Nat.cast_one, one_add_one_eq_two] at hm
  have hmap : MapsTo (fun t : ℝ => (u, t)) (Icc u v) (triangle 0 T) :=
    fun t ht => ⟨hu, ht.1, ht.2.trans hvT⟩
  have cF := (hset.c1.c1_lam.continuousOn.mul hset.c1.c1_r.continuousOn).comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le huv).1
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv cF)
  have hn : ∀ᵐ t ∂volume.restrict (Icc u v), 0 ≤ S.lam u t * S.r u t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hb := (stab_radius_bounds hset hu ht.1 (ht.2.trans hvT)).1
    have hr : 0 ≤ S.r u t := by linarith only [hb, ht.1]
    exact mul_nonneg (hset.c1.lam_pos (u, t) (hmap ht)).le hr
  calc
    _ = ∫⁻ t in Icc u v, ENNReal.ofReal (S.lam u t * S.r u t) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro t ht
      by_cases hr : S.r u t = 0
      · simp only [hr, div_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
      · field_simp
    _ = ENNReal.ofReal (∫ t in Icc u v, S.lam u t * S.r u t) :=
      (ofReal_integral_eq_lintegral_ofReal hi hn).symm
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le huv, hm]

end EmcsfAcExtension.Local
