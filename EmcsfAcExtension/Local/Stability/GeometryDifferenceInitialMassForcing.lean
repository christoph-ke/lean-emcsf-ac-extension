module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassForcing
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassAlgebra
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassSign
import EmcsfAcExtension.Local.Stability.GeometryDifferenceInitialGauge
import EmcsfAcExtension.Local.Stability.MomentsSections

/-! # Initial mass forcing without geometric remainder

The normalized mass subtraction is integrated in the shared initial
radial measure. The two source terms are the scalar ratio difference
and the electromagnetic square difference, with no global `G` term.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The absolute initial mass forcing costs `2ε` times the initial
ratio Hardy integral, plus its electromagnetic source integral.
These coefficients are universal, independent of all parameters and
the pair; no mass or geometric comparison conclusion is assumed. -/
theorem stab_initial_mass_forcing_budget
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) :
    (∫⁻ t in Icc 0 T, ENNReal.ofReal |massDifferenceForcing S₁ S₂ 0 t|) ≤
      ENNReal.ofReal (2 * ε) * (∫⁻ t in Icc 0 T, ENNReal.ofReal (S₁.lam 0 t / S₁.r 0 t *
        ‖S₁.theta 0 t / (S₁.lam 0 t : ℂ) - S₂.theta 0 t / (S₂.lam 0 t : ℂ)‖)) +
      ∫⁻ t in Icc 0 T, ENNReal.ofReal (S₁.lam 0 t / S₁.r 0 t *
        |S₁.Q 0 t ^ 2 / S₁.r 0 t ^ 2 - S₂.Q 0 t ^ 2 / S₂.r 0 t ^ 2|) := by
  rw [← restrict_Ioc_eq_restrict_Icc]
  let d := fun t => S₁.lam 0 t / S₁.r 0 t *
    ‖S₁.theta 0 t / (S₁.lam 0 t : ℂ) - S₂.theta 0 t / (S₂.lam 0 t : ℂ)‖
  let c := fun t => S₁.lam 0 t / S₁.r 0 t *
    |S₁.Q 0 t ^ 2 / S₁.r 0 t ^ 2 - S₂.Q 0 t ^ 2 / S₂.r 0 t ^ 2|
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hmap : MapsTo (fun t : ℝ => (0, t)) (Ioc 0 T) (triangle 0 T) :=
    fun t ht => ⟨le_rfl, ht.1.le, ht.2⟩
  have cL := h₁s.c1.c1_lam.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cR := h₁s.c1.c1_r.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cX₁ := (stab_out_ratio_c1 h₁s.c1).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cX₂ := (stab_out_ratio_c1 h₂s.c1).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cd : ContinuousOn d (Ioc 0 T) := (cL.div cR
    (fun t ht => (h₁s.c1.r_pos (0, t) (hmap ht) ht.1).ne')).mul (cX₁.sub cX₂).norm
  have ad : AEMeasurable (fun t => ENNReal.ofReal (2 * ε) * ENNReal.ofReal (d t))
      (volume.restrict (Ioc 0 T)) := by
    have hd : AEMeasurable (fun t => ENNReal.ofReal (d t)) (volume.restrict (Ioc 0 T)) := by
      simpa only [Function.comp_def] using!
        ENNReal.continuous_ofReal.measurable.comp_aemeasurable
          (cd.aemeasurable (μ := volume) measurableSet_Ioc)
    exact hd.const_mul _
  have hp : ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      ENNReal.ofReal |massDifferenceForcing S₁ S₂ 0 t| ≤
        ENNReal.ofReal (2 * ε) * ENNReal.ofReal (d t) + ENNReal.ofReal (c t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hw : 0 ≤ S₁.lam 0 t / S₁.r 0 t :=
      div_nonneg (h₁s.c1.lam_pos (0, t) (hmap ht)).le
        (h₁s.c1.r_pos (0, t) (hmap ht) ht.1).le
    have hweight : |S₁.lam 0 t / S₁.r 0 t - S₂.lam 0 t / S₂.r 0 t| ≤
        20 * (0 : ℝ) * (S₁.lam 0 t / S₁.r 0 t) := by
      rw [stab_initial_lam h₁s ⟨ht.1.le, ht.2⟩, stab_initial_lam h₂s ⟨ht.1.le, ht.2⟩,
        (h₁s.data.1 t ⟨ht.1.le, ht.2⟩).1, (h₂s.data.1 t ⟨ht.1.le, ht.2⟩).1]
      simp
    have hμ := stab_mu_nonneg h₂s le_rfl ht.1.le ht.2
    have hq := stab_mass_difference_forcing_le
      (E₁ := S₁.Q 0 t ^ 2 / S₁.r 0 t ^ 2) hw hμ
      (by linarith only [h₂s.c1.one_sub_mu_pos (0, t) (hmap ht)])
      (sq_nonneg (S₂.Q 0 t) |> fun hh => div_nonneg hh (sq_nonneg (S₂.r 0 t)))
      ((le_add_of_nonneg_right (norm_nonneg _)).trans (h₁s.box.2 (0, t) (hmap ht)).2.2.2.2.2.1)
      ((le_add_of_nonneg_right (norm_nonneg _)).trans (h₂s.box.2 (0, t) (hmap ht)).2.2.2.2.2.1)
      hweight
    have hreal : |massDifferenceForcing S₁ S₂ 0 t| ≤ (2 * ε) * d t + c t := by
      simpa only [massDifferenceForcing, d, c, mul_zero, zero_mul, add_zero] using! hq
    apply (ENNReal.ofReal_le_ofReal hreal).trans_eq
    rw [ENNReal.ofReal_add (by dsimp only [d]; positivity) (by dsimp only [c]; positivity),
      ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * ε)]
  have hi := (lintegral_mono_ae hp).trans_eq
    (lintegral_add_left' (f := fun t => ENNReal.ofReal (2 * ε) * ENNReal.ofReal (d t))
      (g := fun t => ENNReal.ofReal (c t)) ad)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hi
  exact hi

end EmcsfAcExtension.Local
