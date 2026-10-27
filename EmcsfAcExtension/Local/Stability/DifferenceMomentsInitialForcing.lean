module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeometryDifferenceInitialGauge
import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux
import EmcsfAcExtension.Local.Stability.DifferenceMomentsForcing
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Initial radial difference forcing without geometric error

The two initial radii and outgoing expansions agree identically. The
only reconstruction coefficient difference is therefore the mass gap.
The mass bound stays local to the initial cone.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The initial radial forcing has total mass `4Δj+16AεU` when the
initial mass-ratio difference is bounded by `U`. The coefficients are
literal and universal; this conditional helper inserts no global
geometric error into the initial-cone argument. -/
theorem stab_initial_forcing_le_of_mass_bound
    {e T ε M A U : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (hA : 0 < A) (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : ε ≤ 1) (hU : 0 ≤ U)
    (hmass : ∀ v ∈ Icc 0 T, |S₁.mu 0 v - S₂.mu 0 v| ≤ U) :
    let q := fun t =>
      jC1 (triangle 0 T) S₁ 0 t / ((1 - S₁.mu 0 t : ℝ) : ℂ) -
      jC1 (triangle 0 T) S₂ 0 t / ((1 - S₂.mu 0 t : ℝ) : ℂ) -
      (S₁.lam 0 t / S₁.r 0 t - S₂.lam 0 t / S₂.r 0 t) •
        (S₂.theta 0 t / (S₂.lam 0 t : ℂ) - ‖S₂.theta 0 t / (S₂.lam 0 t : ℂ)‖ ^ 2 •
          (S₂.theta 0 t / (S₂.lam 0 t : ℂ)))
    (∫⁻ t in Icc 0 T, ENNReal.ofReal ‖q t‖) ≤
      ENNReal.ofReal (4 * (jDist T S₁ S₂).toReal + 16 * A * ε * U) := by
  let q := fun t =>
    jC1 (triangle 0 T) S₁ 0 t / ((1 - S₁.mu 0 t : ℝ) : ℂ) -
    jC1 (triangle 0 T) S₂ 0 t / ((1 - S₂.mu 0 t : ℝ) : ℂ) -
    (S₁.lam 0 t / S₁.r 0 t - S₂.lam 0 t / S₂.r 0 t) •
      (S₂.theta 0 t / (S₂.lam 0 t : ℂ) - ‖S₂.theta 0 t / (S₂.lam 0 t : ℂ)‖ ^ 2 •
        (S₂.theta 0 t / (S₂.lam 0 t : ℂ)))
  let D := outEnv 0 (fun u v => jC1 (triangle 0 T) S₁ u v - jC1 (triangle 0 T) S₂ u v)
  let J := outEnv 0 (jC1 (triangle 0 T) S₂)
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have cD : ContinuousOn D (Icc 0 T) := continuousOn_outEnv
    ((continuousOn_jC1_aux h₁s.pos h₁s.c1).sub (continuousOn_jC1_aux h₂s.pos h₂s.c1))
  have hpoint : ∀ᵐ t ∂volume.restrict (Icc 0 T),
      ENNReal.ofReal ‖q t‖ ≤ ENNReal.ofReal 4 * D t + ENNReal.ofReal (16 * U) * J t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hp : (0, t) ∈ triangle (0 : ℝ) T := ⟨le_rfl, ht.1, ht.2⟩
    have hweight : S₁.lam 0 t / S₁.r 0 t = S₂.lam 0 t / S₂.r 0 t := by
      rw [stab_initial_lam h₁s ht, stab_initial_lam h₂s ht,
        (h₁s.data.1 t ht).1, (h₂s.data.1 t ht).1]
    have hz : ‖S₂.theta 0 t / (S₂.lam 0 t : ℂ)‖ ≤ 1 :=
      ((le_add_of_nonneg_right (norm_nonneg _)).trans
        (h₂s.box.2 (0, t) hp).2.2.2.2.2.1).trans hε
    have hf := stab_radial_difference_forcing_le (j₁ := jC1 (triangle 0 T) S₁ 0 t)
      (j₂ := jC1 (triangle 0 T) S₂ 0 t) (a₁ := S₁.lam 0 t / S₁.r 0 t)
      (a₂ := S₂.lam 0 t / S₂.r 0 t)
      (h₁s.box.2 (0, t) hp).2.2.2.2.1 (h₂s.box.2 (0, t) hp).2.2.2.2.1 hz
    simp only [hweight, sub_self, zero_smul, sub_zero, abs_zero, zero_mul, add_zero] at hf
    have hreal : ‖q t‖ ≤
        4 * ‖jC1 (triangle 0 T) S₁ 0 t - jC1 (triangle 0 T) S₂ 0 t‖ +
          (16 * U) * ‖jC1 (triangle 0 T) S₂ 0 t‖ := by
      have hscale := mul_le_mul_of_nonneg_right (hmass t ht)
        (show 0 ≤ 16 * ‖jC1 (triangle 0 T) S₂ 0 t‖ by positivity)
      dsimp only [q]
      simp only [hweight, sub_self, zero_smul, sub_zero]
      nlinarith only [hf, hscale]
    apply (ENNReal.ofReal_le_ofReal hreal).trans
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
      ENNReal.ofReal_mul (by positivity : 0 ≤ 16 * U), ofReal_norm, ofReal_norm]
    have hD : ‖jC1 (triangle 0 T) S₁ 0 t - jC1 (triangle 0 T) S₂ 0 t‖ₑ ≤ D t := by
      simpa only [D, outEnv] using! enorm_le_normEnvelope
        (fun u v => jC1 (triangle 0 T) S₁ u v - jC1 (triangle 0 T) S₂ u v) ⟨le_rfl, ht.1⟩
    have hJ : ‖jC1 (triangle 0 T) S₂ 0 t‖ₑ ≤ J t := by
      simpa only [J, outEnv] using! enorm_le_normEnvelope (jC1 (triangle 0 T) S₂)
        ⟨le_rfl, ht.1⟩
    exact add_le_add (mul_le_mul' le_rfl hD) (mul_le_mul' le_rfl hJ)
  have hDmeas : AEMeasurable (fun t => ENNReal.ofReal 4 * D t)
      (volume.restrict (Icc 0 T)) := (cD.aemeasurable measurableSet_Icc).const_mul _
  have hi := (lintegral_mono_ae hpoint).trans_eq
    (lintegral_add_left' (f := fun t => ENNReal.ofReal 4 * D t)
      (g := fun t => ENNReal.ofReal (16 * U) * J t) hDmeas)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hi
  have henv : (∫⁻ t in Icc 0 T, J t) ≤ ENNReal.ofReal (A * ε) :=
    (le_add_of_nonneg_right bot_le).trans h₂s.env
  apply hi.trans
  apply (add_le_add le_rfl (mul_le_mul' le_rfl henv)).trans_eq
  change ENNReal.ofReal 4 * jDist T S₁ S₂ +
    ENNReal.ofReal (16 * U) * ENNReal.ofReal (A * ε) = _
  rw [← ENNReal.ofReal_toReal (stab_jDist_ne_top h₁s h₂s),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 16 * U),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  simp only [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
  ring

end EmcsfAcExtension.Local
