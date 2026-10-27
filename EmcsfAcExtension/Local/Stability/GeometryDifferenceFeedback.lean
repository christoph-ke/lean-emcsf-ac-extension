module

public import EmcsfAcExtension.Local.Stability.GeometryDifference
import EmcsfAcExtension.Local.Stability.DifferenceMomentsEstimates
import EmcsfAcExtension.Local.Stability.FluxDifferenceIntegral

/-! # Explicit outgoing optical mass feedback

The exact axis optical identity and the unabsorbed radial Hardy bound
give one scalar inequality for the finite mass-ratio distance. No later
field, charge, potential or mass-Volterra projection is used.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The outgoing optical mass feedback before absorption. All numerical
coefficients are universal; envelope dependence occurs only through the
displayed `A`. The distances are finite from classical regularity before
their real values are used, with no minimum-radius dependence. -/
theorem stab_out_mass_feedback_before_absorption
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (hA : 0 < A) (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : 3 * ε ^ 2 ≤ 1 / 2) :
    let G := (geomDist T S₁ S₂).toReal
    let U := (supDist T S₁.mu S₂.mu).toReal
    let J := (jDist T S₁ S₂).toReal
    U ≤ 20 * G + 131072 * ε * (J + (G + U) * (A * ε)) + 20480 * A * ε ^ 2 * G := by
  let G := (geomDist T S₁ S₂).toReal
  let U := (supDist T S₁.mu S₂.mu).toReal
  let J := (jDist T S₁ S₂).toReal
  let R := J + (G + U) * (A * ε)
  let L := 20 * G + 131072 * ε * R + 20480 * A * ε ^ 2 * G
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hU : 0 ≤ U := ENNReal.toReal_nonneg
  have hJ : 0 ≤ J := ENNReal.toReal_nonneg
  have hR : 0 ≤ R := add_nonneg hJ
    (mul_nonneg (add_nonneg hG hU) (mul_nonneg hA.le hε0))
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hJval : ENNReal.ofReal J = jDist T S₁ S₂ :=
    ENNReal.ofReal_toReal (stab_jDist_ne_top h₁s h₂s)
  have hpoint : ∀ u v : ℝ, (u, v) ∈ triangle 0 T → |S₁.mu u v - S₂.mu u v| ≤ L := by
    intro u v hp
    rcases eq_or_lt_of_le hp.2.1 with heq | huv
    · change u = v at heq
      subst v
      simpa only [Fields.mu, (h₁s.c1.axis u hp).1, (h₂s.c1.axis u hp).1,
        div_zero, sub_self, abs_zero] using hL
    · have hH := stab_out_difference_hardy_before_absorption h₁s h₂s hε hp.1
        (huv.le.trans hp.2.2)
      rw [restrict_Ioc_eq_restrict_Icc] at hH
      have hH' : (∫⁻ s in Icc u T, ENNReal.ofReal (S₁.lam u s / S₁.r u s *
          ‖S₁.theta u s / (S₁.lam u s : ℂ) - S₂.theta u s / (S₂.lam u s : ℂ)‖)) ≤
          ENNReal.ofReal (16384 * R) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16384)]
        dsimp only [R]
        rw [ENNReal.ofReal_add hJ (mul_nonneg (add_nonneg hG hU) (mul_nonneg hA.le hε0)),
          ENNReal.ofReal_mul (add_nonneg hG hU), hJval]
        simpa only [G, U, ENNReal.ofReal_ofNat] using hH
      have hF := stab_out_optical_exponent_sub_le hA h₁s h₂s
        (by linarith only [hε] : ε ^ 2 ≤ 1 / 4) hp.1 huv hp.2.2
      have hI : ENNReal.ofReal |(∫ s in u..v, S₁.lam u s / S₁.r u s *
            ‖S₁.theta u s / (S₁.lam u s : ℂ)‖ ^ 2) -
          (∫ s in u..v, S₂.lam u s / S₂.r u s *
            ‖S₂.theta u s / (S₂.lam u s : ℂ)‖ ^ 2)| ≤
          ENNReal.ofReal (32768 * ε * R + 5120 * A * ε ^ 2 * G) := by
        apply (hF.trans (add_le_add (mul_le_mul' le_rfl hH') le_rfl)).trans_eq
        rw [← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hε0),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        dsimp only [G]
        ring
      have hIreal := (ENNReal.ofReal_le_ofReal_iff (show
        0 ≤ 32768 * ε * R + 5120 * A * ε ^ 2 * G by positivity)).mp hI
      have hopt := stab_out_mass_gap_sub_le h₁s h₂s hp.1 huv hp.2.2
      change |S₁.mu u v - S₂.mu u v| ≤ L
      dsimp only [L]
      dsimp only [G] at hIreal ⊢
      linarith only [hopt, hIreal]
  have hsup : supDist T S₁.mu S₂.mu ≤ ENNReal.ofReal L := by
    apply iSup₂_le
    rintro ⟨u, v⟩ hp
    rw [← ofReal_norm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (hpoint u v hp)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsup
  simpa only [ENNReal.toReal_ofReal hL] using hreal

end EmcsfAcExtension.Local
