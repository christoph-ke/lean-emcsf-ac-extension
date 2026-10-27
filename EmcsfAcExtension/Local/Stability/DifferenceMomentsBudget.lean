module

public import EmcsfAcExtension.Local.Stability.DifferenceMomentsFieldForcing
public import EmcsfAcExtension.Local.Stability.GeometryDifferenceWeights
import EmcsfAcExtension.Local.Stability.DifferenceMomentsDensity
import EmcsfAcExtension.Local.Stability.DifferenceMomentsLocalHardy
import EmcsfAcExtension.Local.Calculus.RadialIdentity
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Integral budget for the exact outgoing difference forcing

The individual Hardy estimate controls the geometric forcing. The
result retains the mass difference and is uniform down to the axis.
All envelope dependence is displayed as the product `A ε`.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The exact outgoing difference forcing has total mass at most `8192`
times the unabsorbed comparison budget. The coefficient is universal,
independent of the pair and all parameters; `A ε` is explicit. -/
theorem stab_out_difference_forcing_lintegral_le
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : 3 * ε ^ 2 ≤ 1 / 2)
    {u : ℝ} (hu : 0 ≤ u) (huT : u ≤ T) :
    let q := fun t : ℝ =>
      jC1 (triangle 0 T) S₁ u t / ((1 - S₁.mu u t : ℝ) : ℂ) -
      jC1 (triangle 0 T) S₂ u t / ((1 - S₂.mu u t : ℝ) : ℂ) -
      (S₁.lam u t / S₁.r u t - S₂.lam u t / S₂.r u t) •
        (S₂.theta u t / (S₂.lam u t : ℂ) -
          ‖S₂.theta u t / (S₂.lam u t : ℂ)‖ ^ 2 • (S₂.theta u t / (S₂.lam u t : ℂ)))
    (∫⁻ t in Ioc u T, ENNReal.ofReal ‖q t‖) ≤
      8192 * (jDist T S₁ S₂ +
        ENNReal.ofReal ((geomDist T S₁ S₂).toReal + (supDist T S₁.mu S₂.mu).toReal) *
          ENNReal.ofReal (A * ε)) := by
  let G := ENNReal.ofReal (geomDist T S₁ S₂).toReal
  let U := ENNReal.ofReal (supDist T S₁.mu S₂.mu).toReal
  let D := outEnv 0 (fun u v => jC1 (triangle 0 T) S₁ u v - jC1 (triangle 0 T) S₂ u v)
  let J := outEnv 0 (jC1 (triangle 0 T) S₂)
  let B := fun t => ENNReal.ofReal (S₁.lam u t / S₁.r u t)
  let X := fun t => ENNReal.ofReal ‖S₂.theta u t / (S₂.lam u t : ℂ)‖
  let H := fun t => B t * X t
  let Z := fun t => ENNReal.ofReal (1 / 64 : ℝ) * H t
  let F := fun t => ENNReal.ofReal ‖
    jC1 (triangle 0 T) S₁ u t / ((1 - S₁.mu u t : ℝ) : ℂ) -
    jC1 (triangle 0 T) S₂ u t / ((1 - S₂.mu u t : ℝ) : ℂ) -
    (S₁.lam u t / S₁.r u t - S₂.lam u t / S₂.r u t) •
      (S₂.theta u t / (S₂.lam u t : ℂ) -
        ‖S₂.theta u t / (S₂.lam u t : ℂ)‖ ^ 2 • (S₂.theta u t / (S₂.lam u t : ℂ)))‖
  have hε1 : ε ≤ 1 := by nlinarith only [hε, sq_nonneg (ε - 1)]
  have hεq : ε ^ 2 ≤ 1 / 4 := by linarith only [hε]
  have cD : ContinuousOn D (Icc u T) :=
    (continuousOn_outEnv ((continuousOn_jC1_aux h₁s.pos h₁s.c1).sub
    (continuousOn_jC1_aux h₂s.pos h₂s.c1))).mono (Icc_subset_Icc hu le_rfl)
  have cJ : ContinuousOn J (Icc u T) :=
    (continuousOn_outEnv (continuousOn_jC1_aux h₂s.pos h₂s.c1)).mono
    (Icc_subset_Icc hu le_rfl)
  have hH : (∫⁻ t in Icc u T, H t) ≤
      16 * (16 * ∫⁻ t in Icc u T, J t) := by
    have hi := stab_out_hardy_local_of_identity h₂s (fun u v hu huv hvT => by
      apply (stab_out_reconstruction h₂s.c1 hu huv hvT).congr_deriv
      simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_sub,
        Complex.ofReal_one, Complex.ofReal_pow]) hεq hu huT
    rw [restrict_Ioc_eq_restrict_Icc] at hi
    have hcost : ENNReal.ofReal (16 / 3 : ℝ) ≤ 16 := by
      calc
        _ ≤ ENNReal.ofReal (16 : ℝ) := ENNReal.ofReal_le_ofReal (by norm_num)
        _ = _ := by norm_num
    have hi' := hi.trans (mul_le_mul' hcost le_rfl)
    apply le_trans ?_ (mul_le_mul' le_rfl hi')
    rw [← lintegral_const_mul' 16 _ (by norm_num)]
    have hne : ∀ᵐ t : ℝ, t ≠ u := by simp [ae_iff, measure_singleton]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with t ht htu
    have hut : u < t := lt_of_le_of_ne ht.1 htu.symm
    have hp : (u, t) ∈ triangle 0 T := ⟨hu, hut.le, ht.2⟩
    have hB₂ : 0 ≤ S₂.lam u t / S₂.r u t := div_nonneg
      (h₂s.c1.lam_pos (u, t) hp).le (h₂s.c1.r_pos (u, t) hp hut).le
    have hm := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (stab_out_weight_le_sixteen h₁s h₂s hu hut ht.2)
      (norm_nonneg (S₂.theta u t / (S₂.lam u t : ℂ))))
    dsimp only [H, B, X]
    rw [← ENNReal.ofReal_mul (div_nonneg (h₁s.c1.lam_pos (u, t) hp).le
      (h₁s.c1.r_pos (u, t) hp hut).le)]
    simpa only [mul_assoc, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16),
      ENNReal.ofReal_ofNat] using hm
  have hconv : (∫⁻ t in Icc u T, (1 : ℝ≥0∞) * 1 * Z t) ≤
      4 * ∫⁻ t in Icc u T, (1 : ℝ≥0∞) * J t := by
    simp only [one_mul]
    change (∫⁻ t in Icc u T, ENNReal.ofReal (1 / 64 : ℝ) * H t) ≤ _
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply (mul_le_mul' le_rfl hH).trans
    have hc : ENNReal.ofReal (1 / 64 : ℝ) * 256 = 4 := by
      have hh : ENNReal.ofReal ((1 / 64 : ℝ) * 256) =
          ENNReal.ofReal (1 / 64 : ℝ) * ENNReal.ofReal (256 : ℝ) :=
        ENNReal.ofReal_mul (by norm_num)
      norm_num at hh
      exact hh.symm
    apply le_of_eq
    calc
      _ = (ENNReal.ofReal (1 / 64 : ℝ) * 256) * ∫⁻ t in Icc u T, J t := by ring
      _ = _ := by rw [hc]
  have hforce : ∀ᵐ t ∂volume.restrict (Icc u T),
      F t ≤ 4 * D t + 16 * U * J t + 20 * G * 1 * H t := by
    have hne : ∀ᵐ t : ℝ, t ≠ u := by simp [ae_iff, measure_singleton]
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with t ht htu
    have hut : u < t := lt_of_le_of_ne ht.1 htu.symm
    simpa only [F, D, J, G, U, H, B, X, mul_one, mul_assoc] using
      stab_out_difference_forcing_enorm_le h₁s h₂s hε1 hu hut ht.2
  have hdensity := stab_difference_density_of_moment_bounds
    (K := fun _ => 1) (B := fun _ => 1) (X := H) (Z := Z)
    (show G ≠ ⊤ from ENNReal.ofReal_ne_top) (show U ≠ ⊤ from ENNReal.ofReal_ne_top)
    (by simpa only [one_mul] using cD.aemeasurable (μ := volume) measurableSet_Icc)
    (by simpa only [one_mul] using cJ.aemeasurable (μ := volume) measurableSet_Icc)
    hforce (by
      filter_upwards [] with t
      have hc : (64 : ℝ≥0∞) * ENNReal.ofReal (1 / 64 : ℝ) = 1 := by
        have hh : ENNReal.ofReal ((64 : ℝ) * (1 / 64)) =
            ENNReal.ofReal (64 : ℝ) * ENNReal.ofReal (1 / 64 : ℝ) :=
          ENNReal.ofReal_mul (by norm_num)
        norm_num at hh
        exact hh.symm
      change H t ≤ 64 * (ENNReal.ofReal (1 / 64 : ℝ) * H t)
      rw [← mul_assoc, hc, one_mul]) hconv
  simp only [one_mul] at hdensity
  rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
  have hres : (∫⁻ t in Ioc u T, F t) ≤ ∫⁻ t in Icc u T, F t :=
    lintegral_mono_set (fun _ ht => ⟨ht.1.le, ht.2⟩)
  apply (hres.trans hdensity).trans
  apply mul_le_mul' le_rfl
  rw [lintegral_add_left' (cD.aemeasurable measurableSet_Icc),
    lintegral_const_mul' (G + U) _ (ENNReal.add_ne_top.mpr
      ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)]
  apply add_le_add
  · exact lintegral_mono_set (Icc_subset_Icc hu le_rfl)
  · apply mul_le_mul' le_rfl
    exact (lintegral_mono_set (Icc_subset_Icc hu le_rfl)).trans
      ((le_add_of_nonneg_right bot_le).trans h₂s.env)

end EmcsfAcExtension.Local
