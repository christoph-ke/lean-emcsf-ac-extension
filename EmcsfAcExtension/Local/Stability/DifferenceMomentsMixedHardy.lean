module

public import EmcsfAcExtension.Local.Stability.GeometryDifferenceWeights
import EmcsfAcExtension.Local.Stability.DifferenceMomentsLocalHardy
import EmcsfAcExtension.Local.Calculus.RadialIdentity
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Mixed-radius individual Hardy budget

The first solution's radial measure can be used on the second scalar
ratio with universal cost `256`. Envelope dependence remains explicit.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The outgoing linear Hardy budget in the comparison measure has
coefficient `256`, uniformly in all parameters and the pair, with
envelope dependence only through the displayed product `A ε`. -/
theorem stab_out_mixed_hardy_le
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : ε ^ 2 ≤ 1 / 4)
    {u : ℝ} (hu : 0 ≤ u) (huT : u ≤ T) :
    (∫⁻ t in Icc u T, ENNReal.ofReal (S₁.lam u t / S₁.r u t *
      ‖S₂.theta u t / (S₂.lam u t : ℂ)‖)) ≤ ENNReal.ofReal (256 * A * ε) := by
  let B := fun t => ENNReal.ofReal (S₁.lam u t / S₁.r u t)
  let X := fun t => ENNReal.ofReal ‖S₂.theta u t / (S₂.lam u t : ℂ)‖
  let H := fun t => B t * X t
  let J := outEnv 0 (jC1 (triangle 0 T) S₂)
  have hH : (∫⁻ t in Icc u T, H t) ≤
      16 * (16 * ∫⁻ t in Icc u T, J t) := by
    have hi := stab_out_hardy_local_of_identity h₂s (fun u v hu huv hvT => by
      apply (stab_out_reconstruction h₂s.c1 hu huv hvT).congr_deriv
      simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_sub,
        Complex.ofReal_one, Complex.ofReal_pow]) hε hu huT
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
  have heq : (∫⁻ t in Icc u T, ENNReal.ofReal (S₁.lam u t / S₁.r u t *
      ‖S₂.theta u t / (S₂.lam u t : ℂ)‖)) = ∫⁻ t in Icc u T, H t := by
    apply setLIntegral_congr_fun measurableSet_Icc
    intro t ht
    have hr := (stab_radius_bounds h₁s hu ht.1 ht.2).1
    have hr0 : 0 ≤ S₁.r u t := by linarith only [hr, ht.1]
    exact ENNReal.ofReal_mul (div_nonneg
      (h₁s.c1.lam_pos (u, t) ⟨hu, ht.1, ht.2⟩).le hr0)
  rw [heq]
  have henv : (∫⁻ t in Icc u T, J t) ≤ ENNReal.ofReal (A * ε) :=
    (lintegral_mono_set (Icc_subset_Icc hu le_rfl)).trans
      ((le_add_of_nonneg_right bot_le).trans h₂s.env)
  apply hH.trans
  apply (mul_le_mul' le_rfl (mul_le_mul' le_rfl henv)).trans_eq
  calc
    _ = ENNReal.ofReal (256 : ℝ) * ENNReal.ofReal (A * ε) := by
      norm_num only [ENNReal.ofReal_ofNat]
      ring
    _ = ENNReal.ofReal (256 * A * ε) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 256)]
      congr 1
      ring

end EmcsfAcExtension.Local
