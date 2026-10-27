module

public import EmcsfAcExtension.Local.Stability.Moments

/-! # Localized individual Hardy budget

The individual Hardy estimate can retain the starting label in its
right-hand integral. This is needed when comparing forcing on one section.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local

variable {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}

private theorem out_damping_local_aux (hset : StabSetting e T ε M A S h) {u v p : ℝ}
    (hp : p ≤ 1 - ε ^ 2) (hu : 0 ≤ u) (_huv : u < v) (hvT : v ≤ T)
    {s : ℝ} (hs : s ∈ Ioo u v) :
    p * (S.lam u s / ∫ t in u..s, S.lam u t) ≤
      S.lam u s / S.r u s * (1 - ‖S.theta u s / (S.lam u s : ℂ)‖ ^ 2) := by
  rw [stab_radius_out_integral hset hu hs.1.le (hs.2.le.trans hvT)]
  have hbox := hset.box.2 (u, s) ⟨hu, hs.1.le, hs.2.le.trans hvT⟩
  have hx : ‖S.theta u s / (S.lam u s : ℂ)‖ ≤ ε :=
    (le_add_of_nonneg_right (norm_nonneg (S.xi u s / (S.nu u s : ℂ)))).trans
      hbox.2.2.2.2.2.1
  have hsq := mul_self_le_mul_self (norm_nonneg _) hx
  have hp' : p ≤ 1 - ‖S.theta u s / (S.lam u s : ℂ)‖ ^ 2 := by
    nlinarith only [hp, hsq]
  have hnonneg : 0 ≤ S.lam u s / S.r u s := div_nonneg
    (hset.c1.lam_pos (u, s) ⟨hu, hs.1.le, hs.2.le.trans hvT⟩).le
    (hset.c1.r_pos (u, s) ⟨hu, hs.1.le, hs.2.le.trans hvT⟩ hs.1).le
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp' hnonneg

/-- The outgoing linear Hardy estimate assuming the exact sectional
reconstruction identity. The coefficient is the universal number `16/3`;
it is independent of every solution parameter and of derivative suprema.
The individual-field exponent is `3/4`, with `ε² ≤ 1/4`. -/
theorem stab_out_hardy_local_of_identity (hset : StabSetting e T ε M A S h)
    (hidentity : ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ T →
      HasDerivWithinAt (fun s => S.theta u s / (S.lam u s : ℂ))
        (jC1 (triangle 0 T) S u v / ((1 - S.mu u v : ℝ) : ℂ) -
          (S.lam u v / S.r u v * (1 - ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2)) •
            (S.theta u v / (S.lam u v : ℂ))) (Icc u T) v)
    (hε : ε ^ 2 ≤ 1 / 4) {u : ℝ} (hu : 0 ≤ u) (huT : u ≤ T) :
    (∫⁻ s in Ioc u T, ENNReal.ofReal
      (S.lam u s / S.r u s * ‖S.theta u s / (S.lam u s : ℂ)‖)) ≤
        ENNReal.ofReal (16 / 3) * ∫⁻ s in Icc u T, outEnv 0 (jC1 (triangle 0 T) S) s := by
  have hl : ContinuousOn (S.lam u) (uIcc u T) := by
    rw [uIcc_of_le huT]
    exact hset.c1.c1_lam.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn (fun s hs => ⟨hu, hs.1, hs.2⟩)
  have hq := (stab_out_forcing_measurable hset hu huT le_rfl).mono_measure
    (Measure.restrict_mono (show Ioc u T ⊆ Icc u T from
      fun _ hs => ⟨hs.1.le, hs.2⟩) le_rfl)
  have hi := stab_radial_hardy_of_identity (α := fun _ => 0) (p := 3 / 4) huT
    (by norm_num) hl.intervalIntegrable
    (fun s hs => (hset.c1.lam_pos (u, s) ⟨hu, hs.1, hs.2⟩).le)
    (stab_out_ratio_ac hset hu huT le_rfl) (stab_out_ratio_axis hset ⟨hu, huT⟩) hq
    (fun s hs => out_damping_local_aux hset (by linarith only [hε]) hu
      (hs.1.trans hs.2) le_rfl hs)
    (fun s hs => by
      simpa only [zero_smul, sub_zero] using hidentity u s hu hs.1 hs.2.le)
  have hleft : (∫⁻ s in Ioc u T, ENNReal.ofReal
      (S.lam u s / S.r u s * ‖S.theta u s / (S.lam u s : ℂ)‖)) =
      ∫⁻ s in Ioc u T, ENNReal.ofReal
        (S.lam u s / (∫ t in u..s, S.lam u t) * ‖S.theta u s / (S.lam u s : ℂ)‖) := by
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro s hs
    dsimp only
    rw [stab_radius_out_integral hset hu hs.1.le hs.2]
  rw [hleft]
  apply hi.trans
  have hforce : (∫⁻ s in Ioc u T,
      ENNReal.ofReal ‖jC1 (triangle 0 T) S u s / ((1 - S.mu u s : ℝ) : ℂ)‖) ≤
      ENNReal.ofReal 4 * ∫⁻ s in Icc u T, outEnv 0 (jC1 (triangle 0 T) S) s := by
    calc
      _ ≤ ∫⁻ s in Ioc u T, ENNReal.ofReal 4 * outEnv 0 (jC1 (triangle 0 T) S) s := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        have hf := ENNReal.ofReal_le_ofReal
          (stab_forcing_norm_le hset hu hs.1.le hs.2 (jC1 (triangle 0 T) S u s))
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)] at hf
        have hj : ENNReal.ofReal ‖jC1 (triangle 0 T) S u s‖ ≤
            outEnv 0 (jC1 (triangle 0 T) S) s := by
          rw [ofReal_norm]
          exact enorm_le_normEnvelope (jC1 (triangle 0 T) S) ⟨hu, hs.1.le⟩
        exact hf.trans (mul_le_mul' le_rfl hj)
      _ = ENNReal.ofReal 4 * ∫⁻ s in Ioc u T, outEnv 0 (jC1 (triangle 0 T) S) s :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := mul_le_mul' le_rfl (lintegral_mono_set
        (show Ioc u T ⊆ Icc u T from fun s hs => ⟨hs.1.le, hs.2⟩))
  calc
    _ ≤ ENNReal.ofReal ((3 / 4 : ℝ)⁻¹) *
        (ENNReal.ofReal 4 * ∫⁻ s in Icc u T, outEnv 0 (jC1 (triangle 0 T) S) s) :=
      mul_le_mul' le_rfl hforce
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ (3 / 4 : ℝ)⁻¹)]
      norm_num


end EmcsfAcExtension.Local
