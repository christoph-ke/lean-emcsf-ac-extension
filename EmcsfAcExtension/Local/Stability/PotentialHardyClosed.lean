module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Defs.Bounds
import EmcsfAcExtension.Local.Stability.PotentialHardyDifference
import EmcsfAcExtension.Local.Stability.DifferenceMomentsMixedHardy
import EmcsfAcExtension.Local.Stability.MomentsSections
import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux

/-! # Closing the charge-difference Hardy forcing

The actual local scalar difference remains inside the Maxwell primitive
until the proved pair Hardy clause is used. Its undifferenced companion
uses the independent mixed radial Hardy budget.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The charge-difference Hardy norm is `K |e| M Δ₀` under the proved
extended pair record. `K>0` depends only on `A` and its uniform record
constant `C`, before all fields, scales, coupling, background and data,
uniformly in minimum radii and initial derivative suprema. -/
theorem stab_charge_hardy_difference_of_stab_bounds_c1
    (A C : ℝ) (hA : 0 < A) (hC : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ^ 2 ≤ 1 / 4 → StabBounds C e T M (dataDist h₁ h₂ T) S₁ S₂ →
      (⨆ u ∈ Icc 0 T, ∫⁻ t in Icc u T, ENNReal.ofReal
        (S₁.lam u t * |S₁.Q u t - S₂.Q u t| / S₁.r u t ^ 3)) ≤
          ENNReal.ofReal (K * |e| * M * dataDist h₁ h₂ T) := by
  refine ⟨C * (1 + 2304 * A), by positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hεsq hb
  let Δ := dataDist h₁ h₂ T
  let B₀ := C * Δ
  let Φ := (supDist T S₁.phi S₂.phi).toReal
  let G := (geomDist T S₁ S₂).toReal
  let B := Φ + 8 * G * M
  have hΔ : 0 ≤ Δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hB₀ : 0 ≤ B₀ := mul_nonneg hC.le hΔ
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans h₁s.box.1
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have heHalf : |e| / 2 ≤ |e| := by linarith only [abs_nonneg e]
  have hε1 : ε ≤ 1 := by nlinarith only [hεsq, sq_nonneg (ε - 1)]
  have hΦ0 : 0 ≤ Φ := ENNReal.toReal_nonneg
  have hG0 : 0 ≤ G := ENNReal.toReal_nonneg
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have real_bound {X : ℝ≥0∞} (hx : X ≤ ENNReal.ofReal B₀) : X.toReal ≤ B₀ := by
    simpa only [ENNReal.toReal_ofReal hB₀] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hx
  have hΦ : Φ ≤ B₀ := real_bound ((le_add_of_nonneg_left bot_le).trans hb.main)
  have hmain3 : jDist T S₁ S₂ + kDist e T S₁ S₂ + geomDist T S₁ S₂ ≤ ENNReal.ofReal B₀ :=
    (le_add_of_nonneg_right bot_le).trans ((le_add_of_nonneg_right bot_le).trans
      ((le_add_of_nonneg_right bot_le).trans hb.main))
  have hG : G ≤ B₀ := real_bound ((le_add_of_nonneg_left bot_le).trans hmain3)
  have hBM : B ≤ 9 * C * M * Δ := by
    have hMB : B₀ ≤ M * B₀ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right h₁s.box.1 hB₀
    have hGM := mul_le_mul_of_nonneg_right hG (show 0 ≤ 8 * M by positivity)
    dsimp only [B, B₀] at hΦ hMB hGM ⊢
    nlinarith only [hΦ, hMB, hGM]
  apply iSup₂_le
  intro u hu
  let w := fun t => S₁.lam u t / S₁.r u t
  let X := fun t => ‖S₁.theta u t / (S₁.lam u t : ℂ) - S₂.theta u t / (S₂.lam u t : ℂ)‖
  let Y := fun t => ‖S₂.theta u t / (S₂.lam u t : ℂ)‖
  have hm : MapsTo (fun t : ℝ => (u, t)) (Icc u T) (triangle 0 T) := fun t ht => ⟨hu.1, ht.1, ht.2⟩
  have cp : ContinuousOn (fun t : ℝ => (u, t)) (Icc u T) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have aw : AEMeasurable w (volume.restrict (Icc u T)) :=
    ((h₁s.c1.c1_lam.continuousOn.comp cp hm).aemeasurable measurableSet_Icc).div
      ((h₁s.c1.c1_r.continuousOn.comp cp hm).aemeasurable measurableSet_Icc)
  have ax : AEMeasurable X (volume.restrict (Icc u T)) :=
    (((stab_out_ratio_c1 h₁s.c1).continuousOn.comp cp hm).sub
      ((stab_out_ratio_c1 h₂s.c1).continuousOn.comp cp hm)).norm.aemeasurable measurableSet_Icc
  have mx : AEMeasurable (fun t => ENNReal.ofReal M * ENNReal.ofReal (w t * X t))
      (volume.restrict (Icc u T)) := aemeasurable_const.mul
        (ENNReal.measurable_ofReal.comp_aemeasurable (aw.mul ax))
  have hIntegral : (∫⁻ t in Icc u T, ENNReal.ofReal (w t * (M * X t + B * Y t))) =
      ENNReal.ofReal M * (∫⁻ t in Icc u T, ENNReal.ofReal (w t * X t)) +
        ENNReal.ofReal B * (∫⁻ t in Icc u T, ENNReal.ofReal (w t * Y t)) := by
    have heq : (∫⁻ t in Icc u T, ENNReal.ofReal (w t * (M * X t + B * Y t))) =
        ∫⁻ t in Icc u T, ENNReal.ofReal M * ENNReal.ofReal (w t * X t) +
          ENNReal.ofReal B * ENNReal.ofReal (w t * Y t) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro t ht
      have hr : 0 ≤ S₁.r u t :=
        (div_nonneg (sub_nonneg.mpr ht.1) (by norm_num : (0 : ℝ) ≤ 4)).trans
          (stab_radius_bounds h₁s hu.1 ht.1 ht.2).1
      have hw : 0 ≤ w t := div_nonneg (h₁s.c1.lam_pos (u, t) (hm ht)).le hr
      have hx : 0 ≤ X t := norm_nonneg _
      have hy : 0 ≤ Y t := norm_nonneg _
      have hreal : w t * (M * X t + B * Y t) = M * (w t * X t) + B * (w t * Y t) := by ring
      change ENNReal.ofReal (w t * (M * X t + B * Y t)) =
        ENNReal.ofReal M * ENNReal.ofReal (w t * X t) + ENNReal.ofReal B * ENNReal.ofReal (w t * Y
            t)
      rw [hreal, ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul hM, ENNReal.ofReal_mul hB]
    rw [heq, lintegral_add_left' mx, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hX : (∫⁻ t in Icc u T, ENNReal.ofReal (w t * X t)) ≤ ENNReal.ofReal B₀ :=
    (le_iSup₂_of_le u hu le_rfl).trans ((le_add_of_nonneg_right bot_le).trans hb.hardyDiff)
  have hY : (∫⁻ t in Icc u T, ENNReal.ofReal (w t * Y t)) ≤ ENNReal.ofReal (256 * A * ε) :=
    stab_out_mixed_hardy_le h₁s h₂s hεsq hu.1 hu.2
  apply (stab_charge_difference_hardy_raw_c1 h₁s h₂s hu.1 hu.2 le_rfl).trans
  change ENNReal.ofReal (|e| / 2) *
    (∫⁻ t in Icc u T, ENNReal.ofReal (w t * (M * X t + B * Y t))) ≤ _
  rw [hIntegral]
  apply (mul_le_mul' le_rfl (add_le_add (mul_le_mul' le_rfl hX) (mul_le_mul' le_rfl hY))).trans
  rw [← ENNReal.ofReal_mul hM, ← ENNReal.ofReal_mul hB,
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ |e| * (M * B₀ + (9 * C * M * Δ) * (256 * A * 1)) := by gcongr
    _ = _ := by dsimp only [B₀]; ring

end EmcsfAcExtension.Local
