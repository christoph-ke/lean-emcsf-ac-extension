module

public import EmcsfAcExtension.Local.Stability.JCloseInitialRadial
import EmcsfAcExtension.Infra.HardyBV

/-! # Data-only initial radial Hardy estimates

The common weight is exactly one half. The totalized value at the initial
axis point is immaterial and is retained in both real integrands.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local.Stab

/-- The individual initial radial Hardy integrand is the exact weighted
deviation of the initial datum from its radial average, including at zero. -/
theorem initial_weighted_ratio_eq_deviation {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hs : StabSetting e T ε M A S h) {v : ℝ} (hv : v ∈ Icc 0 T) :
    S.lam 0 v / S.r 0 v * ‖S.theta 0 v / S.lam 0 v‖ =
      (1 / 2 : ℝ) / (∫ _s in 0..v, (1 / 2 : ℝ)) *
        ‖h v - radialAverage (fun _ => (1 / 2 : ℝ)) h 0 v‖ := by
  rcases hv.1.eq_or_lt with hv₀ | hv₀
  · rw [← hv₀, (hs.data.1 0 ⟨le_rfl, hs.pos.le⟩).1]
    simp only [zero_div, div_zero, zero_mul, intervalIntegral.integral_same]
  have hx : S.theta 0 v / (S.lam 0 v : ℂ) = h v - S.phi 0 v := by
    rw [← (hs.data.1 v hv).2]
    simp only [Fields.a]
    ring
  rw [hx, initial_lam_of_stabSetting hs hv, (hs.data.1 v hv).1,
    intervalIntegral.integral_const, smul_eq_mul, sub_zero,
    initial_radialAverage_eq_phi hs hv hv₀]
  congr 2
  ring

/-- Individual initial Hardy estimate, with exact universal coefficient one.
Absolute continuity of the standing datum gives integrability at the axis. -/
theorem initial_hardy {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hs : StabSetting e T ε M A S h) :
    IntervalIntegrable (fun v => S.lam 0 v / S.r 0 v * ‖S.theta 0 v / S.lam 0 v‖)
      volume 0 T ∧
    (∫ v in 0..T, S.lam 0 v / S.r 0 v * ‖S.theta 0 v / S.lam 0 v‖) ≤ datumVar h T := by
  have hac := initial_datum_ac hs
  have hh := integrable_and_integral_weighted_deviation_le_variation hs.pos.le
    (intervalIntegrable_const (c := (1 / 2 : ℝ))) (fun _ _ => by norm_num)
    (by simpa only [uIcc_of_le hs.pos.le] using hac.continuousOn)
    (hac.boundedVariationOn_Icc hs.pos.le)
  refine ⟨hh.1.congr (fun v hv => (initial_weighted_ratio_eq_deviation hs
    (by simpa only [uIcc_of_le hs.pos.le] using uIoc_subset_uIcc hv)).symm), ?_⟩
  calc
    _ = _ := intervalIntegral.integral_congr (fun v hv => initial_weighted_ratio_eq_deviation hs
      (by simpa only [uIcc_of_le hs.pos.le] using hv))
    _ ≤ datumVar h T := hh.2

/-- Initial ratio-difference Hardy estimate from the difference datum alone.
The coefficient one is universal, independent of all physical parameters,
box envelopes, lengths and derivative suprema. -/
theorem initial_hardy_difference {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (hs₁ : StabSetting e T ε M A S₁ h₁) (hs₂ : StabSetting e T ε M A S₂ h₂) :
    IntervalIntegrable (fun v => S₁.lam 0 v / S₁.r 0 v *
      ‖S₁.theta 0 v / S₁.lam 0 v - S₂.theta 0 v / S₂.lam 0 v‖) volume 0 T ∧
    (∫ v in 0..T, S₁.lam 0 v / S₁.r 0 v *
      ‖S₁.theta 0 v / S₁.lam 0 v - S₂.theta 0 v / S₂.lam 0 v‖) ≤ dataDist h₁ h₂ T := by
  have hac := (initial_datum_ac hs₁).sub (initial_datum_ac hs₂)
  have hh := integrable_and_integral_weighted_deviation_le_variation hs₁.pos.le
    (intervalIntegrable_const (c := (1 / 2 : ℝ))) (fun _ _ => by norm_num)
    (by simpa only [uIcc_of_le hs₁.pos.le] using hac.continuousOn)
    (hac.boundedVariationOn_Icc hs₁.pos.le)
  have heq (v : ℝ) (hv : v ∈ Icc 0 T) :
      S₁.lam 0 v / S₁.r 0 v * ‖S₁.theta 0 v / S₁.lam 0 v - S₂.theta 0 v / S₂.lam 0 v‖ =
        (1 / 2 : ℝ) / (∫ s in 0..v, (1 / 2 : ℝ)) *
          ‖(h₁ - h₂) v - radialAverage (fun _ => (1 / 2 : ℝ)) (h₁ - h₂) 0 v‖ := by
    rcases hv.1.eq_or_lt with hv₀ | hv₀
    · rw [← hv₀, (hs₁.data.1 0 ⟨le_rfl, hs₁.pos.le⟩).1]
      simp only [zero_div, div_zero, zero_mul, intervalIntegral.integral_same]
    have hx : S₁.theta 0 v / (S₁.lam 0 v : ℂ) - S₂.theta 0 v / (S₂.lam 0 v : ℂ) =
        (h₁ v - h₂ v) - (S₁.phi 0 v - S₂.phi 0 v) := by
      rw [← (hs₁.data.1 v hv).2, ← (hs₂.data.1 v hv).2]
      simp only [Fields.a]
      ring
    rw [hx, initial_lam_of_stabSetting hs₁ hv, (hs₁.data.1 v hv).1,
      intervalIntegral.integral_const, smul_eq_mul, sub_zero,
      initial_radialAverage_sub hs₁ hs₂ hv hv₀, Pi.sub_apply]
    congr 2
    ring
  have hi : IntervalIntegrable (fun v => S₁.lam 0 v / S₁.r 0 v *
      ‖S₁.theta 0 v / S₁.lam 0 v - S₂.theta 0 v / S₂.lam 0 v‖) volume 0 T := by
    apply hh.1.congr
    intro v hv
    exact (heq v (by simpa only [uIcc_of_le hs₁.pos.le] using uIoc_subset_uIcc hv)).symm
  refine ⟨hi, ?_⟩
  calc
    _ = _ := intervalIntegral.integral_congr (fun v hv => heq v (by
      simpa only [uIcc_of_le hs₁.pos.le] using hv))
    _ ≤ datumVar (h₁ - h₂) T := hh.2
    _ ≤ dataDist h₁ h₂ T := le_add_of_nonneg_left (norm_nonneg _)

end EmcsfAcExtension.Local.Stab
