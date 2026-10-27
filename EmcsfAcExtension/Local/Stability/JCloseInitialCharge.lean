module

public import EmcsfAcExtension.Local.Stability.JCloseInitialRadial
import EmcsfAcExtension.Local.Stability.SourceDifferenceEMAlgebra
import EmcsfAcExtension.Local.Stability.MomentsSections
import EmcsfAcExtension.Local.Calculus.RelativeCharge
import EmcsfAcExtension.Local.Calculus.C1ToSolution2

/-! # Data-only comparison of the initial Maxwell constraint

The common radius and expansion remove all geometric differences. The
oscillatory current is subtracted before integrating or dividing by radius.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local.Stab

/-- The initial Maxwell constraint in the common radius label.
All scalar and oscillatory factors retain their exact coefficients. -/
theorem initial_charge_constraint {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hs : StabSetting e T ε M A S h) {v : ℝ} (hv : v ∈ Icc 0 T) :
    S.Q 0 v = -e * ∫ s in 0..v, s / 4 *
      (starRingEnd ℂ (S.phi 0 s) * (S.theta 0 s / S.lam 0 s)).im := by
  rw [oscillatory_charge_constraint (hs.c1.toIsSolution hs.pos) hv.1
    (show outSeg 0 0 v ⊆ triangle 0 T from by
      rintro ⟨x, y⟩ ⟨hx, hp⟩
      change x = 0 at hx
      subst x
      exact ⟨le_rfl, hp.1, hp.2.trans hv.2⟩)]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hmem
  rw [uIcc_of_le hv.1] at hmem
  have hsT : s ∈ Icc 0 T := ⟨hmem.1, hmem.2.trans hv.2⟩
  dsimp only
  rw [initial_lam_of_stabSetting hs hsT, (hs.data.1 s hsT).1]
  ring

private theorem initial_current_continuous {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hs : StabSetting e T ε M A S h) {v : ℝ} (hv : v ∈ Icc 0 T) :
    ContinuousOn (fun s => s / 4 *
      (starRingEnd ℂ (S.phi 0 s) * (S.theta 0 s / S.lam 0 s)).im) (Icc 0 v) := by
  have hmap : MapsTo (fun s => (0, s)) (Icc 0 v) (triangle 0 T) :=
    fun s hs => ⟨le_rfl, hs.1, hs.2.trans hv.2⟩
  have hφ := hs.c1.c1_phi.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have hx := (stab_out_ratio_c1 hs.c1).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  simpa only [Function.comp_apply, Pi.mul_def] using!
    (continuousOn_id.div_const 4).mul
      (Complex.continuous_im.comp_continuousOn (hφ.star.mul hx))

/-- Initial normalized charge comparison from the data only.
The coefficient `3` is universal, uniformly in the background, coupling,
length, envelope and all derivatives; the radius-square weight is exact. -/
theorem initial_charge_difference_le {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (hs₁ : StabSetting e T ε M A S₁ h₁) (hs₂ : StabSetting e T ε M A S₂ h₂)
    (hε₁ : ε ≤ 1) {v : ℝ} (hv : v ∈ Icc 0 T) :
    |S₁.Q 0 v - S₂.Q 0 v| ≤ 3 * |e| * M * dataDist h₁ h₂ T * S₁.r 0 v ^ 2 := by
  let δ := dataDist h₁ h₂ T
  have hδ : 0 ≤ δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hM : 0 < M := zero_lt_one.trans_le hs₂.box.1
  have hεM : ε ≤ M := hε₁.trans hs₂.box.1
  let f := fun s => s / 4 *
    ((starRingEnd ℂ (S₁.phi 0 s) * (S₁.theta 0 s / S₁.lam 0 s)).im -
      (starRingEnd ℂ (S₂.phi 0 s) * (S₂.theta 0 s / S₂.lam 0 s)).im)
  have hi₁ := (initial_current_continuous hs₁ hv).intervalIntegrable_of_Icc (μ := volume) hv.1
  have hi₂ := (initial_current_continuous hs₂ hv).intervalIntegrable_of_Icc (μ := volume) hv.1
  have heq : S₁.Q 0 v - S₂.Q 0 v = -e * ∫ s in 0..v, f s := by
    rw [initial_charge_constraint hs₁ hv, initial_charge_constraint hs₂ hv, ← mul_sub,
      ← intervalIntegral.integral_sub hi₁ hi₂]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp [f]
    ring
  have hbound (s : ℝ) (hs : s ∈ uIoc 0 v) : ‖f s‖ ≤ v / 4 * (3 * M * δ) := by
    rw [uIoc_of_le hv.1] at hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.trans hv.2⟩
    have hp : (0, s) ∈ triangle 0 T := ⟨le_rfl, hsT.1, hsT.2⟩
    have hφ := (hs₁.box.2 (0, s) hp).2.2.2.2.2.2
    have hx₂ := (le_add_of_nonneg_right (norm_nonneg _)).trans
      (hs₂.box.2 (0, s) hp).2.2.2.2.2.1
    have hdiff := initial_scalar_ratio_difference_le hs₁ hs₂ hsT
    have him := abs_im_scalar_current_sub_le (S₁.phi 0 s) (S₂.phi 0 s)
      (S₁.theta 0 s / S₁.lam 0 s) (S₂.theta 0 s / S₂.lam 0 s)
    have hprod₁ := mul_le_mul hφ hdiff.2 (norm_nonneg _) hM.le
    have hprod₂ := mul_le_mul hdiff.1 hx₂ (norm_nonneg _) hδ
    have hδim :
        |(starRingEnd ℂ (S₁.phi 0 s) * (S₁.theta 0 s / S₁.lam 0 s)).im -
          (starRingEnd ℂ (S₂.phi 0 s) * (S₂.theta 0 s / S₂.lam 0 s)).im| ≤ 3 * M * δ := by
      have hεδ := mul_le_mul_of_nonneg_right hεM hδ
      dsimp only [δ] at *
      nlinarith only [him, hprod₁, hprod₂, hεδ]
    dsimp only [f]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (div_nonneg hs.1.le (by norm_num : (0 : ℝ) ≤ 4))]
    exact mul_le_mul (div_le_div_of_nonneg_right hs.2 (by norm_num)) hδim
      (abs_nonneg _) (div_nonneg hv.1 (by norm_num))
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [heq, abs_mul, abs_neg]
  have h := mul_le_mul_of_nonneg_left hint (abs_nonneg e)
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hv.1] at h
  apply h.trans_eq
  rw [(hs₁.data.1 v hv).1]
  dsimp only [δ]
  ring

end EmcsfAcExtension.Local.Stab
