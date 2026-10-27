module

public import EmcsfAcExtension.Local.Stability.JCloseInitial
public import EmcsfAcExtension.Local.Stability.JCloseInitialGeometry
public import EmcsfAcExtension.Infra.Hardy
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Infra.HardyBV
import EmcsfAcExtension.Infra.W11.Distance

/-! # Initial scalar and ratio comparison from the data alone

The initial geometry is identical for the two fields. Its radial averages
therefore commute with subtraction, without any global comparison term.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local.Stab

/-- Pointwise difference of the two AC data from the endpoint-plus-variation
distance, with exact coefficient one independent of every parameter. -/
theorem initial_datum_difference_le {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (hs₁ : StabSetting e T ε M A S₁ h₁) (hs₂ : StabSetting e T ε M A S₂ h₂)
    {v : ℝ} (hv : v ∈ Icc 0 T) : ‖h₁ v - h₂ v‖ ≤ dataDist h₁ h₂ T := by
  simpa only [W11.intervalDist, W11.intervalNorm, dataDist, datumVar, Pi.sub_apply] using
    W11.norm_sub_le_intervalDist
      ((initial_datum_ac hs₁).boundedVariationOn_Icc hs₁.pos.le)
      ((initial_datum_ac hs₂).boundedVariationOn_Icc hs₂.pos.le) hv

/-- The initial scalar is the radial average with the common weight `1/2`.
The axis value is handled separately, because a totalized average is zero there. -/
theorem initial_radialAverage_eq_phi {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hs : StabSetting e T ε M A S h) {v : ℝ} (hv : v ∈ Icc 0 T) (hv₀ : 0 < v) :
    radialAverage (fun _ => (1 / 2 : ℝ)) h 0 v = S.phi 0 v := by
  have hrec := Area.outgoing_radial_reconstruction hs.c1 le_rfl hv.1 hv.2
  have hi : (∫ s in 0..v, (1 / 2 : ℝ) • h s) = (S.r 0 v : ℂ) * S.phi 0 v := by
    rw [hrec]
    apply intervalIntegral.integral_congr
    intro s hs'
    rw [uIcc_of_le hv.1] at hs'
    have hsT : s ∈ Icc 0 T := ⟨hs'.1, hs'.2.trans hv.2⟩
    dsimp only
    rw [initial_lam_of_stabSetting hs hsT, (hs.data.1 s hsT).2, Complex.real_smul]
  have hr : ∫ s in 0..v, (1 / 2 : ℝ) = S.r 0 v := by
    rw [intervalIntegral.integral_const, smul_eq_mul, (hs.data.1 v hv).1]
    ring
  rw [radialAverage, hr, hi, Complex.real_smul, Complex.ofReal_inv, ← mul_assoc,
    inv_mul_cancel₀ (ofReal_ne_zero.mpr (hs.c1.r_pos (0, v) ⟨le_rfl, hv.1, hv.2⟩ hv₀).ne'),
    one_mul]

/-- Subtract the two initial radial averages in their common geometry.
The coefficient is exactly one, and all identities hold at the given endpoint. -/
theorem initial_radialAverage_sub {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (hs₁ : StabSetting e T ε M A S₁ h₁) (hs₂ : StabSetting e T ε M A S₂ h₂)
    {v : ℝ} (hv : v ∈ Icc 0 T) (hv₀ : 0 < v) :
    radialAverage (fun _ => (1 / 2 : ℝ)) (h₁ - h₂) 0 v = S₁.phi 0 v - S₂.phi 0 v := by
  have hsub : uIcc 0 v ⊆ uIcc 0 T := by
    rw [uIcc_of_le hv.1, uIcc_of_le hs₁.pos.le]
    exact Icc_subset_Icc le_rfl hv.2
  have hc₁ := (initial_datum_ac hs₁).continuousOn.mono hsub
  have hc₂ := (initial_datum_ac hs₂).continuousOn.mono hsub
  have hi₁ := (intervalIntegrable_const (μ := volume) (c := (1 / 2 : ℝ))).smul_continuousOn hc₁
  have hi₂ := (intervalIntegrable_const (μ := volume) (c := (1 / 2 : ℝ))).smul_continuousOn hc₂
  rw [← initial_radialAverage_eq_phi hs₁ hv hv₀, ← initial_radialAverage_eq_phi hs₂ hv hv₀]
  dsimp only [radialAverage]
  simp_rw [Pi.sub_apply, smul_sub]
  rw [intervalIntegral.integral_sub hi₁ hi₂, smul_sub]

/-- The initial scalar and outgoing ratio differences have data-only
bounds `Δ₀` and `2 Δ₀`, with universal coefficients. No final or global
solution comparison is used to control the initial constraints. -/
theorem initial_scalar_ratio_difference_le {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (hs₁ : StabSetting e T ε M A S₁ h₁) (hs₂ : StabSetting e T ε M A S₂ h₂)
    {v : ℝ} (hv : v ∈ Icc 0 T) :
    ‖S₁.phi 0 v - S₂.phi 0 v‖ ≤ dataDist h₁ h₂ T ∧
    ‖S₁.theta 0 v / S₁.lam 0 v - S₂.theta 0 v / S₂.lam 0 v‖ ≤ 2 * dataDist h₁ h₂ T := by
  have hδ := initial_datum_difference_le hs₁ hs₂ hv
  have hφ : ‖S₁.phi 0 v - S₂.phi 0 v‖ ≤ dataDist h₁ h₂ T := by
    rcases hv.1.eq_or_lt with hv₀ | hv₀
    · rw [← hv₀, ← (hs₁.c1.axis 0 ⟨le_rfl, le_rfl, hs₁.pos.le⟩).2.2.2.2.1,
        ← (hs₂.c1.axis 0 ⟨le_rfl, le_rfl, hs₂.pos.le⟩).2.2.2.2.1,
        (hs₁.data.1 0 ⟨le_rfl, hs₁.pos.le⟩).2, (hs₂.data.1 0 ⟨le_rfl, hs₂.pos.le⟩).2]
      simpa only [← hv₀] using hδ
    rw [← initial_radialAverage_sub hs₁ hs₂ hv hv₀]
    have hsub : uIcc 0 v ⊆ uIcc 0 T := by
      rw [uIcc_of_le hv.1, uIcc_of_le hs₁.pos.le]
      exact Icc_subset_Icc le_rfl hv.2
    have hc : ContinuousOn (h₁ - h₂) (Icc 0 v) := by
      simpa only [uIcc_of_le hv.1] using
        ((initial_datum_ac hs₁).sub (initial_datum_ac hs₂)).continuousOn.mono hsub
    have hδ0 : 0 ≤ dataDist h₁ h₂ T := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
    apply norm_radialAverage_le_of_bound hv.1
      (intervalIntegrable_const (μ := volume) (c := (1 / 2 : ℝ)))
      (fun _ _ => by norm_num) hc hδ0
    intro s hs
    exact initial_datum_difference_le hs₁ hs₂ ⟨hs.1, hs.2.trans hv.2⟩
  have heq : S₁.theta 0 v / (S₁.lam 0 v : ℂ) - S₂.theta 0 v / (S₂.lam 0 v : ℂ) =
      (h₁ v - h₂ v) - (S₁.phi 0 v - S₂.phi 0 v) := by
    rw [← (hs₁.data.1 v hv).2, ← (hs₂.data.1 v hv).2]
    simp only [Fields.a]
    ring
  refine ⟨hφ, ?_⟩
  rw [heq]
  exact (norm_sub_le _ _).trans (by linarith only [hδ, hφ])

end EmcsfAcExtension.Local.Stab
