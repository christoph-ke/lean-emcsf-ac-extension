module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.MomentsSections
import EmcsfAcExtension.Infra.Triangle

/-! # Incoming ratio differences on the potential triangle

The incoming weighted difference is integrated in its own orientation.
This supplies the area norm required by `StabBounds.xiRatioArea`.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The triangle integral of the incoming ratio difference is at most
`4 T` times its incoming Hardy norm. The numerical coefficient is
universal, uniformly in the background, coupling and minimum radius.
The conclusion is through the axis, and uses no main comparison premise. -/
theorem Stab.xi_ratio_area_le
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {v : ℝ} (hv : v ∈ Icc 0 T) :
    (∫⁻ p in triangle 0 v, ENNReal.ofReal
      (‖S₁.xi p.1 p.2 / (S₁.nu p.1 p.2 : ℂ) -
        S₂.xi p.1 p.2 / (S₂.nu p.1 p.2 : ℂ)‖ / (p.2 - p.1))) ≤
      ENNReal.ofReal (4 * T) *
        (⨆ w ∈ Icc 0 T, ∫⁻ u in Icc 0 w, ENNReal.ofReal
          (-S₁.nu u w / S₁.r u w *
            ‖S₁.xi u w / (S₁.nu u w : ℂ) - S₂.xi u w / (S₂.nu u w : ℂ)‖)) := by
  classical
  let Y := (triangle 0 v).indicator
    (fun p : ℝ × ℝ => (S₁.xi p.1 p.2 / (S₁.nu p.1 p.2 : ℂ) - S₂.xi p.1 p.2 / (S₂.nu p.1 p.2 : ℂ)))
  let F := fun p : ℝ × ℝ => ENNReal.ofReal (‖Y p‖ / (p.2 - p.1))
  let K := ⨆ w ∈ Icc 0 T, ∫⁻ u in Icc 0 w, ENNReal.ofReal
    (-S₁.nu u w / S₁.r u w *
      ‖S₁.xi u w / (S₁.nu u w : ℂ) - S₂.xi u w / (S₂.nu u w : ℂ)‖)
  have hsub : triangle 0 v ⊆ triangle 0 T := by
    intro p hp
    exact ⟨hp.1, hp.2.1, hp.2.2.trans hv.2⟩
  have hY : Measurable Y := by
    dsimp only [Y]
    rw [← Set.piecewise_eq_indicator]
    exact (((stab_in_ratio_c1 h₁s.c1).continuousOn.sub (stab_in_ratio_c1 h₂s.c1).continuousOn).mono
        hsub).measurable_piecewise
      continuousOn_const (measurableSet_triangle 0 v)
  have hF : Measurable F :=
    ENNReal.measurable_ofReal.comp (hY.norm.div (measurable_snd.sub measurable_fst))
  have hsection : ∀ w ∈ Icc 0 v,
      (∫⁻ u in Icc 0 w, F (u, w)) ≤ ENNReal.ofReal (4 : ℝ) * K := by
    intro w hw
    have hwT := hw.2.trans hv.2
    have hpoint : (∫⁻ u in Icc 0 w, F (u, w)) ≤ 4 *
        ∫⁻ u in Icc 0 w, ENNReal.ofReal
          (-S₁.nu u w / S₁.r u w * ‖(S₁.xi u w / (S₁.nu u w : ℂ) - S₂.xi u w / (S₂.nu u w : ℂ))‖) :=
              by
      rw [← lintegral_const_mul' 4 _ (by norm_num)]
      apply setLIntegral_mono' measurableSet_Icc
      intro u hu
      have hpv : (u, w) ∈ triangle 0 v := ⟨hu.1, hu.2, hw.2⟩
      have hpT := hsub hpv
      dsimp only [F, Y]
      rw [indicator_of_mem hpv]
      rcases hu.2.eq_or_lt with rfl | huw
      · simp only [sub_self, div_zero, ENNReal.ofReal_zero]
        exact bot_le
      have hr := h₁s.c1.r_pos (u, w) hpT huw
      have hb := h₁s.box.2 (u, w) hpT
      have hrb := (stab_radius_bounds h₁s hu.1 huw.le hwT).2
      have hgap : 0 < w - u := sub_pos.mpr huw
      have hweight : 1 / (w - u) ≤ 4 * (-S₁.nu u w / S₁.r u w) := by
        rw [← mul_div_assoc, div_le_div_iff₀ hgap hr]
        have hn : 1 ≤ 4 * (-S₁.nu u w) := by linarith only [hb.2.2.1]
        have hmul := mul_le_mul_of_nonneg_right hn hgap.le
        linarith only [hrb, hmul]
      rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      apply ENNReal.ofReal_le_ofReal
      have hmul := mul_le_mul_of_nonneg_right hweight
        (norm_nonneg ((S₁.xi u w / (S₁.nu u w : ℂ) - S₂.xi u w / (S₂.nu u w : ℂ))))
      simpa only [one_div_mul_eq_div, mul_assoc] using hmul
    norm_num only [ENNReal.ofReal_ofNat]
    exact hpoint.trans (mul_le_mul' le_rfl
      (le_iSup₂_of_le w ⟨hw.1, hwT⟩ le_rfl))
  calc
    _ = ∫⁻ p in triangle 0 v, F p := by
      apply setLIntegral_congr_fun (measurableSet_triangle 0 v)
      intro p hp
      dsimp only [F, Y]
      rw [indicator_of_mem hp]
    _ = ∫⁻ w in Icc 0 v, ∫⁻ u in Icc 0 w, F (u, w) :=
      by
        rw [Measure.volume_eq_prod]
        exact lintegral_triangle_eq_lintegral_lintegral_symm hF
    _ ≤ ∫⁻ w in Icc 0 v, ENNReal.ofReal (4 : ℝ) * K :=
      setLIntegral_mono' measurableSet_Icc hsection
    _ = ENNReal.ofReal ((4) * v) * K := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      ring
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left hv.2 (by norm_num : (0 : ℝ) ≤ 4))) le_rfl

end EmcsfAcExtension.Local
