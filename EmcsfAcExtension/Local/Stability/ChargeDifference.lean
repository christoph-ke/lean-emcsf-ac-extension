module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.ChargeDifferenceRaw
import EmcsfAcExtension.Local.Stability.DifferenceMomentsCloseOut
import EmcsfAcExtension.Local.Stability.FieldDifference

/-! # Scale-correct charge comparison

The common-label Maxwell subtraction retains its endpoint radius
squared. The outgoing ratio and scalar field comparisons supply the
three terms in the approved source bound.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [node restart-stab-charge-difference]
The charge difference weighted by the first radius squared,
charged_SF_new_version.tex:L5109–5119 and approved internal project record. Constants depend only on
the fixed box and `A`, before all other parameters and the solution pair,
uniformly as the axis is approached and for arbitrary coupling. -/
theorem stab_charge_difference (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ T →
          |S₁.Q u v - S₂.Q u v| / S₁.r u v ^ 2 ≤ C * |e| *
            (M * (jDist T S₁ S₂).toReal + ε * dataDist h₁ h₂ T +
              M * ε * (geomDist T S₁ S₂).toReal) := by
  obtain ⟨η₁, C₁, hη₁, hC₁, hOut⟩ := stab_out_difference A hA
  obtain ⟨η₂, C₂, hη₂, hC₂, hField⟩ := stab_field_difference A hA
  refine ⟨min η₁ (min η₂ (1 / 12)), 4 * (C₁ + C₂ + 1),
    lt_min hη₁ (lt_min hη₂ (by norm_num)), by positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall u v hu huv hvT
  let J := (jDist T S₁ S₂).toReal
  let G := (geomDist T S₁ S₂).toReal
  let H := J + ε * G
  let L := dataDist h₁ h₂ T + J + ε * G
  let X := (supDist T (fun u v => S₁.theta u v / (S₁.lam u v : ℂ))
    (fun u v => S₂.theta u v / (S₂.lam u v : ℂ))).toReal
  let Φ := (supDist T S₁.phi S₂.phi).toReal
  have hJ : 0 ≤ J := ENNReal.toReal_nonneg
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hΔ : 0 ≤ dataDist h₁ h₂ T := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hM : 0 ≤ M := le_trans (by norm_num) h₁s.box.1
  have hH : 0 ≤ H := add_nonneg hJ (mul_nonneg hε0 hG)
  have hL : 0 ≤ L := add_nonneg (add_nonneg hΔ hJ) (mul_nonneg hε0 hG)
  have hσ : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hεsq : ε ^ 2 ≤ 1 / 12 :=
    ((le_add_of_nonneg_right hσ).trans hsmall).trans
      ((min_le_right _ _).trans (min_le_right _ _))
  have hε1 : ε ≤ 1 := by nlinarith only [hεsq, sq_nonneg (ε - 1)]
  have hεM : ε ≤ M := hε1.trans h₁s.box.1
  have hOutB := hOut T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hsmall.trans (min_le_left _ _))
  have hFieldB := hField T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
    (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hX : X ≤ C₁ * H := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      ((le_add_of_nonneg_right bot_le).trans hOutB)
    change X ≤ (ENNReal.ofReal (C₁ * H)).toReal at hh
    simpa only [ENNReal.toReal_ofReal (mul_nonneg hC₁.le hH)] using! hh
  have hΦ : Φ ≤ C₂ * L := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      ((le_add_of_nonneg_left bot_le).trans hFieldB)
    change Φ ≤ (ENNReal.ofReal (C₂ * L)).toReal at hh
    simpa only [ENNReal.toReal_ofReal (mul_nonneg hC₂.le hL)] using! hh
  have hMX := mul_le_mul_of_nonneg_left hX hM
  have hεΦ := mul_le_mul_of_nonneg_left hΦ hε0
  have heJ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hεM hJ) hC₂.le
  have heG := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hεM (mul_nonneg hε0 hG)) hC₂.le
  have hbudget : M * X + ε * Φ + M * ε * G ≤
      (C₁ + C₂ + 1) * (M * J + ε * dataDist h₁ h₂ T + M * ε * G) := by
    dsimp only [H, L] at hMX hεΦ
    have hMJ := mul_nonneg hM hJ
    have hCΔ := mul_nonneg (show 0 ≤ C₁ + 1 by positivity) (mul_nonneg hε0 hΔ)
    nlinarith only [hMX, hεΦ, heJ, heG, hMJ, hCΔ]
  apply (stab_charge_difference_raw h₁s h₂s hu huv hvT).trans
  have hb := mul_le_mul_of_nonneg_left hbudget (show 0 ≤ 4 * |e| by positivity)
  apply hb.trans_eq
  ring

end EmcsfAcExtension.Local
