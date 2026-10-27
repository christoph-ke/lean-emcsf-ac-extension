module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMass
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassIndividualBudget

/-! # Outgoing weighted mass comparison

The landed normalized mass Volterra estimate retains the singular
weighted norm. Extracting that norm and the individual mass budgets
gives approved internal project record (WM+), needed by the geometric cross derivatives
at charged_SF_new_version.tex:L5439–5441.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [node restart-sec-bv-stability-independent#outgoing-weighted-mass-difference]
The outgoing weighted mass difference and both undifferenced budgets.
The threshold and constant depend only on `A` and the fixed geometric
box, before all parameters, data and the pair, uniformly in the minimum
radius and derivative suprema. No uniform mass error is integrated
against `1/r`; the weighted conclusion of the Volterra estimate is used. -/
theorem Stab.outgoing_weighted_mass_difference (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        ((⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ENNReal.ofReal
          (S₁.lam u v / S₁.r u v * |S₁.mu u v - S₂.mu u v|)) ≤
          ENNReal.ofReal (C * ε * (jDist T S₁ S₂).toReal +
            C * ε ^ 2 * (geomDist T S₁ S₂).toReal + C * sigma e M T * ε *
              ((jDist T S₁ S₂).toReal + ε * dataDist h₁ h₂ T +
                ε * (geomDist T S₁ S₂).toReal))) ∧
        ((⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ENNReal.ofReal
          (S₁.lam u v / S₁.r u v * |S₁.mu u v|)) ≤
            ENNReal.ofReal (C * (1 + sigma e M T) * ε ^ 2)) ∧
        ((⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ENNReal.ofReal
          (S₂.lam u v / S₂.r u v * |S₂.mu u v|)) ≤
            ENNReal.ofReal (C * (1 + sigma e M T) * ε ^ 2)) := by
  obtain ⟨ηm, Cm, hηm, hCm, hMass⟩ := Stab.mass_volterra_difference A hA
  let C := Cm + 4096 * A + 512
  have hC : 0 < C := by dsimp only [C]; positivity
  have hCmC : Cm ≤ C := by dsimp only [C]; linarith only [hA]
  have hbaseC : 4096 * A + 512 ≤ C := by dsimp only [C]; linarith only [hCm]
  refine ⟨min ηm (1 / 4), C, lt_min hηm (by norm_num), hC, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall
  have hσ : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₁.xi 0 0 / (S₁.nu 0 0 : ℂ)))).trans
      (h₁s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₁s.pos.le⟩).2.2.2.2.2.1)
  have hεsq : ε ^ 2 ≤ 1 / 4 :=
    ((le_add_of_nonneg_right hσ).trans hsmall).trans (min_le_right _ _)
  let B := ε * (jDist T S₁ S₂).toReal + ε ^ 2 * (geomDist T S₁ S₂).toReal +
    sigma e M T * ε * ((jDist T S₁ S₂).toReal + ε * dataDist h₁ h₂ T +
      ε * (geomDist T S₁ S₂).toReal)
  have hΔ : 0 ≤ dataDist h₁ h₂ T :=
    add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hm := hMass T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
    (hsmall.trans (min_le_left _ _))
  have hd := (le_add_of_nonneg_left bot_le).trans hm
  have hbudget {S : Fields} {h : ℝ → ℂ} (hs : StabSetting e T ε M A S h) :
      (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ENNReal.ofReal
        (S.lam u v / S.r u v * |S.mu u v|)) ≤
          ENNReal.ofReal (C * (1 + sigma e M T) * ε ^ 2) := by
    apply iSup₂_le
    intro u hu
    apply (stab_out_mixed_mass_le hA hs hs hεsq hu.1 hu.2).trans
    apply ENNReal.ofReal_le_ofReal
    have hcoef : 16 * (256 * A + 32 * sigma e M T) ≤ C * (1 + sigma e M T) := by
      calc
        _ ≤ (4096 * A + 512) * (1 + sigma e M T) := by
          nlinarith only [mul_nonneg hA.le hσ]
        _ ≤ _ := mul_le_mul_of_nonneg_right hbaseC (by positivity)
    have hh := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ε)
    linarith only [hh]
  refine ⟨?_, hbudget h₁s, hbudget h₂s⟩
  apply hd.trans
  apply ENNReal.ofReal_le_ofReal
  have hh := mul_le_mul_of_nonneg_right hCmC hB
  dsimp only [B] at hh
  linarith only [hh]

end EmcsfAcExtension.Local
