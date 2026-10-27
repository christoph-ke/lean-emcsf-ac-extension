module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.ChargeDifference
import EmcsfAcExtension.Local.Stability.GeometryDifferenceCoarseMass
import EmcsfAcExtension.Local.Stability.PotentialDifferenceForcing
import EmcsfAcExtension.Local.Stability.PotentialDifferenceIntegral

/-! # Scale-correct potential comparison

The charge comparison and coarse optical mass control bound the
potential constraint density. Integrating from the common axis gauge
retains the length factor `T = 2R` explicitly.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [node restart-stab-potential-difference]
The potential comparison, charged_SF_new_version.tex:L5370–5370 and approved internal project
record,
with `T=2R` as the explicit length scale. Constants depend only on `A`
and the fixed box, before all other parameters and the pair, uniformly
in the coupling, scalar background and minimum radius. -/
theorem stab_potential_difference (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        supDist T S₁.A S₂.A ≤ ENNReal.ofReal (C * |e| * T *
          (M * (jDist T S₁ S₂).toReal + ε * dataDist h₁ h₂ T +
            M * ε * (geomDist T S₁ S₂).toReal)) := by
  obtain ⟨ηq, Cq, hηq, hCq, hCharge⟩ := stab_charge_difference A hA
  obtain ⟨ηm, Cm, hηm, hCm, hMass⟩ := stab_mass_optical_le A hA
  let B := 128 * (Cq + 1 + 2 * Cm)
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨min ηq (min ηm (1 / 12)), B,
    lt_min hηq (lt_min hηm (by norm_num)), hB, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall
  let J := (jDist T S₁ S₂).toReal
  let G := (geomDist T S₁ S₂).toReal
  let U := (supDist T S₁.mu S₂.mu).toReal
  let L := M * J + ε * dataDist h₁ h₂ T + M * ε * G
  have hJ : 0 ≤ J := ENNReal.toReal_nonneg
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hΔ : 0 ≤ dataDist h₁ h₂ T := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hM : 0 ≤ M := le_trans (by norm_num) h₁s.box.1
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hσ : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hε1 : ε ^ 2 ≤ 1 := by
    have hb := ((le_add_of_nonneg_right hσ).trans hsmall).trans
      ((min_le_right _ _).trans (min_le_right _ _))
    linarith only [hb]
  have hU := hMass T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
    (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hMU := mul_le_mul_of_nonneg_left hU (mul_nonneg hM hε0)
  have hJJ := mul_le_mul_of_nonneg_left hε1 (show 0 ≤ Cm * M * J by positivity)
  have hMU' : M * ε * U ≤ Cm * (M * ε * G + M * J) := by
    nlinarith only [hMU, hJJ]
  have hMG : M * ε * G ≤ L := by
    dsimp only [L]
    nlinarith only [mul_nonneg hM hJ, mul_nonneg hε0 hΔ]
  have hMJ : M * J ≤ L := by
    dsimp only [L]
    nlinarith only [mul_nonneg hε0 hΔ, mul_nonneg (mul_nonneg hM hε0) hG]
  have hbudget : M * ε * (G + U) ≤ (1 + 2 * Cm) * L := by
    have hmG := mul_le_mul_of_nonneg_left hMG hCm.le
    have hmJ := mul_le_mul_of_nonneg_left hMJ hCm.le
    nlinarith only [hMU', hMG, hmG, hmJ]
  have hpartial : ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ T →
      |pdV (triangle 0 T) S₁.A u v - pdV (triangle 0 T) S₂.A u v| ≤ B * |e| * L := by
    intro u v hu huv hvT
    have hD := hCharge T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
      (hsmall.trans (min_le_left _ _)) u v hu huv hvT
    have hf := stab_potential_partial_sub_le_of_charge h₁s h₂s hu huv hvT hD
    apply hf.trans
    change 128 * (Cq * |e| * L + (|e| * M * ε) * (G + U)) ≤ B * |e| * L
    have hs := mul_le_mul_of_nonneg_left hbudget (abs_nonneg e)
    calc
      _ = 128 * (Cq * |e| * L + |e| * (M * ε * (G + U))) := by ring
      _ ≤ 128 * (Cq * |e| * L + |e| * ((1 + 2 * Cm) * L)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hs) (by norm_num)
      _ = _ := by dsimp only [B]; ring
  have hs := stab_potential_sup_le_of_partial h₁s h₂s
    (show 0 ≤ B * |e| * L by positivity) hpartial
  apply hs.trans_eq
  congr 1
  dsimp only [L, J, G]
  ring

end EmcsfAcExtension.Local
