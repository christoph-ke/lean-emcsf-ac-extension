module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMass
import EmcsfAcExtension.Local.Stability.ChargeDifference
import EmcsfAcExtension.Local.Stability.PotentialDifference

/-! # The mass, charge and potential clauses of extended stability

The scale-correct internal project record comparisons are projected from the main
Lipschitz conclusion without absorbing a background or length factor
into the uniform constant.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The three extra field clauses follow from the first three main
Lipschitz clauses. The threshold and constant depend only on `A` and
its uniform main constant `C₀`, before all fields, data, coupling,
background and time parameters, uniformly in derivative suprema and
minimum radii. The factors `|e| M` and `|e| T M` are retained. -/
theorem stab_extra_fields_of_main_lipschitz
    (A C₀ : ℝ) (hA : 0 < A) (hC₀ : 0 < C₀) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        jDist T S₁ S₂ + kDist e T S₁ S₂ + geomDist T S₁ S₂ ≤
          ENNReal.ofReal (C₀ * dataDist h₁ h₂ T) →
        supDist T S₁.mu S₂.mu ≤ ENNReal.ofReal (C * dataDist h₁ h₂ T) ∧
        (∀ p ∈ triangle 0 T, p.1 < p.2 →
          |S₁.Q p.1 p.2 - S₂.Q p.1 p.2| / S₁.r p.1 p.2 ^ 2 ≤
            C * |e| * M * dataDist h₁ h₂ T) ∧
        supDist T S₁.A S₂.A ≤ ENNReal.ofReal (C * |e| * T * M * dataDist h₁ h₂ T) := by
  obtain ⟨ηm, Cm, hηm, hCm, hMass⟩ := Stab.mass_volterra_difference A hA
  obtain ⟨ηq, Cq, hηq, hCq, hCharge⟩ := stab_charge_difference A hA
  obtain ⟨ηp, Cp, hηp, hCp, hPotential⟩ := stab_potential_difference A hA
  let C := (Cm + Cq + Cp) * (4 * C₀ + 2)
  refine ⟨min ηm (min ηq (min ηp (1 / 4))), C,
    lt_min hηm (lt_min hηq (lt_min hηp (by norm_num))),
    by dsimp only [C]; positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall hmain
  let Δ := dataDist h₁ h₂ T
  let B := C₀ * Δ
  let J := (jDist T S₁ S₂).toReal
  let G := (geomDist T S₁ S₂).toReal
  let L := M * J + ε * Δ + M * ε * G
  have hΔ : 0 ≤ Δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hB : 0 ≤ B := mul_nonneg hC₀.le hΔ
  have hT : 0 ≤ T := h₁s.pos.le
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans h₁s.box.1
  have hJ0 : 0 ≤ J := ENNReal.toReal_nonneg
  have hG0 : 0 ≤ G := ENNReal.toReal_nonneg
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hσ0 : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hs1 := hsmall.trans (min_le_right _ _)
  have hs2 := hs1.trans (min_le_right _ _)
  have hsize := hs2.trans (min_le_right _ _)
  have hε1 : ε ≤ 1 := by nlinarith only [hsize, hσ0, sq_nonneg (ε - 1)]
  have hεsq : ε ^ 2 ≤ 1 := by linarith only [hsize, hσ0]
  have hσ : sigma e M T ≤ 1 := by linarith only [hsize, sq_nonneg ε]
  have rb {X : ℝ≥0∞} (hX : X ≤ ENNReal.ofReal B) : X.toReal ≤ B := by
    simpa only [ENNReal.toReal_ofReal hB] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hX
  have hJ : J ≤ B := rb ((le_add_of_nonneg_right bot_le).trans
    ((le_add_of_nonneg_right bot_le).trans hmain))
  have hG : G ≤ B := rb ((le_add_of_nonneg_left bot_le).trans hmain)
  have hL : L ≤ M * ((2 * C₀ + 1) * Δ) := by
    have hεM : ε ≤ M := hε1.trans h₁s.box.1
    have hδ := mul_le_mul_of_nonneg_right hεM hΔ
    have hj := mul_le_mul_of_nonneg_left hJ hM
    have hg := mul_le_mul_of_nonneg_left (mul_le_mul hε1 hG hG0 (by norm_num : (0 : ℝ) ≤ 1)) hM
    dsimp only [L, B] at hj hg ⊢
    nlinarith only [hδ, hj, hg]
  have hCmC : Cm * (4 * C₀ + 1) ≤ C := by
    calc
      _ ≤ Cm * (4 * C₀ + 2) := by gcongr ; linarith only []
      _ ≤ _ := by dsimp only [C]; gcongr; linarith only [hCq, hCp]
  have hCqC : Cq * (2 * C₀ + 1) ≤ C := by
    calc
      _ ≤ Cq * (4 * C₀ + 2) := by gcongr <;> linarith only [hC₀]
      _ ≤ _ := by dsimp only [C]; gcongr; linarith only [hCm, hCp]
  have hCpC : Cp * (2 * C₀ + 1) ≤ C := by
    calc
      _ ≤ Cp * (4 * C₀ + 2) := by gcongr <;> linarith only [hC₀]
      _ ≤ _ := by dsimp only [C]; gcongr; linarith only [hCm, hCq]
  refine ⟨?_, ?_, ?_⟩
  · apply ((le_add_of_nonneg_right bot_le).trans
      (hMass T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hsmall.trans (min_le_left _ _)))).trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ Cm * 1 * B + Cm * 1 * B + Cm * 1 * 1 * (B + 1 * Δ + 1 * B) := by gcongr
      _ = (Cm * (4 * C₀ + 1)) * Δ := by dsimp only [B]; ring
      _ ≤ C * Δ := mul_le_mul_of_nonneg_right hCmC hΔ
  · intro p hp hlt
    apply (hCharge T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hs1.trans (min_le_left _ _))
      p.1 p.2 hp.1 hlt hp.2.2).trans
    calc
      _ ≤ Cq * |e| * (M * ((2 * C₀ + 1) * Δ)) :=
        mul_le_mul_of_nonneg_left hL (mul_nonneg hCq.le (abs_nonneg e))
      _ = (Cq * (2 * C₀ + 1)) * |e| * M * Δ := by ring
      _ ≤ _ := by gcongr
  · apply (hPotential T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hs2.trans (min_le_left _ _))).trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ Cp * |e| * T * (M * ((2 * C₀ + 1) * Δ)) :=
        mul_le_mul_of_nonneg_left hL (show 0 ≤ Cp * |e| * T by positivity)
      _ = (Cp * (2 * C₀ + 1)) * |e| * T * M * Δ := by ring
      _ ≤ _ := by gcongr

end EmcsfAcExtension.Local
