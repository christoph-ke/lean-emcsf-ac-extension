module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassForcing
public import EmcsfAcExtension.Local.Stability.GeomStrongMassInRaw
import EmcsfAcExtension.Local.Stability.ExtendedHardy
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassForcingBudget
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassCharge
import EmcsfAcExtension.Local.Stability.GeomStrongMassInForcing
import EmcsfAcExtension.Local.Stability.GeomStrongMassInCharge

/-! # Closing both absolute normalized mass forcings

The scalar Hardy difference, electromagnetic comparison and individual
mass budgets control the exact damped forcings in both orientations.
These are the sources needed for strong mass derivative comparison.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- Absolute mass forcing comparison under the main Lipschitz record.
Constants depend only on `A` and its uniform main constant `C₀`, before
all field parameters, data, solutions, derivative suprema and minimum radii.
Both forcings are integrated with their own characteristic orientation. -/
theorem stab_mass_forcing_difference_of_main_lipschitz
    (A C₀ : ℝ) (hA : 0 < A) (hC₀ : 0 < C₀) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        jDist T S₁ S₂ + kDist e T S₁ S₂ + geomDist T S₁ S₂ ≤
          ENNReal.ofReal (C₀ * dataDist h₁ h₂ T) →
        (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T,
          ENNReal.ofReal |massDifferenceForcing S₁ S₂ u v|) +
        (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
          ENNReal.ofReal |massDifferenceForcingIn S₁ S₂ u v|) ≤
            ENNReal.ofReal (C * dataDist h₁ h₂ T) := by
  obtain ⟨ηh, Ch, hηh, hCh, hHardy⟩ := stab_hardy_difference_of_main_lipschitz A C₀ hA hC₀
  obtain ⟨ηo, Co, hηo, hCo, hOut⟩ := stab_out_em_difference A hA
  obtain ⟨ηi, Ci, hηi, hCi, hIn⟩ := stab_in_em_difference A hA
  let R := 87040 * A + 10880
  let C := 2 * Ch + (Co + Ci) * (2 * C₀ + 1) + 2 * R * C₀
  have hR : 0 < R := by dsimp only [R]; positivity
  refine ⟨min ηh (min ηo (min ηi (1 / 4))), C,
    lt_min hηh (lt_min hηo (lt_min hηi (by norm_num))),
    by dsimp only [C]; positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall hmain
  let Δ := dataDist h₁ h₂ T
  let B := C₀ * Δ
  let G := (geomDist T S₁ S₂).toReal
  let J := (jDist T S₁ S₂).toReal
  let H := J + ε * Δ + ε * G
  let Ho := ⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ENNReal.ofReal (S₁.lam u v / S₁.r u v *
    ‖S₁.theta u v / S₁.lam u v - S₂.theta u v / S₂.lam u v‖)
  let Hi := ⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v, ENNReal.ofReal (-S₁.nu u v / S₁.r u v *
    ‖S₁.xi u v / S₁.nu u v - S₂.xi u v / S₂.nu u v‖)
  let Eo := ⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ENNReal.ofReal (S₁.lam u v / S₁.r u v *
    |S₁.Q u v ^ 2 / S₁.r u v ^ 2 - S₂.Q u v ^ 2 / S₂.r u v ^ 2|)
  let Ei := ⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v, ENNReal.ofReal (-S₁.nu u v / S₁.r u v *
    |S₁.Q u v ^ 2 / S₁.r u v ^ 2 - S₂.Q u v ^ 2 / S₂.r u v ^ 2|)
  have hΔ : 0 ≤ Δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hB : 0 ≤ B := mul_nonneg hC₀.le hΔ
  have hG0 : 0 ≤ G := ENNReal.toReal_nonneg
  have hJ0 : 0 ≤ J := ENNReal.toReal_nonneg
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hσ : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hs : ε ^ 2 + sigma e M T ≤ 1 / 4 :=
    hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hεsq : ε ^ 2 ≤ 1 / 4 := by linarith only [hs, hσ]
  have hεsq1 : ε ^ 2 ≤ 1 := by linarith only [hεsq]
  have hε1 : ε ≤ 1 := by nlinarith only [hεsq, sq_nonneg (ε - 1)]
  have hσ1 : sigma e M T ≤ 1 := by linarith only [hs, sq_nonneg ε]
  have hHb : Ho + Hi ≤ ENNReal.ofReal (Ch * Δ) :=
    hHardy T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hsmall.trans (min_le_left _ _)) hmain
  have heo : Eo ≤ ENNReal.ofReal (Co * sigma e M T * ε * H) :=
    hOut T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
      (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hei : Ei ≤ ENNReal.ofReal (Ci * sigma e M T * ε * H) :=
    hIn T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
      (hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have real_bound {X : ℝ≥0∞} (hX : X ≤ ENNReal.ofReal B) : X.toReal ≤ B := by
    simpa only [ENNReal.toReal_ofReal hB] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hX
  have hJ : J ≤ B := real_bound
    ((le_add_of_nonneg_right bot_le).trans ((le_add_of_nonneg_right bot_le).trans hmain))
  have hG : G ≤ B := real_bound ((le_add_of_nonneg_left bot_le).trans hmain)
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hHc : H ≤ (2 * C₀ + 1) * Δ := by
    calc
      _ ≤ B + 1 * Δ + 1 * B := by dsimp only [H]; gcongr
      _ = _ := by dsimp only [B]; ring
  have ho : (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T,
      ENNReal.ofReal |massDifferenceForcing S₁ S₂ u v|) ≤
      ENNReal.ofReal (2 * ε) * Ho + Eo + ENNReal.ofReal (R * ε ^ 2 * G) := by
    apply iSup₂_le
    intro u hu
    apply (stab_out_mass_forcing_budget hA h₁s h₂s hεsq hσ1 hu.1 hu.2).trans
    exact add_le_add (add_le_add (mul_le_mul' le_rfl (le_iSup₂_of_le u hu le_rfl))
      (le_iSup₂_of_le u hu le_rfl)) le_rfl
  have hi : (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
      ENNReal.ofReal |massDifferenceForcingIn S₁ S₂ u v|) ≤
      ENNReal.ofReal (2 * ε) * Hi + Ei + ENNReal.ofReal (R * ε ^ 2 * G) := by
    apply iSup₂_le
    intro v hv
    apply (stab_in_mass_forcing_budget hA h₁s h₂s hεsq hσ1 hv.1 hv.2).trans
    exact add_le_add (add_le_add (mul_le_mul' le_rfl (le_iSup₂_of_le v hv le_rfl))
      (le_iSup₂_of_le v hv le_rfl)) le_rfl
  apply (add_le_add ho hi).trans
  calc
    _ = ENNReal.ofReal (2 * ε) * (Ho + Hi) + (Eo + Ei) +
        (ENNReal.ofReal (R * ε ^ 2 * G) + ENNReal.ofReal (R * ε ^ 2 * G)) := by ring
    _ ≤ ENNReal.ofReal (2 * ε) * ENNReal.ofReal (Ch * Δ) +
        (ENNReal.ofReal (Co * sigma e M T * ε * H) +
          ENNReal.ofReal (Ci * sigma e M T * ε * H)) +
        (ENNReal.ofReal (R * ε ^ 2 * G) + ENNReal.ofReal (R * ε ^ 2 * G)) :=
      add_le_add (add_le_add (mul_le_mul' le_rfl hHb) (add_le_add heo hei)) le_rfl
    _ = ENNReal.ofReal ((2 * ε) * (Ch * Δ) + (Co + Ci) * sigma e M T * ε * H +
        2 * R * ε ^ 2 * G) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * ε)]
      repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ (2 * 1) * (Ch * Δ) + (Co + Ci) * 1 * 1 * ((2 * C₀ + 1) * Δ) +
            2 * R * 1 * B := by gcongr
        _ = _ := by dsimp only [C, B]; ring

end EmcsfAcExtension.Local
