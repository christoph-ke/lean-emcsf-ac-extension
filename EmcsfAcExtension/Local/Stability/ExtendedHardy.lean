module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.DifferenceMomentsCloseOut
import EmcsfAcExtension.Local.Stability.DifferenceMomentsCloseIn
import EmcsfAcExtension.Local.Stability.PotentialDifferenceBudget
import EmcsfAcExtension.Local.Stability.PotentialTriangleDifference

/-! # Weighted scalar clauses of the extended stability estimate

The two oriented Hardy differences and the incoming ratio triangle area
are closed using only the explicit pending main Lipschitz record.
No variation or geometric derivative conclusion is an assumption.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The `hardyDiff` clause under the main Lipschitz record. The threshold
and constant depend only on `A` and its uniform main constant `C₀`, before
all time, coupling, background, data, fields and derivative suprema. -/
theorem stab_hardy_difference_of_main_lipschitz
    (A C₀ : ℝ) (hA : 0 < A) (hC₀ : 0 < C₀) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        jDist T S₁ S₂ + kDist e T S₁ S₂ + geomDist T S₁ S₂ ≤
          ENNReal.ofReal (C₀ * dataDist h₁ h₂ T) →
        (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ENNReal.ofReal (S₁.lam u v / S₁.r u v *
          ‖S₁.theta u v / S₁.lam u v - S₂.theta u v / S₂.lam u v‖)) +
        (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v, ENNReal.ofReal (-S₁.nu u v / S₁.r u v *
          ‖S₁.xi u v / S₁.nu u v - S₂.xi u v / S₂.nu u v‖)) ≤
          ENNReal.ofReal (C * dataDist h₁ h₂ T) := by
  obtain ⟨ηo, Co, hηo, hCo, hOut⟩ := stab_out_difference A hA
  obtain ⟨ηi, Ci, hηi, hCi, hIn⟩ := stab_in_difference A hA
  obtain ⟨ηp, Cp, hηp, hCp, hPhase⟩ := stab_potential_phase_bounds A hA
  let C := 2 * Co * C₀ + Ci * (2 * C₀ + Cp * (2 * C₀ + 1))
  refine ⟨min ηo (min ηi (min ηp (1 / 4))), C,
    lt_min hηo (lt_min hηi (lt_min hηp (by norm_num))),
    by dsimp only [C]; positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall hmain
  let Δ := dataDist h₁ h₂ T
  let B := C₀ * Δ
  let J := (jDist T S₁ S₂).toReal
  let K := (kDist e T S₁ S₂).toReal
  let G := (geomDist T S₁ S₂).toReal
  let P := T * |e| * (supDist T S₁.A S₂.A).toReal
  have hT : 0 < T := h₁s.pos
  have hΔ : 0 ≤ Δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hB : 0 ≤ B := mul_nonneg hC₀.le hΔ
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hσ : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hs : ε ^ 2 + sigma e M T ≤ 1 / 4 :=
    hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hε1 : ε ≤ 1 := by nlinarith only [hs, hσ, sq_nonneg (ε - 1)]
  have hσ1 : sigma e M T ≤ 1 := by linarith only [hs, sq_nonneg ε]
  have hP0 : 0 ≤ P := mul_nonneg (mul_nonneg h₁s.pos.le (abs_nonneg e)) ENNReal.toReal_nonneg
  have real_bound {X : ℝ≥0∞} (hX : X ≤ ENNReal.ofReal B) : X.toReal ≤ B := by
    simpa only [ENNReal.toReal_ofReal hB] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hX
  have hJ : J ≤ B := real_bound
    ((le_add_of_nonneg_right bot_le).trans ((le_add_of_nonneg_right bot_le).trans hmain))
  have hK : K ≤ B := real_bound
    ((le_add_of_nonneg_left bot_le).trans ((le_add_of_nonneg_right bot_le).trans hmain))
  have hG : G ≤ B := real_bound ((le_add_of_nonneg_left bot_le).trans hmain)
  have hp := (hPhase T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
    (hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))).2
  have hP : P ≤ Cp * (2 * B + Δ) := by
    calc
      P ≤ Cp * sigma e M T * (J + ε * Δ + ε * G) := hp
      _ ≤ Cp * 1 * (B + 1 * Δ + 1 * B) := by gcongr
      _ = _ := by ring
  have ho := (le_add_of_nonneg_left bot_le).trans
    (hOut T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hsmall.trans (min_le_left _ _)))
  have hi := (le_add_of_nonneg_left bot_le).trans
    (hIn T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
      (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))))
  apply (add_le_add ho hi).trans
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hphase : Ci * ε * |e| * (T / 2) * (supDist T S₁.A S₂.A).toReal = Ci * ε * P / 2 := by
    dsimp only [P]; ring
  rw [hphase]
  calc
    _ ≤ Co * (B + 1 * B) + (Ci * (B + 1 * B) + Ci * 1 * (Cp * (2 * B + Δ))) := by
      have hh : Ci * ε * P / 2 ≤ Ci * ε * P := by
        linarith only [mul_nonneg (mul_nonneg hCi.le hε) hP0]
      apply (add_le_add le_rfl (add_le_add le_rfl hh)).trans
      gcongr
    _ = _ := by dsimp only [C, B]; ring

/-- The `xiRatioArea` clause follows from incoming Hardy in its correct
orientation. The threshold and constant depend only on `A` and `C₀`,
uniformly in every field parameter, pair and minimum radius. The
single length factor `T` is retained exactly. -/
theorem stab_xi_ratio_area_of_main_lipschitz
    (A C₀ : ℝ) (hA : 0 < A) (hC₀ : 0 < C₀) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        jDist T S₁ S₂ + kDist e T S₁ S₂ + geomDist T S₁ S₂ ≤
          ENNReal.ofReal (C₀ * dataDist h₁ h₂ T) →
        (∫⁻ p in triangle 0 T, ENNReal.ofReal
          (‖S₁.xi p.1 p.2 / S₁.nu p.1 p.2 - S₂.xi p.1 p.2 / S₂.nu p.1 p.2‖ /
            (p.2 - p.1))) ≤ ENNReal.ofReal (C * T * dataDist h₁ h₂ T) := by
  obtain ⟨η, C, hη, hC, hHardy⟩ := stab_hardy_difference_of_main_lipschitz A C₀ hA hC₀
  refine ⟨η, 4 * C, hη, by positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall hmain
  have hi := (le_add_of_nonneg_left bot_le).trans
    (hHardy T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall hmain)
  apply (Stab.xi_ratio_area_le h₁s h₂s ⟨h₁s.pos.le, le_rfl⟩).trans
  apply (mul_le_mul' le_rfl hi).trans_eq
  rw [← ENNReal.ofReal_mul (mul_nonneg (by norm_num) h₁s.pos.le)]
  congr 1
  ring

end EmcsfAcExtension.Local
