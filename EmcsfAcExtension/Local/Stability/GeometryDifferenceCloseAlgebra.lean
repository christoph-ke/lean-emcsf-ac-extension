module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Constants in the final geometric comparison

This scalar calculation keeps the data term accompanied by `σ` and
the geometric remainder accompanied by `ε²+σ`.
-/

public section

namespace EmcsfAcExtension.Local

/-- The four proved optical budgets have the scale required by the
geometric node. The displayed constant depends only on their four
constants, uniformly in every nonnegative distance and small parameter. -/
theorem stab_geometry_budgets_le
    {Cm Ci Co C₀ ε σ J K G Δ : ℝ}
    (hm : 0 ≤ Cm) (hi : 0 ≤ Ci) (ho : 0 ≤ Co) (h₀ : 0 ≤ C₀)
    (hε : 0 ≤ ε) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hεsq : ε ^ 2 ≤ 1)
    (hJ : 0 ≤ J) (hK : 0 ≤ K) (hG : 0 ≤ G) (hΔ : 0 ≤ Δ) :
    let H := J + ε * Δ + ε * G
    let U := Cm * ε * J + Cm * ε ^ 2 * G + Cm * σ * ε * H
    let I := C₀ * ε * J + C₀ * σ * ε ^ 2 * Δ
    let Fo := Co * ε * J + Co * ε ^ 2 * G
    let Fi := Ci * ε * K + Ci * ε ^ 2 * G + Ci * σ * ε * H
    let C := 100 * (2 * Cm + C₀ + Co + 2 * Ci + 1)
    100 * (U + I + Fo + Fi) ≤
      C * ε * (J + K) + C * σ * Δ + C * (ε ^ 2 + σ) * G := by
  let B := 2 * Cm + C₀ + Co + 2 * Ci + 1
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hsJ := mul_le_mul_of_nonneg_right hσ1
    (show 0 ≤ (Cm + Ci) * ε * J by positivity)
  have hsG := mul_le_mul_of_nonneg_right hσ1
    (show 0 ≤ (Cm + Ci) * ε ^ 2 * G by positivity)
  have hsΔ := mul_le_mul_of_nonneg_right hεsq
    (show 0 ≤ (Cm + Ci + C₀) * σ * Δ by positivity)
  have hc : (Cm + Ci) * σ * ε * (J + ε * Δ + ε * G) + C₀ * σ * ε ^ 2 * Δ ≤
      (Cm + Ci) * ε * J + (Cm + Ci) * ε ^ 2 * G + (Cm + Ci + C₀) * σ * Δ := by
    nlinarith only [hsJ, hsG, hsΔ]
  have hj := mul_le_mul_of_nonneg_right
    (show 2 * Cm + C₀ + Co + Ci ≤ B by dsimp only [B]; linarith only [hi])
    (mul_nonneg hε hJ)
  have hk := mul_le_mul_of_nonneg_right
    (show Ci ≤ B by dsimp only [B]; linarith only [hm, h₀, ho, hi]) (mul_nonneg hε hK)
  have hg := mul_le_mul_of_nonneg_right
    (show 2 * Cm + Co + 2 * Ci ≤ B by dsimp only [B]; linarith only [h₀])
    (mul_nonneg (sq_nonneg ε) hG)
  have hd := mul_le_mul_of_nonneg_right
    (show Cm + Ci + C₀ ≤ B by dsimp only [B]; linarith only [hm, ho, hi]) (mul_nonneg hσ hΔ)
  have hsum :
      (Cm * ε * J + Cm * ε ^ 2 * G + Cm * σ * ε * (J + ε * Δ + ε * G)) +
      (C₀ * ε * J + C₀ * σ * ε ^ 2 * Δ) + (Co * ε * J + Co * ε ^ 2 * G) +
      (Ci * ε * K + Ci * ε ^ 2 * G + Ci * σ * ε * (J + ε * Δ + ε * G)) ≤
        B * ε * (J + K) + B * σ * Δ + B * ε ^ 2 * G := by
    nlinarith only [hc, hj, hk, hg, hd]
  have hscale := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 100)
  have hextra : 0 ≤ (100 * B) * σ * G := by positivity
  change 100 * _ ≤ (100 * B) * ε * (J + K) + (100 * B) * σ * Δ +
    (100 * B) * (ε ^ 2 + σ) * G
  nlinarith only [hscale, hextra]

end EmcsfAcExtension.Local
