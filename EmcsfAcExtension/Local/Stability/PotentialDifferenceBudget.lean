module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.PotentialDifference
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Dimensionless potential phase budget

The length factor in the potential estimate is multiplied by the
incoming transport length and coupling. Both scale-correct and coarser
dimensionless forms retain all data contributions.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- The potential comparison controls its incoming phase budget.
Constants depend only on `A` and the fixed box, before all other
parameters and the pair. The first bound retains `M⁻²`; the second
uses `M ≥ 1` and is sufficient for the quadratic flux projection. -/
theorem stab_potential_phase_bounds (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        T * |e| * (supDist T S₁.A S₂.A).toReal ≤ C * sigma e M T / M ^ 2 *
          (M * (jDist T S₁ S₂).toReal + ε * dataDist h₁ h₂ T +
            M * ε * (geomDist T S₁ S₂).toReal) ∧
        T * |e| * (supDist T S₁.A S₂.A).toReal ≤ C * sigma e M T *
          ((jDist T S₁ S₂).toReal + ε * dataDist h₁ h₂ T +
            ε * (geomDist T S₁ S₂).toReal) := by
  obtain ⟨η, C, hη, hC, hPot⟩ := stab_potential_difference A hA
  refine ⟨η, 4 * C, hη, by positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall
  let J := (jDist T S₁ S₂).toReal
  let G := (geomDist T S₁ S₂).toReal
  let L := M * J + ε * dataDist h₁ h₂ T + M * ε * G
  let H := J + ε * dataDist h₁ h₂ T + ε * G
  have hJ : 0 ≤ J := ENNReal.toReal_nonneg
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hΔ : 0 ≤ dataDist h₁ h₂ T := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hM1 : 1 ≤ M := h₁s.box.1
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) hM1
  have hT : 0 < T := h₁s.pos
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hp := hPot T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall
  have hpReal : (supDist T S₁.A S₂.A).toReal ≤ C * |e| * T * L := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hp
    change (supDist T S₁.A S₂.A).toReal ≤ (ENNReal.ofReal (C * |e| * T * L)).toReal at hh
    simpa only [ENNReal.toReal_ofReal (show 0 ≤ C * |e| * T * L by positivity)] using! hh
  have hscaled := mul_le_mul_of_nonneg_left hpReal (mul_nonneg h₁s.pos.le (abs_nonneg e))
  have hbase : T * |e| * (supDist T S₁.A S₂.A).toReal ≤ C * e ^ 2 * T ^ 2 * L := by
    apply hscaled.trans_eq
    calc
      _ = C * |e| ^ 2 * T ^ 2 * L := by ring
      _ = _ := by rw [sq_abs]
  constructor
  · apply hbase.trans_eq
    dsimp only [sigma, L, J, G]
    field_simp
    ring
  · have hMM : M ≤ M ^ 2 := by nlinarith only [hM1]
    have hMM1 : 1 ≤ M ^ 2 := by nlinarith only [hM1]
    have hMJ := mul_le_mul_of_nonneg_right hMM hJ
    have hMG := mul_le_mul_of_nonneg_right hMM (mul_nonneg hε hG)
    have hMD := mul_le_mul_of_nonneg_right hMM1 (mul_nonneg hε hΔ)
    have hLH : L ≤ M ^ 2 * H := by
      dsimp only [L, H]
      nlinarith only [hMJ, hMG, hMD]
    apply hbase.trans
    apply (mul_le_mul_of_nonneg_left hLH (show 0 ≤ C * e ^ 2 * T ^ 2 by positivity)).trans_eq
    dsimp only [sigma, H, J, G]
    ring

end EmcsfAcExtension.Local
