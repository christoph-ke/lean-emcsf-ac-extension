module

public import EmcsfAcExtension.Local.Stability.GeomStrongMassInMeasure
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassMeasure
import EmcsfAcExtension.Local.Stability.ChargeDifference

/-! # Incoming charge contribution to the mass difference

The area primitive and the undifferenced charge give the explicit
factor `σε`. The background bound is used only through `M ≥ 1`.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The absolute electromagnetic source in the incoming mass
difference has size `Cσε(Δj+εδ₀+εG)`. The threshold and constant
depend only on `A` and the fixed box, before all remaining parameters
and the pair; no radius cutoff or data derivative supremum enters. -/
theorem stab_in_em_difference (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        (⨆ v ∈ Icc 0 T, ∫⁻ t in Icc 0 v, ENNReal.ofReal ((-S₁.nu t v) / S₁.r t v *
          |S₁.Q t v ^ 2 / S₁.r t v ^ 2 - S₂.Q t v ^ 2 / S₂.r t v ^ 2|)) ≤
          ENNReal.ofReal (C * sigma e M T * ε *
            ((jDist T S₁ S₂).toReal + ε * dataDist h₁ h₂ T +
              ε * (geomDist T S₁ S₂).toReal)) := by
  obtain ⟨η, Cq, hη, hCq, hCharge⟩ := stab_charge_difference A hA
  refine ⟨η, 40 * (Cq + 1), hη, by positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall
  let J := (jDist T S₁ S₂).toReal
  let G := (geomDist T S₁ S₂).toReal
  let Δ := dataDist h₁ h₂ T
  let H := J + ε * Δ + ε * G
  let L := M * J + ε * Δ + M * ε * G
  let D := Cq * |e| * L
  let K := |e| * M * ε
  have hJ : 0 ≤ J := ENNReal.toReal_nonneg
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hΔ : 0 ≤ Δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans h₁s.box.1
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hLM : L ≤ M * H := by
    have hh := mul_nonneg (sub_nonneg.mpr h₁s.box.1) (mul_nonneg hε hΔ)
    dsimp only [L, H]
    nlinarith only [hh]
  have hKG : K * G ≤ |e| * M * H := by
    have hh : ε * G ≤ H := by dsimp only [H]; linarith only [hJ, mul_nonneg hε hΔ]
    have hs := mul_le_mul_of_nonneg_left hh (mul_nonneg (abs_nonneg e) hM)
    dsimp only [K]
    nlinarith only [hs]
  have hDm : D ≤ Cq * |e| * M * H := by
    have hh := mul_le_mul_of_nonneg_left hLM (mul_nonneg hCq.le (abs_nonneg e))
    dsimp only [D]
    nlinarith only [hh]
  have hsum : D + K * G ≤ (Cq + 1) * |e| * M * H := by
    nlinarith only [hDm, hKG]
  apply iSup₂_le
  intro v hv
  apply (stab_in_em_difference_le_of_charge_bound h₁s h₂s hD
    (hCharge T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall) hv.1 hv.2).trans
  apply ENNReal.ofReal_le_ofReal
  have hs := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ 10 * K * T ^ 2 by positivity)
  calc
    _ ≤ (10 * K * T ^ 2) * ((Cq + 1) * |e| * M * H) := hs
    _ = _ := by
      dsimp only [K, H, J, G, Δ, sigma]
      rw [← sq_abs e]
      ring

end EmcsfAcExtension.Local
