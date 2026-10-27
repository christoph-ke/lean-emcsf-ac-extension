module

public import EmcsfAcExtension.Local.Stability.GeomStrongScalarPrimitive
import EmcsfAcExtension.Local.Stability.GeomStrongScalarArea
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMass
import EmcsfAcExtension.Local.Stability.PotentialDifferenceBudget

/-! # Closing the scalar geometric-source comparison

The normalized mass Volterra comparison and the dimensionless potential
phase bound remove the feedback from the ordered scalar area estimate.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- Scalar part of G1 with its approved small factors. Constants depend
only on `A` and the fixed box, before all time, coupling, background,
fields and data, uniformly in the minimum radius and derivative suprema.
No main Lipschitz conclusion is assumed.
-/
theorem stab_geometric_scalar_source_difference_c1 (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        (∫⁻ q in triangle 0 T, ‖geometricScalarSource (triangle 0 T) S₁ q.1 q.2 -
          geometricScalarSource (triangle 0 T) S₂ q.1 q.2‖ₑ) ≤
        ENNReal.ofReal (C * ε * ((jDist T S₁ S₂).toReal + (kDist e T S₁ S₂).toReal) +
          C * ε ^ 2 * (geomDist T S₁ S₂).toReal + C * sigma e M T *
            (dataDist h₁ h₂ T + (jDist T S₁ S₂).toReal + (kDist e T S₁ S₂).toReal +
              ε * (geomDist T S₁ S₂).toReal)) := by
  obtain ⟨Cs, hCs, hScalar⟩ := stab_geometric_scalar_area_difference_c1 A hA
  obtain ⟨ηm, Cm, hηm, hCm, hMass⟩ := Stab.mass_volterra_difference A hA
  obtain ⟨ηp, Cp, hηp, hCp, hPhase⟩ := stab_potential_phase_bounds A hA
  let C := Cs * (1 + Cp + Cm)
  refine ⟨min ηm (min ηp (1 / 12)), C,
    lt_min hηm (lt_min hηp (by norm_num)), by dsimp only [C]; positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall
  let Δ := dataDist h₁ h₂ T
  let J := (jDist T S₁ S₂).toReal
  let K := (kDist e T S₁ S₂).toReal
  let G := (geomDist T S₁ S₂).toReal
  let U := (supDist T S₁.mu S₂.mu).toReal
  let P := T * |e| * (supDist T S₁.A S₂.A).toReal
  let H := J + ε * Δ + ε * G
  let Hbar := Δ + J + K + ε * G
  have hΔ : 0 ≤ Δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hJ : 0 ≤ J := ENNReal.toReal_nonneg
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hU0 : 0 ≤ U := ENNReal.toReal_nonneg
  have hP0 : 0 ≤ P := mul_nonneg (mul_nonneg h₁s.pos.le (abs_nonneg e)) ENNReal.toReal_nonneg
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hσ : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hsize : ε ^ 2 + sigma e M T ≤ 1 / 12 :=
    hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hεsq : ε ^ 2 ≤ 1 := by linarith only [hsize, hσ]
  have hεrad : 3 * ε ^ 2 ≤ 1 / 2 := by linarith only [hsize, hσ]
  have hε1 : ε ≤ 1 := by nlinarith only [hεsq, sq_nonneg (ε - 1)]
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hHbar : 0 ≤ Hbar := by dsimp only [Hbar]; positivity
  have hHb : H ≤ Hbar := by
    have hh := mul_le_mul_of_nonneg_right hε1 hΔ
    dsimp only [H, Hbar]
    linarith only [hh, hK]
  have hm := (le_add_of_nonneg_right bot_le).trans
    (hMass T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hsmall.trans (min_le_left _ _)))
  have hU : U ≤ Cm * ε * J + Cm * ε ^ 2 * G + Cm * sigma e M T * ε * H := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
    change U ≤ (ENNReal.ofReal
      (Cm * ε * J + Cm * ε ^ 2 * G + Cm * sigma e M T * ε * H)).toReal at hh
    simpa only [ENNReal.toReal_ofReal (show
      0 ≤ Cm * ε * J + Cm * ε ^ 2 * G + Cm * sigma e M T * ε * H by positivity)] using hh
  have hP : P ≤ Cp * sigma e M T * H :=
    (hPhase T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
      (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _)))).2
  have hεP : ε ^ 2 * P ≤ Cp * sigma e M T * Hbar := by
    calc
      _ ≤ ε ^ 2 * (Cp * sigma e M T * H) := mul_le_mul_of_nonneg_left hP (sq_nonneg ε)
      _ ≤ 1 * (Cp * sigma e M T * Hbar) := by gcongr
      _ = _ := one_mul _
  have hεU : ε ^ 2 * U ≤ Cm * ε * J + Cm * ε ^ 2 * G + Cm * sigma e M T * Hbar := by
    calc
      _ ≤ ε ^ 2 * (Cm * ε * J + Cm * ε ^ 2 * G + Cm * sigma e M T * ε * H) :=
        mul_le_mul_of_nonneg_left hU (sq_nonneg ε)
      _ = (ε ^ 2 * Cm * ε * J) + (ε ^ 2 * Cm * ε ^ 2 * G) +
          ε ^ 2 * Cm * sigma e M T * ε * H := by ring
      _ ≤ (1 * Cm * ε * J) + (1 * Cm * ε ^ 2 * G) +
          1 * Cm * sigma e M T * 1 * Hbar := by gcongr
      _ = _ := by ring
  have hraw := hScalar T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hεrad
  apply hraw.trans
  apply ENNReal.ofReal_le_ofReal
  have hcoeff : Cs * (1 + Cm) ≤ C := by
    dsimp only [C]
    apply mul_le_mul_of_nonneg_left _ hCs.le
    linarith only [hCp]
  have hcoeffσ : Cs * (Cp + Cm) ≤ C := by
    dsimp only [C]
    apply mul_le_mul_of_nonneg_left _ hCs.le
    linarith only []
  calc
    _ = Cs * (ε * (J + K) + ε ^ 2 * G + ε ^ 2 * P + ε ^ 2 * U) := by ring
    _ ≤ Cs * (ε * (J + K) + ε ^ 2 * G + Cp * sigma e M T * Hbar +
        (Cm * ε * J + Cm * ε ^ 2 * G + Cm * sigma e M T * Hbar)) := by gcongr
    _ ≤ (Cs * (1 + Cm)) * ε * (J + K) + (Cs * (1 + Cm)) * ε ^ 2 * G +
        (Cs * (Cp + Cm)) * sigma e M T * Hbar := by
      apply sub_nonneg.mp
      convert (show 0 ≤ Cs * Cm * ε * K by positivity) using 1; ring
    _ ≤ _ := by gcongr

end EmcsfAcExtension.Local
