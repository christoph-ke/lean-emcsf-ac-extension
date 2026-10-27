module

public import EmcsfAcExtension.Local.Stability.MainLipschitzRecords
import EmcsfAcExtension.Local.Stability.SourceDifferencePhase
import EmcsfAcExtension.Local.Stability.SourceDifferenceCoefficient
import EmcsfAcExtension.Local.Stability.SourceDifference
public import EmcsfAcExtension.Local.Stability.SourceDifferenceEM

/-! # Unconditional small-data stability comparisons

The seven comparison inputs are produced from internal project record with a common
constant before the data or solution pair. The approved scalar and k
remainders are retained throughout the closure argument.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

open Stab

/-- [node restart-sec-bv-stability-independent#covariant-transport-phase-difference]
The comparison on the §4.4 small-data scope. Threshold and constant depend
only on `A` and the fixed box, before every physical parameter, datum and
solution pair, uniformly in derivative suprema and the minimum radius. -/
theorem Stab.covariant_transport_phase_difference (A : ℝ)
    (hA : 0 < A) : ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
    ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ^ 2 + sigma e M T ≤ η →
      (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v,
        ‖-(I * e * (S₁.A u v - S₂.A u v) * jC1 (triangle 0 T) S₂ u v)‖ₑ) ≤
        ENNReal.ofReal (C * sigma e M T * (dataDist h₁ h₂ T +
          (jDist T S₁ S₂).toReal + ε * (geomDist T S₁ S₂).toReal)) := by
  obtain ⟨ηr, D, hηr, hD, hrecords⟩ := Stab.difference_records A hA
  obtain ⟨C, hC, hclose⟩ := Stab.covariant_transport_phase_difference_of_differences A D hA hD
  refine ⟨min ηr (1 / 4), C, lt_min hηr (by norm_num), hC, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hsmall
  rcases hrecords T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂
    (hsmall.trans (min_le_left _ _)) with ⟨hr, hf, hq, hp, hi, ho, hg⟩
  have hε : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans
    (hs₂.box.2 (0, 0) ⟨le_rfl, le_rfl, hs₂.pos.le⟩).2.2.2.2.2.1
  have hσ : 0 ≤ sigma e M T := by unfold sigma; positivity
  have hsmall₁ := hsmall.trans (min_le_right _ _)
  have hε₂ : ε ^ 2 ≤ 1 / 4 := (le_add_of_nonneg_right hσ).trans hsmall₁
  have hε₁ : ε ≤ 1 := by nlinarith only [hε₂, hε]
  have hσ₁ : sigma e M T ≤ 1 := by nlinarith only [hsmall₁, sq_nonneg ε]
  exact hclose T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hε₁ hp

/-- [node restart-sec-bv-stability-independent#homogeneous-coefficient-difference]
The comparison on the §4.4 small-data scope. Threshold and constant depend
only on `A` and the fixed box, before every physical parameter, datum and
solution pair, uniformly in derivative suprema and the minimum radius. -/
theorem Stab.homogeneous_coefficient_difference (A : ℝ)
    (hA : 0 < A) : ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
    ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ^ 2 + sigma e M T ≤ η →
      (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v,
        ‖(((-S₁.nu u v / S₁.r u v * ‖S₁.xi u v / (S₁.nu u v : ℂ)‖ ^ 2) -
            (-S₂.nu u v / S₂.r u v * ‖S₂.xi u v / (S₂.nu u v : ℂ)‖ ^ 2) : ℝ) : ℂ) *
          jC1 (triangle 0 T) S₂ u v‖ₑ) ≤
        ENNReal.ofReal
          (C * ε * (∫⁻ v in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S₂) v).toReal *
              (kDist e T S₁ S₂).toReal +
            C * ε ^ 2 * (∫⁻ v in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S₂) v).toReal *
              (geomDist T S₁ S₂).toReal +
            C * sigma e M T * (dataDist h₁ h₂ T + (jDist T S₁ S₂).toReal +
              (kDist e T S₁ S₂).toReal + ε * (geomDist T S₁ S₂).toReal)) := by
  obtain ⟨ηr, D, hηr, hD, hrecords⟩ := Stab.difference_records A hA
  obtain ⟨C, hC, hclose⟩ := Stab.homogeneous_coefficient_difference_of_differences A D hA hD
  refine ⟨min ηr (1 / 4), C, lt_min hηr (by norm_num), hC, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hsmall
  rcases hrecords T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂
    (hsmall.trans (min_le_left _ _)) with ⟨hr, hf, hq, hp, hi, ho, hg⟩
  have hε : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans
    (hs₂.box.2 (0, 0) ⟨le_rfl, le_rfl, hs₂.pos.le⟩).2.2.2.2.2.1
  have hσ : 0 ≤ sigma e M T := by unfold sigma; positivity
  have hsmall₁ := hsmall.trans (min_le_right _ _)
  have hε₂ : ε ^ 2 ≤ 1 / 4 := (le_add_of_nonneg_right hσ).trans hsmall₁
  have hε₁ : ε ≤ 1 := by nlinarith only [hε₂, hε]
  have hσ₁ : sigma e M T ≤ 1 := by nlinarith only [hsmall₁, sq_nonneg ε]
  exact hclose T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hε₁ hi

/-- [node restart-sec-bv-stability-independent#scalar-curvature-source-difference]
The comparison on the §4.4 small-data scope. Threshold and constant depend
only on `A` and the fixed box, before every physical parameter, datum and
solution pair, uniformly in derivative suprema and the minimum radius. -/
theorem Stab.scalar_curvature_source_difference (A : ℝ)
    (hA : 0 < A) : ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
    ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ^ 2 + sigma e M T ≤ η →
      (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v,
        ‖(S₁.nu u v : ℂ) * S₁.theta u v / (S₁.r u v : ℂ) ^ 2 *
            (curvScalar (triangle 0 T) S₁ u v +
              2 * starRingEnd ℂ (curvScalar (triangle 0 T) S₁ u v)) -
          (S₂.nu u v : ℂ) * S₂.theta u v / (S₂.r u v : ℂ) ^ 2 *
            (curvScalar (triangle 0 T) S₂ u v +
              2 * starRingEnd ℂ (curvScalar (triangle 0 T) S₂ u v))‖ₑ +
        ‖(S₁.lam u v : ℂ) * S₁.xi u v / (S₁.r u v : ℂ) ^ 2 *
            (curvScalarIn e (triangle 0 T) S₁ u v +
              2 * starRingEnd ℂ (curvScalarIn e (triangle 0 T) S₁ u v)) -
          (S₂.lam u v : ℂ) * S₂.xi u v / (S₂.r u v : ℂ) ^ 2 *
            (curvScalarIn e (triangle 0 T) S₂ u v +
              2 * starRingEnd ℂ (curvScalarIn e (triangle 0 T) S₂ u v))‖ₑ) ≤
        ENNReal.ofReal (C * ε ^ 2 * ((jDist T S₁ S₂).toReal + (kDist e T S₁ S₂).toReal) +
          C * ε ^ 3 * (geomDist T S₁ S₂).toReal +
          C * sigma e M T * ε ^ 4 * dataDist h₁ h₂ T / M) := by
  obtain ⟨ηr, D, hηr, hD, hrecords⟩ := Stab.difference_records A hA
  obtain ⟨ηh, C, hηh, hC, hclose⟩ :=
    Stab.scalar_curvature_source_difference_of_differences A D hA hD
  refine ⟨min ηr (min ηh (1 / 4)), C,
    lt_min hηr (lt_min hηh (by norm_num)), hC, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hsmall
  rcases hrecords T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂
    (hsmall.trans (min_le_left _ _)) with ⟨hr, hf, hq, hp, hi, ho, hg⟩
  exact hclose T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂
    (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))) hr

end EmcsfAcExtension.Local
