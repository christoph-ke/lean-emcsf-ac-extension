module

public import EmcsfAcExtension.Local.Stability.MainRecords
import EmcsfAcExtension.Local.Stability.SourceDifferenceScalarAreaJ
import EmcsfAcExtension.Local.Stability.SourceDifferenceScalarAreaK
import EmcsfAcExtension.Local.Stability.SourceDifferenceScalarMeasurable
import EmcsfAcExtension.Local.Stability.SourceDifferenceArea

/-! # Repaired scalar-curvature source difference

The literal outgoing and incoming scalar primitives are combined only after
both area estimates and measurability are proved. The author-adopted internal project record
remainder is retained in the conclusion.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- [internal]
 Conditional helper for
`restart-sec-bv-stability-independent#scalar-curvature-source-difference`.
The repaired contract of internal project record retains `C σ ε⁴ Δ₀/M`.
Constants depend only on the fixed envelope and ratio constants `A,D`,
uniformly in the triangle, coupling, background, data and derivative suprema. -/
theorem scalar_curvature_source_difference_of_differences (A D : ℝ)
    (hA : 0 < A) (hD : 0 < D) : ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
    ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ^ 2 + sigma e M T ≤ η →
      RatioDifferences D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
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
  obtain ⟨Cj, hCj, hj⟩ := scalar_source_j_difference_of_differences A D hA hD
  obtain ⟨Ck, hCk, hk⟩ := scalar_source_k_difference_of_differences A D hA hD
  refine ⟨1 / 4, Cj + Ck, by norm_num, add_pos hCj hCk, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ hset₁ hset₂ hsmall hratio
  have hσ : 0 ≤ sigma e M T := by unfold sigma; positivity
  have hε : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans
    (hset₂.box.2 (0, 0) ⟨le_rfl, le_rfl, hset₂.pos.le⟩).2.2.2.2.2.1
  have hε₂ : ε ^ 2 ≤ 1 / 4 := (le_add_of_nonneg_right hσ).trans hsmall
  have hσ₁ : sigma e M T ≤ 1 := by nlinarith only [hsmall, sq_nonneg ε]
  have hM : 0 < M := zero_lt_one.trans_le hset₂.box.1
  have hδ : 0 ≤ dataDist h₁ h₂ T := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  let Sj := fun (S : Fields) (p : ℝ × ℝ) =>
    (S.nu p.1 p.2 : ℂ) * S.theta p.1 p.2 / (S.r p.1 p.2 : ℂ) ^ 2 *
      (curvScalar (triangle 0 T) S p.1 p.2 +
        2 * starRingEnd ℂ (curvScalar (triangle 0 T) S p.1 p.2))
  let Sk := fun (S : Fields) (p : ℝ × ℝ) =>
    (S.lam p.1 p.2 : ℂ) * S.xi p.1 p.2 / (S.r p.1 p.2 : ℂ) ^ 2 *
      (curvScalarIn e (triangle 0 T) S p.1 p.2 +
        2 * starRingEnd ℂ (curvScalarIn e (triangle 0 T) S p.1 p.2))
  let Bj := Cj * ε ^ 2 * ((jDist T S₁ S₂).toReal + (kDist e T S₁ S₂).toReal) +
    Cj * ε ^ 3 * (geomDist T S₁ S₂).toReal + Cj * sigma e M T * ε ^ 4 * dataDist h₁ h₂ T / M
  let Bk := Ck * ε ^ 2 * ((jDist T S₁ S₂).toReal + (kDist e T S₁ S₂).toReal) +
    Ck * ε ^ 3 * (geomDist T S₁ S₂).toReal + Ck * sigma e M T * ε ^ 4 * dataDist h₁ h₂ T / M
  have hBj : 0 ≤ Bj := by dsimp [Bj]; positivity
  have hBk : 0 ≤ Bk := by dsimp [Bk]; positivity
  have hmj : Measurable ((triangle 0 T).indicator (fun p => ‖Sj S₁ p - Sj S₂ p‖ₑ)) :=
    measurable_triangle_difference_enorm (measurable_scalar_source_j hset₁)
      (measurable_scalar_source_j hset₂)
  have hmk : Measurable ((triangle 0 T).indicator (fun p => ‖Sk S₁ p - Sk S₂ p‖ₑ)) :=
    measurable_triangle_difference_enorm (measurable_scalar_source_k hset₁)
      (measurable_scalar_source_k hset₂)
  have hsum : (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v,
      ‖Sj S₁ (u, v) - Sj S₂ (u, v)‖ₑ + ‖Sk S₁ (u, v) - Sk S₂ (u, v)‖ₑ) =
      (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, ‖Sj S₁ (u, v) - Sj S₂ (u, v)‖ₑ) +
      ∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, ‖Sk S₁ (u, v) - Sk S₂ (u, v)‖ₑ := by
    simpa only using incoming_area_add_of_measurable_indicators hmj hmk
  calc
    _ = _ := hsum
    _ ≤ ENNReal.ofReal Bj + ENNReal.ofReal Bk :=
      add_le_add (hj T e ε M S₁ S₂ h₁ h₂ hset₁ hset₂ hε₂ hσ₁ hratio)
        (hk T e ε M S₁ S₂ h₁ h₂ hset₁ hset₂ hε₂ hσ₁ hratio)
    _ = ENNReal.ofReal (Bj + Bk) := (ENNReal.ofReal_add hBj hBk).symm
    _ = _ := by dsimp only [Bj, Bk]; congr 1; ring

end EmcsfAcExtension.Local.Stab
