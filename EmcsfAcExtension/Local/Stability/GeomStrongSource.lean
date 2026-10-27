module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeomStrongElectricClose
import EmcsfAcExtension.Local.Stability.GeomStrongScalarClose
import EmcsfAcExtension.Local.Stability.GeomStrongPrimitiveMeas
import EmcsfAcExtension.Infra.Triangle

/-! # The geometric source difference

The scalar ordered area estimate and the quadratic electric primitive
comparison give G1 with every small factor and constant scope retained.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [internal]
The common geometric source satisfies G1, charged_SF_new_version.tex:L5414–5424,
with the repaired primitive subtraction in approved internal project record A1–A12.
The threshold and constant depend only on `A` and the literal box,
before all fields, coupling, background, time and data, uniformly in
minimum radii and initial derivative suprema. -/
theorem stab_geometric_source_difference (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        (∫⁻ p in triangle 0 T, ‖geomSource S₁ p.1 p.2 - geomSource S₂ p.1 p.2‖ₑ) ≤
          ENNReal.ofReal (C * ε * ((jDist T S₁ S₂).toReal + (kDist e T S₁ S₂).toReal) +
            C * ε ^ 2 * (geomDist T S₁ S₂).toReal + C * sigma e M T *
              (dataDist h₁ h₂ T + (jDist T S₁ S₂).toReal + (kDist e T S₁ S₂).toReal +
                ε * (geomDist T S₁ S₂).toReal)) := by
  obtain ⟨ηs, Cs, hηs, hCs, hScalar⟩ := stab_geometric_scalar_source_difference_c1 A hA
  obtain ⟨ηe, Ce, hηe, hCe, hElectric⟩ := stab_geometric_electric_source_difference_c1 A hA
  let C := Cs + 2 * Ce
  refine ⟨min ηs ηe, C, lt_min hηs hηe, by dsimp only [C]; positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall
  let J := (jDist T S₁ S₂).toReal
  let K := (kDist e T S₁ S₂).toReal
  let G := (geomDist T S₁ S₂).toReal
  let H := dataDist h₁ h₂ T + J + K + ε * G
  let B := Ce * (|e| * M) ^ 2 * H
  let F := fun p : ℝ × ℝ => ‖(triangle 0 T).indicator
    (Function.uncurry (geometricScalarSource (triangle 0 T) S₁)) p -
      (triangle 0 T).indicator
        (Function.uncurry (geometricScalarSource (triangle 0 T) S₂)) p‖ₑ
  have hJ : 0 ≤ J := ENNReal.toReal_nonneg
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hΔ : 0 ≤ dataDist h₁ h₂ T := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hσ : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have mF : Measurable F := ((stab_geometricScalarSource_borel_c1 h₁s).sub
    (stab_geometricScalarSource_borel_c1 h₂s)).enorm
  have hF p (hp : p ∈ triangle 0 T) : F p =
      ‖geometricScalarSource (triangle 0 T) S₁ p.1 p.2 -
        geometricScalarSource (triangle 0 T) S₂ p.1 p.2‖ₑ := by
    dsimp only [F]
    rw [indicator_of_mem hp, indicator_of_mem hp]
    rfl
  have hb : (∫⁻ p in triangle 0 T, ‖geomSource S₁ p.1 p.2 - geomSource S₂ p.1 p.2‖ₑ) ≤
      (∫⁻ p in triangle 0 T, F p) + ENNReal.ofReal B * volume (triangle 0 T) := by
    have hpoint : ∀ p ∈ triangle 0 T, ‖geomSource S₁ p.1 p.2 - geomSource S₂ p.1 p.2‖ₑ ≤ F p +
        ENNReal.ofReal B := by
      intro p hp
      have hh := stab_geometric_source_sub_le_parts_c1 h₁s h₂s hp.1 hp.2.1 hp.2.2
      have he := hElectric T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
        (hsmall.trans (min_le_right _ _)) p.1 p.2 hp.1 hp.2.1 hp.2.2
      rw [hF p hp, ← ofReal_norm, Real.norm_eq_abs]
      apply (ENNReal.ofReal_le_ofReal hh).trans
      rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
      rw [ofReal_norm]
      exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal he)
    have hh := setLIntegral_mono' (μ := (volume : Measure (ℝ × ℝ))) (measurableSet_triangle 0 T)
        hpoint
    rw [lintegral_add_left mF, setLIntegral_const] at hh
    simpa only [mul_comm] using hh
  have hareaF : (∫⁻ p in triangle 0 T, F p) =
      ∫⁻ p in triangle 0 T, ‖geometricScalarSource (triangle 0 T) S₁ p.1 p.2 -
        geometricScalarSource (triangle 0 T) S₂ p.1 p.2‖ₑ :=
    setLIntegral_congr_fun (measurableSet_triangle 0 T) hF
  rw [hareaF, volume_triangle h₁s.pos.le, sub_zero,
    ← ENNReal.ofReal_mul hB] at hb
  have hscale : B * (T ^ 2 / 2) = 2 * Ce * sigma e M T * H := by
    dsimp only [B, sigma]
    rw [← sq_abs e]
    ring
  rw [hscale] at hb
  apply (hb.trans (add_le_add
    (hScalar T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hsmall.trans (min_le_left _ _))) le_rfl)).trans
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hC : Cs ≤ C := by dsimp only [C]; linarith only [hCe]
  calc
    _ = Cs * ε * (J + K) + Cs * ε ^ 2 * G + (Cs + 2 * Ce) * sigma e M T * H := by ring
    _ ≤ C * ε * (J + K) + C * ε ^ 2 * G + C * sigma e M T * H := by gcongr

end EmcsfAcExtension.Local
