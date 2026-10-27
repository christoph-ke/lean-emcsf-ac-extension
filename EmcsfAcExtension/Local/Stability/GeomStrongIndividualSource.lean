module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeomStrongElectricIndividual
import EmcsfAcExtension.Local.Stability.GeomStrongIndividualScalar
import EmcsfAcExtension.Local.Stability.GeomStrongPrimitiveMeas
import EmcsfAcExtension.Infra.Triangle

/-! # Individual geometric-source area at the quadratic scale

Ordered scalar mass and the electric polynomial majorant combine before
the charged area factor is bounded by the small dimensionless scale.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- An individual common geometric source has area budget
`(4096 A²+800) ε²` when `σ≤1`. The dependence on `A` is explicit;
all coefficients are universal before fields, scales, data and higher
derivatives, uniformly in minimum radii. -/
theorem stab_geometric_source_area_le_c1
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) (hA : 0 ≤ A)
    (hε : ε ^ 2 ≤ 1 / 4) (hσ : sigma e M T ≤ 1) :
    (∫⁻ p in triangle 0 T, ‖geomSource S p.1 p.2‖ₑ) ≤
      ENNReal.ofReal ((4096 * A ^ 2 + 800) * ε ^ 2) := by
  let F := fun p : ℝ × ℝ => ‖(triangle 0 T).indicator
    (Function.uncurry (geometricScalarSource (triangle 0 T) S)) p‖ₑ
  let B := 400 * (|e| * M) ^ 2 * ε ^ 2
  have hσ0 : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have mF : Measurable F := (stab_geometricScalarSource_borel_c1 hset).enorm
  have hF p (hp : p ∈ triangle 0 T) : F p =
      ‖geometricScalarSource (triangle 0 T) S p.1 p.2‖ₑ := by
    dsimp only [F]
    rw [indicator_of_mem hp]
    rfl
  have hb : (∫⁻ p in triangle 0 T, ‖geomSource S p.1 p.2‖ₑ) ≤
      (∫⁻ p in triangle 0 T, F p) + ENNReal.ofReal B * volume (triangle 0 T) := by
    have hpoint : ∀ p ∈ triangle 0 T, ‖geomSource S p.1 p.2‖ₑ ≤ F p + ENNReal.ofReal B := by
      intro p hp
      have he := stab_geometric_electric_source_norm_le_c1 hset hp.1 hp.2.1 hp.2.2
      rw [stab_geometric_source_split_c1 hset hp.1 hp.2.1 hp.2.2,
        ← ofReal_norm, Real.norm_eq_abs, abs_neg, hF p hp]
      apply (ENNReal.ofReal_le_ofReal ((Complex.abs_re_le_norm _).trans (norm_add_le _ _))).trans
      rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
      rw [ofReal_norm]
      exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal he)
    have hh := setLIntegral_mono' (μ := (volume : Measure (ℝ × ℝ))) (measurableSet_triangle 0 T)
        hpoint
    rw [lintegral_add_left mF, setLIntegral_const] at hh
    simpa only [mul_comm] using hh
  have hareaF : (∫⁻ p in triangle 0 T, F p) =
      ∫⁻ p in triangle 0 T, ‖geometricScalarSource (triangle 0 T) S p.1 p.2‖ₑ :=
    setLIntegral_congr_fun (measurableSet_triangle 0 T) hF
  rw [hareaF, volume_triangle hset.pos.le, sub_zero, ← ENNReal.ofReal_mul hB] at hb
  have hscale : B * (T ^ 2 / 2) = 800 * sigma e M T * ε ^ 2 := by
    dsimp only [B, sigma]
    rw [← sq_abs e]
    ring
  rw [hscale] at hb
  apply (hb.trans (add_le_add (stab_geometric_scalar_area_le_c1 hset hA hε) le_rfl)).trans
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hh := mul_le_mul_of_nonneg_right hσ (show 0 ≤ 800 * ε ^ 2 by positivity)
  nlinarith only [hh]

end EmcsfAcExtension.Local
