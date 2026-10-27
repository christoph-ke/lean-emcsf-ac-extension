module

public import Mathlib

/-! # Scalar curvature source differences before the Hardy area estimate

The curvature and its conjugate share the same real inverse radius.
Taking norms after the coefficient subtraction gives the universal factor
three without differentiating either integral or its endpoint maps.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

private theorem norm_scalar_combination_le (z : ℂ) :
    ‖z + 2 * starRingEnd ℂ z‖ ≤ 3 * ‖z‖ := by
  calc
    _ ≤ ‖z‖ + ‖2 * starRingEnd ℂ z‖ := norm_add_le _ _
    _ = _ := by simp only [norm_mul, RCLike.norm_conj]; norm_num; ring

/-- Difference of coefficient-weighted scalar curvature primitives,
including their conjugate summands. The numerical coefficient `3` is
universal; all coefficient and integrand differences remain explicit. -/
theorem scalar_primitive_source_difference_enorm_le {a b : ℝ} {f₁ f₂ : ℝ → ℂ}
    (hf₁ : IntegrableOn f₁ (Ioc a b)) (hf₂ : IntegrableOn f₂ (Ioc a b)) (c₁ c₂ : ℂ) :
    ‖c₁ * ((∫ w in Ioc a b, f₁ w) + 2 * starRingEnd ℂ (∫ w in Ioc a b, f₁ w)) -
      c₂ * ((∫ w in Ioc a b, f₂ w) + 2 * starRingEnd ℂ (∫ w in Ioc a b, f₂ w))‖ₑ ≤
      ENNReal.ofReal 3 *
        (‖c₁ - c₂‖ₑ * (∫⁻ w in Ioc a b, ‖f₁ w‖ₑ) +
          ‖c₂‖ₑ * (∫⁻ w in Ioc a b, ‖f₁ w - f₂ w‖ₑ)) := by
  let z₁ := ∫ w in Ioc a b, f₁ w
  let z₂ := ∫ w in Ioc a b, f₂ w
  have hz : z₁ - z₂ = ∫ w in Ioc a b, f₁ w - f₂ w := (integral_sub hf₁ hf₂).symm
  have hcomb (z : ℂ) : ‖z + 2 * starRingEnd ℂ z‖ₑ ≤ ENNReal.ofReal 3 * ‖z‖ₑ := by
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ofReal_norm] using
      ENNReal.ofReal_le_ofReal (norm_scalar_combination_le z)
  have heq : c₁ * (z₁ + 2 * starRingEnd ℂ z₁) - c₂ * (z₂ + 2 * starRingEnd ℂ z₂) =
      (c₁ - c₂) * (z₁ + 2 * starRingEnd ℂ z₁) +
        c₂ * ((z₁ - z₂) + 2 * starRingEnd ℂ (z₁ - z₂)) := by
    rw [map_sub]
    ring
  change ‖c₁ * (z₁ + 2 * starRingEnd ℂ z₁) - c₂ * (z₂ + 2 * starRingEnd ℂ z₂)‖ₑ ≤ _
  rw [heq]
  calc
    _ ≤ ‖(c₁ - c₂) * (z₁ + 2 * starRingEnd ℂ z₁)‖ₑ +
        ‖c₂ * ((z₁ - z₂) + 2 * starRingEnd ℂ (z₁ - z₂))‖ₑ := enorm_add_le _ _
    _ ≤ ‖c₁ - c₂‖ₑ * (ENNReal.ofReal 3 * ‖z₁‖ₑ) +
        ‖c₂‖ₑ * (ENNReal.ofReal 3 * ‖z₁ - z₂‖ₑ) := by
      rw [enorm_mul, enorm_mul]
      exact add_le_add (mul_le_mul' le_rfl (hcomb z₁))
        (mul_le_mul' le_rfl (hcomb (z₁ - z₂)))
    _ ≤ ‖c₁ - c₂‖ₑ * (ENNReal.ofReal 3 * ∫⁻ w in Ioc a b, ‖f₁ w‖ₑ) +
        ‖c₂‖ₑ * (ENNReal.ofReal 3 * ∫⁻ w in Ioc a b, ‖f₁ w - f₂ w‖ₑ) := by
      rw [hz]
      exact add_le_add
        (mul_le_mul' le_rfl (mul_le_mul' le_rfl (enorm_integral_le_lintegral_enorm _)))
        (mul_le_mul' le_rfl (mul_le_mul' le_rfl (enorm_integral_le_lintegral_enorm _)))
    _ = _ := by ring

/-- Real norm version of the coefficient-weighted primitive subtraction.
The multiplier `3` is universal and keeps both conjugated summands.
All characteristic integrability hypotheses are explicit. -/
theorem scalar_primitive_source_difference_norm_le {a b : ℝ} {f₁ f₂ : ℝ → ℂ}
    (hab : a ≤ b) (hf₁ : IntervalIntegrable f₁ volume a b)
    (hf₂ : IntervalIntegrable f₂ volume a b) (c₁ c₂ : ℂ) :
    ‖c₁ * ((∫ w in a..b, f₁ w) + 2 * starRingEnd ℂ (∫ w in a..b, f₁ w)) -
      c₂ * ((∫ w in a..b, f₂ w) + 2 * starRingEnd ℂ (∫ w in a..b, f₂ w))‖ ≤
      3 * (‖c₁ - c₂‖ * (∫ w in a..b, ‖f₁ w‖) +
        ‖c₂‖ * (∫ w in a..b, ‖f₁ w - f₂ w‖)) := by
  let z₁ := ∫ w in a..b, f₁ w
  let z₂ := ∫ w in a..b, f₂ w
  have hz : z₁ - z₂ = ∫ w in a..b, f₁ w - f₂ w :=
    (intervalIntegral.integral_sub hf₁ hf₂).symm
  have heq : c₁ * (z₁ + 2 * starRingEnd ℂ z₁) - c₂ * (z₂ + 2 * starRingEnd ℂ z₂) =
      (c₁ - c₂) * (z₁ + 2 * starRingEnd ℂ z₁) +
        c₂ * ((z₁ - z₂) + 2 * starRingEnd ℂ (z₁ - z₂)) := by rw [map_sub]; ring
  change ‖c₁ * (z₁ + 2 * starRingEnd ℂ z₁) - c₂ * (z₂ + 2 * starRingEnd ℂ z₂)‖ ≤ _
  rw [heq]
  calc
    _ ≤ ‖c₁ - c₂‖ * ‖z₁ + 2 * starRingEnd ℂ z₁‖ +
        ‖c₂‖ * ‖(z₁ - z₂) + 2 * starRingEnd ℂ (z₁ - z₂)‖ := by
      simpa only [norm_mul] using norm_add_le
        ((c₁ - c₂) * (z₁ + 2 * starRingEnd ℂ z₁))
        (c₂ * ((z₁ - z₂) + 2 * starRingEnd ℂ (z₁ - z₂)))
    _ ≤ ‖c₁ - c₂‖ * (3 * ‖z₁‖) + ‖c₂‖ * (3 * ‖z₁ - z₂‖) :=
      add_le_add (mul_le_mul_of_nonneg_left (norm_scalar_combination_le z₁) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (norm_scalar_combination_le (z₁ - z₂)) (norm_nonneg _))
    _ ≤ ‖c₁ - c₂‖ * (3 * (∫ w in a..b, ‖f₁ w‖)) +
        ‖c₂‖ * (3 * (∫ w in a..b, ‖f₁ w - f₂ w‖)) := by
      rw [hz]
      exact add_le_add (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm hab)
          (by norm_num : (0 : ℝ) ≤ 3)) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm hab)
            (by norm_num : (0 : ℝ) ≤ 3)) (norm_nonneg _))
    _ = _ := by ring

end EmcsfAcExtension.Local.Stab
