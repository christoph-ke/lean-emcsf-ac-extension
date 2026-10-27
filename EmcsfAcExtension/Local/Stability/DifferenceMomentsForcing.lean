module

public import EmcsfAcExtension.Local.Stability.DifferenceMomentsAlgebra
public import EmcsfAcExtension.Local.Stability.GeometryDifferenceAlgebra
import Mathlib.Tactic.FieldSimp

/-! # Norm of the exact radial difference forcing

The inverse-gap difference retains the mass-ratio factor, and the
moving-weight difference retains the individual scalar oscillation.
All numerical coefficients refer to the literal box with gap at least `1/4`.
-/

public section

namespace EmcsfAcExtension.Local

/-- The damped radial nonlinearity has norm at most `‖z‖` on the unit
ball, with exact coefficient `1` independent of any field parameter. -/
theorem stab_radial_nonlinearity_norm_le {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖z - ‖z‖ ^ 2 • z‖ ≤ ‖z‖ := by
  have hz2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith only [hz, norm_nonneg z]
  have heq : z - ‖z‖ ^ 2 • z = (1 - ‖z‖ ^ 2 : ℝ) • z := by
    rw [sub_smul, one_smul]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hz2)]
  nlinarith only [sq_nonneg ‖z‖, norm_nonneg z]

/-- The unabsorbed outgoing forcing has coefficients `4` and `16`
for the derivative and mass differences. The geometric forcing keeps
`|δa| * ‖z₂‖` explicitly. All coefficients are universal. -/
theorem stab_radial_difference_forcing_le
    {j₁ j₂ z₂ : ℂ} {μ₁ μ₂ a₁ a₂ : ℝ}
    (hg₁ : 1 / 4 ≤ 1 - μ₁) (hg₂ : 1 / 4 ≤ 1 - μ₂) (hz : ‖z₂‖ ≤ 1) :
    ‖j₁ / ((1 - μ₁ : ℝ) : ℂ) - j₂ / ((1 - μ₂ : ℝ) : ℂ) -
        (a₁ - a₂) • (z₂ - ‖z₂‖ ^ 2 • z₂)‖ ≤
      4 * ‖j₁ - j₂‖ + 16 * |μ₁ - μ₂| * ‖j₂‖ + |a₁ - a₂| * ‖z₂‖ := by
  have hp₁ : 0 < 1 - μ₁ := lt_of_lt_of_le (by norm_num) hg₁
  have hp₂ : 0 < 1 - μ₂ := lt_of_lt_of_le (by norm_num) hg₂
  have hg₁C : (1 - (μ₁ : ℂ)) ≠ 0 := by exact_mod_cast hp₁.ne'
  have hg₂C : (1 - (μ₂ : ℂ)) ≠ 0 := by exact_mod_cast hp₂.ne'
  have heq : j₁ / ((1 - μ₁ : ℝ) : ℂ) - j₂ / ((1 - μ₂ : ℝ) : ℂ) =
      (j₁ - j₂) / ((1 - μ₁ : ℝ) : ℂ) +
        (((1 - μ₁)⁻¹ - (1 - μ₂)⁻¹ : ℝ) : ℂ) * j₂ := by
    push_cast
    field_simp [hg₁C, hg₂C]
    ring
  have hdiv : ‖(j₁ - j₂) / ((1 - μ₁ : ℝ) : ℂ)‖ ≤ 4 * ‖j₁ - j₂‖ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp₁,
      div_le_iff₀ hp₁]
    have hh := mul_le_mul_of_nonneg_left hg₁
      (show 0 ≤ 4 * ‖j₁ - j₂‖ by positivity)
    nlinarith only [hh]
  have hinv : ‖(((1 - μ₁)⁻¹ - (1 - μ₂)⁻¹ : ℝ) : ℂ) * j₂‖ ≤
      16 * |μ₁ - μ₂| * ‖j₂‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (stab_inv_gap_sub_le hg₁ hg₂) (norm_nonneg _)
  have hgeo : ‖(a₁ - a₂) • (z₂ - ‖z₂‖ ^ 2 • z₂)‖ ≤ |a₁ - a₂| * ‖z₂‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (stab_radial_nonlinearity_norm_le hz) (abs_nonneg _)
  calc
    _ ≤ ‖j₁ / ((1 - μ₁ : ℝ) : ℂ) - j₂ / ((1 - μ₂ : ℝ) : ℂ)‖ +
        ‖(a₁ - a₂) • (z₂ - ‖z₂‖ ^ 2 • z₂)‖ := norm_sub_le _ _
    _ ≤ (‖(j₁ - j₂) / ((1 - μ₁ : ℝ) : ℂ)‖ +
        ‖(((1 - μ₁)⁻¹ - (1 - μ₂)⁻¹ : ℝ) : ℂ) * j₂‖) +
        ‖(a₁ - a₂) • (z₂ - ‖z₂‖ ^ 2 • z₂)‖ := by
      rw [heq]
      exact add_le_add (norm_add_le _ _) le_rfl
    _ ≤ _ := add_le_add (add_le_add hdiv hinv) hgeo

end EmcsfAcExtension.Local
