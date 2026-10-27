module

public import Mathlib

/-! # Cubic Lipschitz algebra for the initial renormalized derivative

The coefficient `3 ε²` is kept explicitly before the radial Hardy estimate.
-/

public section

open Complex

namespace EmcsfAcExtension.Local.Stab

/-- Difference of squared complex norms on the radius-`ε` ball.
The exact multiplier `2 ε` is universal and independent of all factors. -/
theorem abs_norm_sq_difference_le {x y : ℂ} {ε : ℝ}
    (hx : ‖x‖ ≤ ε) (hy : ‖y‖ ≤ ε) :
    |‖x‖ ^ 2 - ‖y‖ ^ 2| ≤ 2 * ε * ‖x - y‖ := by
  rw [show ‖x‖ ^ 2 - ‖y‖ ^ 2 = (‖x‖ + ‖y‖) * (‖x‖ - ‖y‖) by ring,
    abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact mul_le_mul (by linarith only [hx, hy]) (abs_norm_sub_norm_le x y)
    (abs_nonneg _) (by linarith only [hx, norm_nonneg x])

/-- The complex cubic `|x|² x` is `3 ε²`-Lipschitz on the radius-`ε` ball.
The numerical multiplier is universal. -/
theorem norm_cubic_difference_le {x y : ℂ} {ε : ℝ}
    (hx : ‖x‖ ≤ ε) (hy : ‖y‖ ≤ ε) :
    ‖(‖x‖ : ℂ) ^ 2 * x - (‖y‖ : ℂ) ^ 2 * y‖ ≤ 3 * ε ^ 2 * ‖x - y‖ := by
  have hε : 0 ≤ ε := (norm_nonneg x).trans hx
  have hδ := abs_norm_sq_difference_le hx hy
  have hpow := pow_le_pow_left₀ (norm_nonneg x) hx 2
  rw [show (‖x‖ : ℂ) ^ 2 * x - (‖y‖ : ℂ) ^ 2 * y =
      (‖x‖ : ℂ) ^ 2 * (x - y) + ((‖x‖ : ℂ) ^ 2 - (‖y‖ : ℂ) ^ 2) * y by ring]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul, ← ofReal_pow, ← ofReal_pow, ← ofReal_sub,
    norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x‖)]
  have h₁ := mul_le_mul_of_nonneg_right hpow (norm_nonneg (x - y))
  have h₂ := mul_le_mul hδ hy (norm_nonneg _) (by positivity)
  nlinarith only [h₁, h₂]

/-- Initial-j algebra with an explicit optical-factor difference `U`.
All coefficients are the exact universal `1,1,3,1`; the data, cubic and
mass terms are separated before any integration or smallness argument. -/
theorem norm_initial_j_difference_le {x₁ x₂ d₁ d₂ : ℂ} {γ₁ γ₂ q ε U : ℝ}
    (hγ : 0 ≤ γ₁) (hγ₁ : γ₁ ≤ 1) (hδγ : |γ₁ - γ₂| ≤ U)
    (hq : 0 ≤ q) (hx₁ : ‖x₁‖ ≤ ε) (hx₂ : ‖x₂‖ ≤ ε) :
    ‖(γ₁ : ℂ) * (d₁ - (q : ℂ) * (‖x₁‖ : ℂ) ^ 2 * x₁) -
      (γ₂ : ℂ) * (d₂ - (q : ℂ) * (‖x₂‖ : ℂ) ^ 2 * x₂)‖ ≤
      ‖d₁ - d₂‖ + U * ‖d₂‖ + 3 * ε ^ 2 * q * ‖x₁ - x₂‖ +
        U * ε ^ 2 * q * ‖x₂‖ := by
  have hε : 0 ≤ ε := (norm_nonneg x₁).trans hx₁
  have hU : 0 ≤ U := (abs_nonneg _).trans hδγ
  have heq :
      (γ₁ : ℂ) * (d₁ - (q : ℂ) * (‖x₁‖ : ℂ) ^ 2 * x₁) -
        (γ₂ : ℂ) * (d₂ - (q : ℂ) * (‖x₂‖ : ℂ) ^ 2 * x₂) =
      (γ₁ : ℂ) * (d₁ - d₂) + ((γ₁ - γ₂ : ℝ) : ℂ) * d₂ -
        (γ₁ : ℂ) * q * ((‖x₁‖ : ℂ) ^ 2 * x₁ - (‖x₂‖ : ℂ) ^ 2 * x₂) -
        ((γ₁ - γ₂ : ℝ) : ℂ) * q * (‖x₂‖ : ℂ) ^ 2 * x₂ := by push_cast; ring
  rw [heq]
  apply ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)).trans
  apply (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl).trans
  simp only [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_norm,
    abs_of_nonneg hγ, abs_of_nonneg hq]
  have h₁ : γ₁ * ‖d₁ - d₂‖ ≤ ‖d₁ - d₂‖ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hγ₁ (norm_nonneg _)
  have h₂ := mul_le_mul_of_nonneg_right hδγ (norm_nonneg d₂)
  have h₃ : γ₁ * q * ‖(‖x₁‖ : ℂ) ^ 2 * x₁ - (‖x₂‖ : ℂ) ^ 2 * x₂‖ ≤
      3 * ε ^ 2 * q * ‖x₁ - x₂‖ := by
    have h := mul_le_mul (mul_le_mul_of_nonneg_right hγ₁ hq)
      (norm_cubic_difference_le hx₁ hx₂) (norm_nonneg _) (by positivity)
    nlinarith only [h]
  have h₄ := mul_le_mul_of_nonneg_right
    (mul_le_mul hδγ (pow_le_pow_left₀ (norm_nonneg x₂) hx₂ 2) (sq_nonneg _) hU)
    (mul_nonneg hq (norm_nonneg x₂))
  nlinarith only [h₁, h₂, h₃, h₄]

end EmcsfAcExtension.Local.Stab
