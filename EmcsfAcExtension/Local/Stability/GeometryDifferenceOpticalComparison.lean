module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.MeanValue
public import EmcsfAcExtension.Local.Stability.GeometryDifferenceAlgebra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Uniform comparison of reconstructed optical factors

Solving the axis identities for the mass gap uses the decaying
exponential. Its Lipschitz constant is `1` on nonnegative exponents,
so these algebraic bounds require no derivative supremum or radius cutoff.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- The decaying real exponential is `1`-Lipschitz on the nonnegative
half-line. The literal coefficient is independent of both exponents. -/
theorem stab_exp_neg_sub_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.exp (-x) - Real.exp (-y)| ≤ |x - y| := by
  have hd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s : ℝ => Real.exp (-s))
      (-Real.exp (-t)) (Ici 0) t := by
    intro t ht
    simpa only [mul_neg_one] using!
      ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg).hasDerivWithinAt
  have hb : ∀ t ∈ Ici (0 : ℝ), ‖-Real.exp (-t)‖ ≤ 1 := by
    intro t ht
    rw [norm_neg, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
  simpa only [Real.norm_eq_abs, one_mul] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Ici 0) hy hx

/-- Quotients with denominator at least `1/4` and second numerator at
most `1` obey the fixed coefficients `4` and `16`. There is no upper
bound on the first numerator and no solution-dependent constant. -/
theorem stab_optical_quotient_sub_le {n₁ n₂ l₁ l₂ : ℝ}
    (hl₁ : 1 / 4 ≤ l₁) (hl₂ : 1 / 4 ≤ l₂) (hn₂ : |n₂| ≤ 1) :
    |n₁ / l₁ - n₂ / l₂| ≤ 4 * |n₁ - n₂| + 16 * |l₁ - l₂| := by
  have hp₁ : 0 < l₁ := lt_of_lt_of_le (by norm_num) hl₁
  have hp₂ : 0 < l₂ := lt_of_lt_of_le (by norm_num) hl₂
  have hdiv : |(n₁ - n₂) / l₁| ≤ 4 * |n₁ - n₂| := by
    rw [abs_div, abs_of_pos hp₁, div_le_iff₀ hp₁]
    have hh := mul_le_mul_of_nonneg_left hl₁ (show 0 ≤ 4 * |n₁ - n₂| by positivity)
    linarith only [hh]
  have hinv : |l₁⁻¹ - l₂⁻¹| ≤ 16 * |l₁ - l₂| := by
    have hi := stab_inv_gap_sub_le (μ₁ := 1 - l₁) (μ₂ := 1 - l₂)
      (by simpa only [sub_sub_cancel] using hl₁) (by simpa only [sub_sub_cancel] using hl₂)
    simpa only [sub_sub_cancel, sub_sub_sub_cancel_left, abs_sub_comm] using hi
  have hsplit : n₁ / l₁ - n₂ / l₂ = (n₁ - n₂) / l₁ + n₂ * (l₁⁻¹ - l₂⁻¹) := by
    field_simp
    ring
  calc
    _ ≤ |(n₁ - n₂) / l₁| + |n₂ * (l₁⁻¹ - l₂⁻¹)| := by
      rw [hsplit]
      exact abs_add_le _ _
    _ ≤ 4 * |n₁ - n₂| + 16 * |l₁ - l₂| := by
      apply add_le_add hdiv
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul hn₂ hinv (abs_nonneg _) (by positivity)

/-- A mass gap reconstructed from an axis optical identity has
difference at most `4|δn| + 16|δl_axis| + 4|δI|`. These numerical
coefficients are universal. This conditional algebraic helper is used
after the field-level optical identities have been proved. -/
theorem stab_gap_sub_le_of_optical
    {n₁ n₂ l₁ l₂ I₁ I₂ γ₁ γ₂ : ℝ}
    (hl₁ : 1 / 4 ≤ l₁) (hl₂ : 1 / 4 ≤ l₂)
    (hn₂ : |n₂| ≤ 1) (hI₁ : 0 ≤ I₁) (hI₂ : 0 ≤ I₂)
    (hγ₁ : γ₁ = n₁ / l₁ * Real.exp (-I₁))
    (hγ₂ : γ₂ = n₂ / l₂ * Real.exp (-I₂)) :
    |γ₁ - γ₂| ≤ 4 * |n₁ - n₂| + 16 * |l₁ - l₂| + 4 * |I₁ - I₂| := by
  have hp₂ : 0 < l₂ := lt_of_lt_of_le (by norm_num) hl₂
  have hE₁ : |Real.exp (-I₁)| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hI₁)
  have hN₂ : |n₂ / l₂| ≤ 4 := by
    rw [abs_div, abs_of_pos hp₂, div_le_iff₀ hp₂]
    linarith only [hl₂, hn₂]
  have hsplit : γ₁ - γ₂ = (n₁ / l₁ - n₂ / l₂) * Real.exp (-I₁) +
      (n₂ / l₂) * (Real.exp (-I₁) - Real.exp (-I₂)) := by
    rw [hγ₁, hγ₂]
    ring
  calc
    _ ≤ |(n₁ / l₁ - n₂ / l₂) * Real.exp (-I₁)| +
        |(n₂ / l₂) * (Real.exp (-I₁) - Real.exp (-I₂))| := by
      rw [hsplit]
      exact abs_add_le _ _
    _ = |n₁ / l₁ - n₂ / l₂| * |Real.exp (-I₁)| +
        |n₂ / l₂| * |Real.exp (-I₁) - Real.exp (-I₂)| := by rw [abs_mul, abs_mul]
    _ ≤ |n₁ / l₁ - n₂ / l₂| + 4 * |I₁ - I₂| := by
      exact add_le_add (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hE₁ (abs_nonneg _))
        (mul_le_mul hN₂ (stab_exp_neg_sub_le hI₁ hI₂) (abs_nonneg _) (by norm_num))
    _ ≤ _ := add_le_add (stab_optical_quotient_sub_le hl₁ hl₂ hn₂) le_rfl

end EmcsfAcExtension.Local
