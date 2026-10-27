module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Algebra of moving radial weights and inverse mass gaps

The coefficients are the literal constants for the box `[1/4,1]`.
No field equation, data, solution or chosen estimate constant is used.
-/

public section

namespace EmcsfAcExtension.Local

/-- A common-label radial coefficient has relative difference at most
`20G`. The coefficient `20` is universal for the fixed stability box. -/
theorem stab_radial_weight_sub_le {a b r s G : ℝ}
    (ha : 1 / 4 ≤ a) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ 4 * s)
    (hab : |a - b| ≤ G) (hrr : |r - s| / r ≤ G) :
    |a / r - b / s| ≤ 20 * G * (a / r) := by
  have hG : 0 ≤ G := (abs_nonneg _).trans hab
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hba : b / s ≤ 16 * (a / r) := by
    rw [← mul_div_assoc, div_le_div_iff₀ hs hr]
    calc
      b * r ≤ r := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hb1 hr.le
      _ ≤ 4 * s := hrs
      _ ≤ 16 * a * s := mul_le_mul_of_nonneg_right (by linarith only [ha]) hs.le
  have hga : G / r ≤ 4 * G * (a / r) := by
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right hr]
    have h := mul_le_mul_of_nonneg_left (show 1 ≤ 4 * a by linarith only [ha]) hG
    nlinarith only [h]
  have hsplit : a / r - b / s = (a - b) / r + (b / s) * ((s - r) / r) := by
    field_simp
    ring
  calc
    |a / r - b / s| ≤ |a - b| / r + (b / s) * (|r - s| / r) := by
      rw [hsplit]
      simpa only [abs_div, abs_of_pos hr, abs_of_pos hs, abs_of_nonneg hb0,
        abs_mul, abs_sub_comm] using
        abs_add_le ((a - b) / r) ((b / s) * ((s - r) / r))
    _ ≤ G / r + (16 * (a / r)) * G := by
      exact add_le_add (div_le_div_of_nonneg_right hab hr.le)
        (mul_le_mul hba hrr (div_nonneg (abs_nonneg _) hr.le)
          (by positivity))
    _ ≤ 20 * G * (a / r) := by linarith only [hga]

/-- Reciprocals of positive mass gaps at least `1/4` differ by at most
`16` times the mass-ratio difference, uniformly in both gaps. -/
theorem stab_inv_gap_sub_le {μ₁ μ₂ : ℝ}
    (h₁ : 1 / 4 ≤ 1 - μ₁) (h₂ : 1 / 4 ≤ 1 - μ₂) :
    |(1 - μ₁)⁻¹ - (1 - μ₂)⁻¹| ≤ 16 * |μ₁ - μ₂| := by
  have hp₁ : 0 < 1 - μ₁ := lt_of_lt_of_le (by norm_num) h₁
  have hp₂ : 0 < 1 - μ₂ := lt_of_lt_of_le (by norm_num) h₂
  have hprod : 1 / 16 ≤ (1 - μ₁) * (1 - μ₂) := by
    have hh := mul_le_mul h₁ h₂ (by norm_num : (0 : ℝ) ≤ 1 / 4) hp₁.le
    norm_num at hh ⊢
    exact hh
  have heq : (1 - μ₁)⁻¹ - (1 - μ₂)⁻¹ =
      (μ₁ - μ₂) / ((1 - μ₁) * (1 - μ₂)) := by
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos (mul_pos hp₁ hp₂), div_le_iff₀ (mul_pos hp₁ hp₂)]
  have hh : (1 / 16) * (16 * |μ₁ - μ₂|) ≤
      ((1 - μ₁) * (1 - μ₂)) * (16 * |μ₁ - μ₂|) :=
    mul_le_mul_of_nonneg_right hprod (mul_nonneg (by norm_num) (abs_nonneg _))
  nlinarith only [hh]

/-- Replacing a moment's radius by a comparable radius costs at most
`16`, uniformly for all exponents in `[0,1]`. The numerator may vanish
at the axis; both endpoint radii are strictly positive. -/
theorem stab_radius_power_compare {r₁ r₂ R₁ R₂ p : ℝ}
    (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (hrc : r₂ ≤ 4 * r₁) (hRc : R₁ ≤ 4 * R₂) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (r₂ / R₂) ^ p ≤ 16 * (r₁ / R₁) ^ p := by
  have hbase : r₂ / R₂ ≤ 16 * (r₁ / R₁) := by
    rw [← mul_div_assoc, div_le_div_iff₀ hR₂ hR₁]
    have hh := mul_le_mul hrc hRc hR₁.le (by positivity : 0 ≤ 4 * r₁)
    nlinarith only [hh]
  have h16 : (16 : ℝ) ^ p ≤ 16 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 16) hp1
  calc
    _ ≤ (16 * (r₁ / R₁)) ^ p :=
      Real.rpow_le_rpow (div_nonneg hr₂ hR₂.le) hbase hp0
    _ = (16 : ℝ) ^ p * (r₁ / R₁) ^ p :=
      Real.mul_rpow (by norm_num) (div_nonneg hr₁ hR₁.le)
    _ ≤ _ := mul_le_mul_of_nonneg_right h16 (Real.rpow_nonneg (div_nonneg hr₁ hR₁.le) p)

end EmcsfAcExtension.Local
