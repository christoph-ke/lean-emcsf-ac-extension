module

public import EmcsfAcExtension.Local.Broad.ChargeAlgebra

/-! # Reciprocal-gap algebra for the broad potential comparison -/

public section

namespace EmcsfAcExtension.Local.Broad

/-- A product difference bound with exact universal coefficients one. -/
theorem abs_product_sub_le (a b c d : ℝ) :
    |a * b - c * d| ≤ |a| * |b - d| + |a - c| * |d| := by
  calc
    _ = |a * (b - d) + (a - c) * d| := by congr 1; ring
    _ ≤ |a * (b - d)| + |(a - c) * d| := abs_add_le _ _
    _ = _ := by rw [abs_mul, abs_mul]

/-- The reciprocal of a positive gap has difference bounded by the gap
difference divided by `c²`. This coefficient depends only on the lower gap
bound, uniformly in the two gaps and their difference bound. -/
theorem abs_inv_sub_le_of_lower {g₁ g₂ c X : ℝ} (hc : 0 < c)
    (hg₁ : c ≤ g₁) (hg₂ : c ≤ g₂) (hδg : |g₁ - g₂| ≤ X) :
    |g₁⁻¹ - g₂⁻¹| ≤ X / c ^ 2 := by
  have h₁ := hc.trans_le hg₁
  have h₂ := hc.trans_le hg₂
  calc
    _ = |g₁ - g₂| / (g₁ * g₂) := by
      rw [inv_sub_inv h₁.ne' h₂.ne', abs_div, abs_sub_comm,
        abs_of_pos (mul_pos h₁ h₂)]
    _ ≤ X / c ^ 2 := div_le_div₀ ((abs_nonneg _).trans hδg) hδg (sq_pos_of_pos hc)
      (by simpa only [pow_two] using mul_le_mul hg₁ hg₂ hc.le h₁.le)

/-- The factor `νλ/g` in the potential equation, including every product
and reciprocal-gap error. Coefficients depend only on the box `c,C`,
uniformly in all six field values and both error bounds. -/
theorem potential_factor_difference_of_bounds {n₁ n₂ l₁ l₂ g₁ g₂ c C G X : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (hG : 0 ≤ G) (_hX : 0 ≤ X)
    (hn₁ : |n₁| ≤ C) (hn₂ : |n₂| ≤ C) (hl₁ : |l₁| ≤ C) (hl₂ : |l₂| ≤ C)
    (hg₁ : c ≤ g₁) (hg₂ : c ≤ g₂)
    (hδn : |n₁ - n₂| ≤ G) (hδl : |l₁ - l₂| ≤ G) (hδg : |g₁ - g₂| ≤ X) :
    |n₁ * l₁ / g₁| ≤ C ^ 2 / c ∧
      |n₁ * l₁ / g₁ - n₂ * l₂ / g₂| ≤ (2 * C / c) * G + (C ^ 2 / c ^ 2) * X := by
  have hg₁0 := hc.trans_le hg₁
  have hg₂0 := hc.trans_le hg₂
  have hprod : |n₁ * l₁ - n₂ * l₂| ≤ 2 * C * G := by
    apply (abs_product_sub_le _ _ _ _).trans
    calc
      _ ≤ C * G + G * C := by gcongr
      _ = _ := by ring
  have hprod₁ : |n₁ * l₁| ≤ C ^ 2 := by rw [abs_mul, pow_two]; gcongr
  have hprod₂ : |n₂ * l₂| ≤ C ^ 2 := by rw [abs_mul, pow_two]; gcongr
  refine ⟨?_, ?_⟩
  · rw [abs_div, abs_of_pos hg₁0]
    exact div_le_div₀ (sq_nonneg C) hprod₁ hc hg₁
  · calc
      _ = |(n₁ * l₁) * g₁⁻¹ - (n₂ * l₂) * g₂⁻¹| := by simp only [div_eq_mul_inv]
      _ ≤ |n₁ * l₁| * |g₁⁻¹ - g₂⁻¹| + |n₁ * l₁ - n₂ * l₂| * |g₂⁻¹| :=
        abs_product_sub_le _ _ _ _
      _ ≤ C ^ 2 * (X / c ^ 2) + (2 * C * G) * c⁻¹ := by
        have hi : |g₂⁻¹| ≤ c⁻¹ := by
          rw [abs_of_pos (inv_pos.mpr hg₂0)]
          exact inv_le_inv₀ hg₂0 hc |>.mpr hg₂
        gcongr
        exact abs_inv_sub_le_of_lower hc hg₁ hg₂ hδg
      _ = _ := by ring

end EmcsfAcExtension.Local.Broad
