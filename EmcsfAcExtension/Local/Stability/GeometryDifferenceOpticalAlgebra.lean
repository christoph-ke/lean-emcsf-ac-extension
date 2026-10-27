module

public import EmcsfAcExtension.Local.Stability.GeometryDifferenceOpticalComparison

/-! # Product estimates for the ordered optical comparison

The incoming reconstruction uses a decaying exponential. The outgoing
exponentials have a uniform endpoint bound supplied by the fixed box.
All constants below are numerical and independent of field parameters.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- The exponential difference is bounded by the larger endpoint
exponential times the exponent difference. The coefficient `1` is
uniform; the displayed bound `K` is the only dependence. -/
theorem stab_exp_sub_le_of_exp_le {x y K : ℝ}
    (hx : Real.exp x ≤ K) (hy : Real.exp y ≤ K) :
    |Real.exp x - Real.exp y| ≤ K * |x - y| := by
  have hd : ∀ t ∈ Iic (max x y),
      HasDerivWithinAt Real.exp (Real.exp t) (Iic (max x y)) t :=
    fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt
  have hb : ∀ t ∈ Iic (max x y), ‖Real.exp t‖ ≤ K := by
    intro t ht
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply (Real.exp_le_exp.mpr ht).trans
    rcases le_total x y with hxy | hyx
    · simpa only [max_eq_right hxy] using hy
    · simpa only [max_eq_left hyx] using hx
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Iic (max x y))
      (le_max_right x y) (le_max_left x y)

/-- A triple product difference has the three telescope costs with
literal coefficient `1`; only the displayed factor bounds enter. -/
theorem stab_triple_product_sub_le {a b c d e f A B C : ℝ}
    (hd : |d| ≤ A) (hb : |b| ≤ B) (he : |e| ≤ B) (hc : |c| ≤ C) :
    |a * b * c - d * e * f| ≤
      B * C * |a - d| + A * C * |b - e| + A * B * |c - f| := by
  have hA : 0 ≤ A := (abs_nonneg d).trans hd
  have hB : 0 ≤ B := (abs_nonneg b).trans hb
  have hC : 0 ≤ C := (abs_nonneg c).trans hc
  have hsplit : a * b * c - d * e * f =
      (a - d) * b * c + d * (b - e) * c + d * e * (c - f) := by ring
  have ht₁ := mul_le_mul_of_nonneg_left
    (mul_le_mul hb hc (abs_nonneg _) hB) (abs_nonneg (a - d))
  have ht₂ := mul_le_mul_of_nonneg_right
    (mul_le_mul hd hc (abs_nonneg _) hA) (abs_nonneg (b - e))
  have ht₃ := mul_le_mul_of_nonneg_right
    (mul_le_mul hd he (abs_nonneg _) hA) (abs_nonneg (c - f))
  calc
    _ ≤ |(a - d) * b * c + d * (b - e) * c| + |d * e * (c - f)| := by
      rw [hsplit]; exact abs_add_le _ _
    _ ≤ |(a - d) * b * c| + |d * (b - e) * c| + |d * e * (c - f)| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ _ := by
      simp only [abs_mul]
      nlinarith only [ht₁, ht₂, ht₃]

/-- The incoming optical product costs `4|δγ|+|δL₀|+4|δI|`.
All numerical constants are uniform in the two exponents and factors. -/
theorem stab_lam_product_sub_le {γ₁ γ₂ L₁ L₂ I₁ I₂ : ℝ}
    (hγ₂ : |γ₂| ≤ 1) (hL₁ : |L₁| ≤ 4) (hL₂ : |L₂| ≤ 4)
    (hI₁ : 0 ≤ I₁) (hI₂ : 0 ≤ I₂) :
    |γ₁ * L₁ * Real.exp (-I₁) - γ₂ * L₂ * Real.exp (-I₂)| ≤
      4 * |γ₁ - γ₂| + |L₁ - L₂| + 4 * |I₁ - I₂| := by
  have he : |Real.exp (-I₁)| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hI₁)
  have ht := stab_triple_product_sub_le (a := γ₁) (f := Real.exp (-I₂)) hγ₂ hL₁ hL₂ he
  have hd := stab_exp_neg_sub_le hI₁ hI₂
  nlinarith only [ht, hd]

/-- The outgoing optical product costs `16` times the sum of the
gap, axis expansion and exponent differences. The endpoint exponential
bound is exactly the universal `16` supplied by the fixed box. -/
theorem stab_nu_product_sub_le {γ₁ γ₂ l₁ l₂ I₁ I₂ : ℝ}
    (hγ₂ : |γ₂| ≤ 1) (hl₁ : |l₁| ≤ 1) (hl₂ : |l₂| ≤ 1)
    (hI₁ : Real.exp I₁ ≤ 16) (hI₂ : Real.exp I₂ ≤ 16) :
    |γ₁ * l₁ * Real.exp I₁ - γ₂ * l₂ * Real.exp I₂| ≤
      16 * |γ₁ - γ₂| + 16 * |l₁ - l₂| + 16 * |I₁ - I₂| := by
  have he : |Real.exp I₁| ≤ 16 := by rwa [abs_of_pos (Real.exp_pos _)]
  have ht := stab_triple_product_sub_le (a := γ₁) (f := Real.exp I₂) hγ₂ hl₁ hl₂ he
  have hd := stab_exp_sub_le_of_exp_le hI₁ hI₂
  nlinarith only [ht, hd]

end EmcsfAcExtension.Local
