module

public import EmcsfAcExtension.Local.Construction.PicardScalarEstimates

/-! # Polynomial difference estimates for normalized radial profiles

These elementary estimates retain explicit bounds for products, reciprocals,
and squared norms. Their constants are independent of the wedge and candidates.
-/

public section

namespace EmcsfAcExtension.Local

/-- The product difference rule with universal constant one. -/
theorem picard_mul_sub_le_aux {E : Type*} [NormedRing E] (x y z w : E) :
    ‖x * z - y * w‖ ≤ ‖x‖ * ‖z - w‖ + ‖x - y‖ * ‖w‖ := by
  have he : x * z - y * w = x * (z - w) + (x - y) * w := by
    rw [mul_sub, sub_mul]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))

/-- Squared norms have Lipschitz constant `2*B` on a norm ball of radius `B`,
uniformly in the normed group and both elements. -/
theorem picard_norm_sq_sub_le_aux {E : Type*} [SeminormedAddCommGroup E]
    (B : ℝ) (x y : E) (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B) :
    |‖x‖ ^ 2 - ‖y‖ ^ 2| ≤ 2 * B * ‖x - y‖ := by
  rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  calc
    _ ≤ (2 * B) * ‖x - y‖ := mul_le_mul
      (by linarith only [hx, hy]) (abs_norm_sub_norm_le x y)
      (abs_nonneg _) (by have hB := (norm_nonneg x).trans hx; positivity)
    _ = _ := rfl

/-- Reciprocals have Lipschitz constant `ell⁻¹^2` above the positive lower
bound `ell`, uniformly in the two denominators. -/
theorem picard_inv_sub_le_aux {ell R S : ℝ} (he : 0 < ell)
    (hR : ell ≤ R) (hS : ell ≤ S) :
    |R⁻¹ - S⁻¹| ≤ ell⁻¹ ^ 2 * |R - S| := by
  have hRp := he.trans_le hR
  have hSp := he.trans_le hS
  have hRi := (inv_le_inv₀ hRp he).mpr hR
  have hSi := (inv_le_inv₀ hSp he).mpr hS
  have heq : R⁻¹ - S⁻¹ = (S - R) * (R⁻¹ * S⁻¹) := by field_simp
  rw [heq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ R⁻¹ * S⁻¹), abs_sub_comm S R]
  calc
    _ ≤ |R - S| * (ell⁻¹ * ell⁻¹) := mul_le_mul_of_nonneg_left
      (mul_le_mul hRi hSi (by positivity) (by positivity)) (abs_nonneg _)
    _ = _ := by ring

/-- Division by a uniformly positive radial average has the displayed
constant depending only on `ell,B,C`, uniformly in the elements and distance
parameter `Δ`. -/
theorem picard_div_sub_le_aux (ell B C Δ x y R S : ℝ)
    (he : 0 < ell) (_hB : 0 ≤ B) (_hC : 0 ≤ C) (hΔ : 0 ≤ Δ)
    (hR : ell ≤ R) (hS : ell ≤ S) (hy : |y| ≤ B)
    (hxy : |x - y| ≤ C * Δ) (hRS : |R - S| ≤ Δ) :
    |x / R - y / S| ≤ (ell⁻¹ * C + B * ell⁻¹ ^ 2) * Δ := by
  have hRi : |R⁻¹| ≤ ell⁻¹ := by
    rw [abs_of_pos (inv_pos.mpr (he.trans_le hR))]
    exact (inv_le_inv₀ (he.trans_le hR) he).mpr hR
  have hI : |R⁻¹ - S⁻¹| ≤ ell⁻¹ ^ 2 * Δ :=
    (picard_inv_sub_le_aux he hR hS).trans
      (mul_le_mul_of_nonneg_left hRS (sq_nonneg _))
  have h := picard_mul_sub_le_aux R⁻¹ S⁻¹ x y
  simp only [Real.norm_eq_abs] at h
  calc
    _ = |R⁻¹ * x - S⁻¹ * y| := by simp only [div_eq_mul_inv]; congr 1; ring
    _ ≤ ell⁻¹ * (C * Δ) + (ell⁻¹ ^ 2 * Δ) * B := h.trans (add_le_add
      (mul_le_mul hRi hxy (abs_nonneg _) (by positivity))
      (mul_le_mul hI hy (abs_nonneg _) (by positivity)))
    _ = _ := by ring

end EmcsfAcExtension.Local
