module

public import EmcsfAcExtension.Local.Defs.Setting
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Radial algebra in the incoming potential density

Charge, cubic inverse radius and expansion coefficients are subtracted
separately. No uniform field error is divided by a bare singular weight.
-/

public section

namespace EmcsfAcExtension.Local

/-- A product difference retains its second undifferenced factor.
The coefficient one is universal before all factors and norm bounds. -/
theorem stab_real_product_sub_le {a b x y : ℝ} :
    |a * x - b * y| ≤ |a| * |x - y| + |a - b| * |y| := by
  have heq : a * x - b * y = a * (x - y) + (a - b) * y := by ring
  rw [heq]
  exact (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_mul])

/-- Normalizing charge by each own radius cubed costs the relative
radius error with universal coefficient `21`. Positive radii and the
fixed comparison `s≤4r` are explicit; no radius cutoff enters. -/
theorem stab_cubic_charge_sub_le {q₁ q₂ r s G : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hc : s ≤ 4 * r) (hrel : |r - s| / r ≤ G) :
    |q₁ / r ^ 3 - q₂ / s ^ 3| ≤ |q₁ - q₂| / r ^ 3 + 21 * (|q₂| / s ^ 3) * G := by
  have hG : 0 ≤ G := (div_nonneg (abs_nonneg _) hr.le).trans hrel
  have hsq : s ^ 2 ≤ 16 * r ^ 2 := by
    have hh := pow_le_pow_left₀ hs.le hc 2
    nlinarith only [hh]
  have hsr : s * r ≤ 4 * r ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hc hr.le
    nlinarith only [hh]
  have hsum : (s ^ 2 + s * r + r ^ 2) / r ^ 2 ≤ 21 := by
    rw [div_le_iff₀ (sq_pos_of_pos hr)]
    linarith only [hsq, hsr]
  have hsum0 : 0 ≤ s ^ 2 + s * r + r ^ 2 := by positivity
  have heq : q₁ / r ^ 3 - q₂ / s ^ 3 = (q₁ - q₂) / r ^ 3 +
      (q₂ / s ^ 3) * ((s - r) / r) * ((s ^ 2 + s * r + r ^ 2) / r ^ 2) := by
    field_simp
    ring
  have hterm : |(q₂ / s ^ 3) * ((s - r) / r) * ((s ^ 2 + s * r + r ^ 2) / r ^ 2)| ≤
      21 * (|q₂| / s ^ 3) * G := by
    rw [abs_mul, abs_mul, abs_div, abs_div, abs_div, abs_of_pos hr,
      abs_of_pos (pow_pos hs 3), abs_of_nonneg hsum0, abs_of_pos (sq_pos_of_pos hr), abs_sub_comm]
    have hh := mul_le_mul hrel hsum
      (div_nonneg hsum0 (sq_nonneg r)) hG
    have hm := mul_le_mul_of_nonneg_left hh (div_nonneg (abs_nonneg q₂) (pow_nonneg hs.le 3))
    nlinarith only [hm]
  calc
    _ ≤ |(q₁ - q₂) / r ^ 3| +
        |(q₂ / s ^ 3) * ((s - r) / r) * ((s ^ 2 + s * r + r ^ 2) / r ^ 2)| := by
      rw [heq]
      exact abs_add_le _ _
    _ ≤ _ := by
      rw [abs_div, abs_of_pos (pow_pos hr 3)]
      exact add_le_add le_rfl hterm

/-- The radial charge source retains the cubic Hardy difference and
an undifferenced cubic charge norm. Coefficients `16,432` are universal
for the fixed comparison and coefficient bounds. -/
theorem stab_cubic_charge_source_sub_le {a b q₁ q₂ r s G U : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hc : s ≤ 4 * r) (_hG : 0 ≤ G) (hU : 0 ≤ U)
    (hrel : |r - s| / r ≤ G) (ha : |a| ≤ 16) (hab : |a - b| ≤ 96 * (G + U)) :
    |a * (q₁ / r ^ 3) - b * (q₂ / s ^ 3)| ≤
      16 * (|q₁ - q₂| / r ^ 3) + 432 * (G + U) * (|q₂| / s ^ 3) := by
  have hq := stab_cubic_charge_sub_le (q₁ := q₁) (q₂ := q₂) hr hs hc hrel
  apply stab_real_product_sub_le.trans
  rw [abs_div, abs_of_pos (pow_pos hs 3)]
  apply (add_le_add (mul_le_mul ha hq (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 16))
    (mul_le_mul_of_nonneg_right hab (div_nonneg (abs_nonneg _) (pow_nonneg hs.le 3)))).trans
  have hnonneg : 0 ≤ U * (|q₂| / s ^ 3) := by positivity
  nlinarith only [hnonneg]

/-- An inverse-radius coefficient difference is controlled by its own
coefficient error and the relative radius error. The coefficients are
explicit inputs, uniform in the two positive radii. -/
theorem stab_coefficient_over_radius_sub_le {a b r s K D G : ℝ}
    (hr : 0 < r) (hs : 0 < s) (ha : |a| ≤ K) (hab : |a - b| ≤ D)
    (hrel : |r - s| / r ≤ G) :
    |a / r - b / s| ≤ (D + K * G) / s := by
  have hK : 0 ≤ K := (abs_nonneg _).trans ha
  have heq : a / r - b / s = (a * ((s - r) / r) + (a - b)) / s := by
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hs]
  apply div_le_div_of_nonneg_right _ hs.le
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_div, abs_of_pos hr, abs_sub_comm]
  exact (add_le_add (mul_le_mul ha hrel (div_nonneg (abs_nonneg _) hr.le) hK) hab).trans_eq
      (by ring)

/-- Multiplying the geometric potential coefficient by one expansion
has bounds `8` and `48(G+U)`. The constants are universal for the fixed
box and independent of fields, radii, data and derivative bounds. -/
theorem stab_expansion_potential_coefficient_bounds
    {a b B₁ B₂ G U : ℝ} (ha : |a| ≤ 1) (hab : |a - b| ≤ G)
    (hB₁ : |B₁| ≤ 8) (hB₂ : |B₂| ≤ 8) (hBB : |B₁ - B₂| ≤ 40 * (G + U))
    (hG : 0 ≤ G) (hU : 0 ≤ U) :
    |a * B₁| ≤ 8 ∧ |a * B₁ - b * B₂| ≤ 48 * (G + U) := by
  constructor
  · rw [abs_mul]
    exact (mul_le_mul ha hB₁ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (by ring)
  · apply stab_real_product_sub_le.trans
    apply (add_le_add (mul_le_mul ha hBB (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))
      (mul_le_mul hab hB₂ (abs_nonneg _) hG)).trans
    linarith only [hU]

/-- A three-term source subtraction costs the sum of its three
individual differences, with universal coefficient one. -/
theorem stab_real_three_source_sub_le (a b c x y z : ℝ) :
    |(a - b + c) - (x - y + z)| ≤ |a - x| + |b - y| + |c - z| := by
  have heq : (a - b + c) - (x - y + z) = ((a - x) - (b - y)) + (c - z) := by ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)

end EmcsfAcExtension.Local
