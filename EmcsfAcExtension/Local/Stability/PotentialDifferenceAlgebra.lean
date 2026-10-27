module

public import EmcsfAcExtension.Local.Stability.GeometryDifferenceOpticalComparison
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Algebra of the potential constraint difference

The coefficient, inverse radius and charge are subtracted separately.
All constants below are literal coefficients for the fixed stability box.
-/

public section

namespace EmcsfAcExtension.Local

/-- The coefficient `2νλ/(1-μ)` has absolute value at most `8`,
universally on the literal fixed box. -/
theorem stab_potential_coefficient_abs_le {ν l μ : ℝ}
    (hν : |ν| ≤ 1) (hl : |l| ≤ 1) (hgap : 1 / 4 ≤ 1 - μ) :
    |2 * ν * l / (1 - μ)| ≤ 8 := by
  have hg : 0 < 1 - μ := lt_of_lt_of_le (by norm_num) hgap
  have hp : |ν| * |l| ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hν hl (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  rw [abs_div, abs_of_pos hg]
  simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [div_le_iff₀ hg]
  nlinarith only [hp, hgap]

/-- The potential coefficient difference is at most `40(G+U)`,
uniformly in both coefficients and the mass gaps. -/
theorem stab_potential_coefficient_sub_le {ν₁ ν₂ l₁ l₂ μ₁ μ₂ G U : ℝ}
    (hl₁ : |l₁| ≤ 1) (hl₂ : |l₂| ≤ 1) (hν₂ : |ν₂| ≤ 1)
    (hg₁ : 1 / 4 ≤ 1 - μ₁) (hg₂ : 1 / 4 ≤ 1 - μ₂)
    (hgeom : |ν₁ - ν₂| + |l₁ - l₂| ≤ G) (hmu : |μ₁ - μ₂| ≤ U) :
    |2 * ν₁ * l₁ / (1 - μ₁) - 2 * ν₂ * l₂ / (1 - μ₂)| ≤ 40 * (G + U) := by
  have hG : 0 ≤ G := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans hgeom
  have hU : 0 ≤ U := (abs_nonneg _).trans hmu
  have hprod₂ : |ν₂ * l₂| ≤ 1 := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul hν₂ hl₂ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hprod : |ν₁ * l₁ - ν₂ * l₂| ≤ G := by
    have heq : ν₁ * l₁ - ν₂ * l₂ = (ν₁ - ν₂) * l₁ + ν₂ * (l₁ - l₂) := by ring
    calc
      _ ≤ |(ν₁ - ν₂) * l₁| + |ν₂ * (l₁ - l₂)| := by rw [heq]; exact abs_add_le _ _
      _ = |ν₁ - ν₂| * |l₁| + |ν₂| * |l₁ - l₂| := by rw [abs_mul, abs_mul]
      _ ≤ |ν₁ - ν₂| + |l₁ - l₂| := add_le_add
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hl₁ (abs_nonneg _))
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hν₂ (abs_nonneg _))
      _ ≤ G := hgeom
  have hq := stab_optical_quotient_sub_le (n₁ := ν₁ * l₁) hg₁ hg₂ hprod₂
  have hgap : |(1 - μ₁) - (1 - μ₂)| = |μ₁ - μ₂| := by
    rw [show (1 - μ₁) - (1 - μ₂) = -(μ₁ - μ₂) by ring, abs_neg]
  rw [hgap] at hq
  have heq : 2 * ν₁ * l₁ / (1 - μ₁) - 2 * ν₂ * l₂ / (1 - μ₂) =
      2 * (ν₁ * l₁ / (1 - μ₁) - ν₂ * l₂ / (1 - μ₂)) := by ring
  rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith only [hq, hprod, hmu, hG, hU]

/-- Comparing normalized charges retains the inverse-radius error
with universal coefficient `5`, independently of either positive radius. -/
theorem stab_normalized_charge_sub_le {q₁ q₂ r s G : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hcompare : s ≤ 4 * r) (hG : |r - s| / r ≤ G) :
    |q₁ / r ^ 2 - q₂ / s ^ 2| ≤ |q₁ - q₂| / r ^ 2 + 5 * (|q₂| / s ^ 2) * G := by
  have hG0 : 0 ≤ G := (div_nonneg (abs_nonneg _) hr.le).trans hG
  have hsum : (s + r) / r ≤ 5 := by rw [div_le_iff₀ hr]; linarith only [hcompare]
  have heq : q₁ / r ^ 2 - q₂ / s ^ 2 = (q₁ - q₂) / r ^ 2 +
      (q₂ / s ^ 2) * ((s - r) / r) * ((s + r) / r) := by
    field_simp
    ring
  have hterm : |(q₂ / s ^ 2) * ((s - r) / r) * ((s + r) / r)| ≤
      5 * (|q₂| / s ^ 2) * G := by
    rw [abs_mul, abs_mul, abs_div, abs_div, abs_div, abs_of_pos hr,
      abs_of_pos (sq_pos_of_pos hs), abs_of_pos (add_pos hs hr), abs_sub_comm]
    have hh := mul_le_mul hG hsum (div_nonneg (le_of_lt (add_pos hs hr)) hr.le) hG0
    have hm := mul_le_mul_of_nonneg_left hh (div_nonneg (abs_nonneg q₂) (sq_nonneg s))
    nlinarith only [hm]
  calc
    _ ≤ |(q₁ - q₂) / r ^ 2| + |(q₂ / s ^ 2) * ((s - r) / r) * ((s + r) / r)| := by
      rw [heq]
      exact abs_add_le _ _
    _ ≤ |q₁ - q₂| / r ^ 2 + 5 * (|q₂| / s ^ 2) * G := by
      rw [abs_div, abs_of_pos (sq_pos_of_pos hr)]
      exact add_le_add le_rfl hterm

/-- The full potential density difference has the universal coefficient
`128`; charge and geometric/mass feedback remain explicit. -/
theorem stab_potential_density_sub_le {B₁ B₂ q₁ q₂ r s G U D K : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hcompare : s ≤ 4 * r)
    (hG : |r - s| / r ≤ G) (hU : 0 ≤ U) (hD : |q₁ - q₂| / r ^ 2 ≤ D)
    (hK : |q₂| / s ^ 2 ≤ K) (hB₁ : |B₁| ≤ 8) (hB : |B₁ - B₂| ≤ 40 * (G + U)) :
    |B₁ * (q₁ / r ^ 2) - B₂ * (q₂ / s ^ 2)| ≤ 128 * (D + K * (G + U)) := by
  have hG0 : 0 ≤ G := (div_nonneg (abs_nonneg _) hr.le).trans hG
  have hD0 : 0 ≤ D := (div_nonneg (abs_nonneg _) (sq_nonneg r)).trans hD
  have hK0 : 0 ≤ K := (div_nonneg (abs_nonneg _) (sq_nonneg s)).trans hK
  have hnorm := stab_normalized_charge_sub_le (q₁ := q₁) (q₂ := q₂) hr hs hcompare hG
  have hnorm' : |q₁ / r ^ 2 - q₂ / s ^ 2| ≤ D + 5 * K * G := by
    nlinarith only [hnorm, hD, mul_le_mul_of_nonneg_right hK hG0]
  have hq₂ : |q₂ / s ^ 2| ≤ K := by simpa only [abs_div, abs_of_pos (sq_pos_of_pos hs)] using hK
  have heq : B₁ * (q₁ / r ^ 2) - B₂ * (q₂ / s ^ 2) =
      B₁ * (q₁ / r ^ 2 - q₂ / s ^ 2) + (B₁ - B₂) * (q₂ / s ^ 2) := by ring
  calc
    _ ≤ |B₁ * (q₁ / r ^ 2 - q₂ / s ^ 2)| + |(B₁ - B₂) * (q₂ / s ^ 2)| := by
      rw [heq]
      exact abs_add_le _ _
    _ = |B₁| * |q₁ / r ^ 2 - q₂ / s ^ 2| + |B₁ - B₂| * |q₂ / s ^ 2| := by
      rw [abs_mul, abs_mul]
    _ ≤ 8 * (D + 5 * K * G) + (40 * (G + U)) * K := add_le_add
      (mul_le_mul hB₁ hnorm' (abs_nonneg _) (by norm_num))
      (mul_le_mul hB hq₂ (abs_nonneg _) (by positivity))
    _ ≤ _ := by
      nlinarith only [hD0, mul_nonneg hK0 hG0, mul_nonneg hK0 hU]

end EmcsfAcExtension.Local
