module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Variable cubic kernels in the geometric source

The relative radius error is subtracted before the endpoint lower bound
is inserted. This avoids any minimum-radius dependence of the constant.
-/

public section

namespace EmcsfAcExtension.Local

/-- The outer cubic coefficient has absolute bound `512/L³` in the
fixed box, uniformly in the positive separation and endpoint radius. -/
theorem stab_geometric_cubic_coefficient_abs_le {a r L : ℝ}
    (hL : 0 < L) (hr : L / 4 ≤ r) (ha : |a| ≤ 8) :
    |a / r ^ 3| ≤ 512 / L ^ 3 := by
  have hr0 : 0 < r := (div_pos hL (by norm_num)).trans_le hr
  rw [abs_div, abs_of_pos (pow_pos hr0 3)]
  calc
    _ ≤ 8 / r ^ 3 := div_le_div_of_nonneg_right ha (pow_nonneg hr0.le 3)
    _ ≤ 8 / (L / 4) ^ 3 := div_le_div_of_nonneg_left (by norm_num)
      (by positivity) (pow_le_pow_left₀ (by positivity) hr 3)
    _ = _ := by field_simp; ring

/-- Subtraction of the outer geometric scalar primitive coefficient.
The literal coefficient `4096` is universal. Only the geometric box
radius lower bound and the relative radius difference occur, uniformly
as the common separation `L` tends to zero.
-/
theorem stab_geometric_cubic_coefficient_sub_le
    {a b r s L G U : ℝ} (hL : 0 < L) (hr : L / 4 ≤ r) (hs : L / 4 ≤ s)
    (hU : 0 ≤ U) (hrel : |r - s| / r ≤ G)
    (hab : |a - b| ≤ 40 * (G + U)) (hb : |b| ≤ 8) :
    |a / r ^ 3 - b / s ^ 3| ≤ 4096 * (G + U) / L ^ 3 := by
  have hr0 : 0 < r := (div_pos hL (by norm_num)).trans_le hr
  have hs0 : 0 < s := (div_pos hL (by norm_num)).trans_le hs
  have hG : 0 ≤ G := (div_nonneg (abs_nonneg _) hr0.le).trans hrel
  have hGU : 0 ≤ G + U := add_nonneg hG hU
  have hri : r⁻¹ ≤ 4 / L := by
    rw [inv_eq_one_div, div_le_div_iff₀ hr0 hL]
    linarith only [hr]
  have hsi : s⁻¹ ≤ 4 / L := by
    rw [inv_eq_one_div, div_le_div_iff₀ hs0 hL]
    linarith only [hs]
  have hdelta : |r⁻¹ - s⁻¹| ≤ 4 * (G + U) / L := by
    have heq : r⁻¹ - s⁻¹ = (s - r) / (r * s) := by field_simp
    rw [heq, abs_div, abs_sub_comm, abs_of_pos (mul_pos hr0 hs0)]
    calc
      _ ≤ (G * r) / (r * s) := div_le_div_of_nonneg_right
        ((div_le_iff₀ hr0).mp hrel) (mul_nonneg hr0.le hs0.le)
      _ = G * s⁻¹ := by field_simp
      _ ≤ (G + U) * (4 / L) := mul_le_mul
        (le_add_of_nonneg_right hU) hsi (inv_nonneg.mpr hs0.le) hGU
      _ = _ := by ring
  have hsum : r⁻¹ ^ 2 + r⁻¹ * s⁻¹ + s⁻¹ ^ 2 ≤ 3 * (4 / L) ^ 2 := by
    have hrr := pow_le_pow_left₀ (inv_nonneg.mpr hr0.le) hri 2
    have hss := pow_le_pow_left₀ (inv_nonneg.mpr hs0.le) hsi 2
    have hrs := mul_le_mul hri hsi (inv_nonneg.mpr hs0.le) (by positivity : 0 ≤ 4 / L)
    nlinarith only [hrr, hss, hrs]
  have hcube : r⁻¹ ^ 3 ≤ (4 / L) ^ 3 := pow_le_pow_left₀ (inv_nonneg.mpr hr0.le) hri 3
  have heq : a / r ^ 3 - b / s ^ 3 = (a - b) * r⁻¹ ^ 3 +
      b * (r⁻¹ - s⁻¹) * (r⁻¹ ^ 2 + r⁻¹ * s⁻¹ + s⁻¹ ^ 2) := by
    simp only [div_eq_mul_inv, inv_pow]
    ring
  calc
    _ ≤ |(a - b) * r⁻¹ ^ 3| +
        |b * (r⁻¹ - s⁻¹) * (r⁻¹ ^ 2 + r⁻¹ * s⁻¹ + s⁻¹ ^ 2)| := by
      rw [heq]
      exact abs_add_le _ _
    _ ≤ (40 * (G + U)) * (4 / L) ^ 3 +
        8 * (4 * (G + U) / L) * (3 * (4 / L) ^ 2) := by
      simp only [abs_mul, abs_of_nonneg (inv_nonneg.mpr hr0.le), abs_pow,
        abs_of_nonneg (show 0 ≤ r⁻¹ ^ 2 + r⁻¹ * s⁻¹ + s⁻¹ ^ 2 by positivity)]
      exact add_le_add (mul_le_mul hab hcube (pow_nonneg (inv_nonneg.mpr hr0.le) 3)
        (by positivity))
        (mul_le_mul (mul_le_mul hb hdelta (abs_nonneg _) (by norm_num)) hsum
          (by positivity) (by positivity))
    _ = _ := by field_simp; ring

end EmcsfAcExtension.Local
