module

public import EmcsfAcExtension.Local.Stability.DifferenceMomentsAlgebra
import Mathlib.Tactic.Ring

/-! # Algebra of the quadratic flux differences

The scalar-square difference and the moving radial weight are kept
separate. Both incoming and outgoing flux comparisons use this exact
subtraction, including the second solution's quadratic flux.
-/

public section

namespace EmcsfAcExtension.Local

/-- The quadratic flux difference retains the varying-weight term,
with exact universal coefficient `2` in the scalar difference term. -/
theorem stab_quadratic_flux_sub_le {a b ε : ℝ} {z w : ℂ}
    (ha : 0 ≤ a) (hz : ‖z‖ ≤ ε) (hw : ‖w‖ ≤ ε) :
    |a * ‖z‖ ^ 2 - b * ‖w‖ ^ 2| ≤
      2 * ε * (a * ‖z - w‖) + |a - b| * ‖w‖ ^ 2 := by
  have heq : a * ‖z‖ ^ 2 - b * ‖w‖ ^ 2 =
      a * (‖z‖ ^ 2 - ‖w‖ ^ 2) + (a - b) * ‖w‖ ^ 2 := by ring
  calc
    _ ≤ |a * (‖z‖ ^ 2 - ‖w‖ ^ 2)| + |(a - b) * ‖w‖ ^ 2| := by
      rw [heq]
      exact abs_add_le _ _
    _ = a * |‖z‖ ^ 2 - ‖w‖ ^ 2| + |a - b| * ‖w‖ ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg (sq_nonneg ‖w‖)]
    _ ≤ a * (2 * ε * ‖z - w‖) + |a - b| * ‖w‖ ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left (stab_norm_sq_sub_le hz hw) ha) le_rfl
    _ = _ := by ring

/-- A relative moving-weight bound gives the raw quadratic flux
comparison, with coefficients `2` and `20`, uniform in all values.
This helper assumes neither a closed radial nor a mass difference bound. -/
theorem stab_quadratic_flux_sub_le_of_weight {a b ε G : ℝ} {z w : ℂ}
    (ha : 0 ≤ a) (hz : ‖z‖ ≤ ε) (hw : ‖w‖ ≤ ε)
    (hweight : |a - b| ≤ 20 * G * a) :
    |a * ‖z‖ ^ 2 - b * ‖w‖ ^ 2| ≤
      2 * ε * (a * ‖z - w‖) + 20 * G * (a * ‖w‖ ^ 2) := by
  apply (stab_quadratic_flux_sub_le ha hz hw).trans
  calc
    _ ≤ 2 * ε * (a * ‖z - w‖) + (20 * G * a) * ‖w‖ ^ 2 :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hweight (sq_nonneg _))
    _ = _ := by ring

end EmcsfAcExtension.Local
