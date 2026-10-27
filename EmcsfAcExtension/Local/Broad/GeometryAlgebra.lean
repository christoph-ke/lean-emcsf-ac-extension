module

public import Mathlib

/-! # Logarithmic and radial-weight comparison algebra

All coefficients are displayed explicitly. These helpers are independent
of the coupling, data size, triangle and characteristic variation.
-/

public section

open Set

namespace EmcsfAcExtension.Local.Broad

/-- Recover an expansion difference from its optical quotient and gap
difference. The explicit coefficient `B` bounds the optical quotient;
the second gap lies in `[0,1]`. All other coefficients are exactly one. -/
theorem expansion_difference_of_optical_bounds {l₁ l₂ g₁ g₂ B X U : ℝ}
    (hg₁ : 0 < g₁) (hg₂ : 0 < g₂) (hg₂1 : g₂ ≤ 1)
    (hl₁ : 0 ≤ l₁) (hB : 0 ≤ B) (hU : 0 ≤ U)
    (hopt₁ : l₁ / g₁ ≤ B) (hδopt : |l₁ / g₁ - l₂ / g₂| ≤ U)
    (hδg : |g₁ - g₂| ≤ X) : |l₁ - l₂| ≤ U + B * X := by
  have heq₁ : l₁ = (l₁ / g₁) * g₁ := by field_simp
  have heq₂ : l₂ = (l₂ / g₂) * g₂ := by field_simp
  calc
    |l₁ - l₂| = |(l₁ / g₁) * g₁ - (l₂ / g₂) * g₂| := congrArg abs (by rw [← heq₁, ← heq₂])
    _ ≤ |l₁ / g₁| * |g₁ - g₂| + |l₁ / g₁ - l₂ / g₂| * |g₂| := by
      calc
        _ = |(l₁ / g₁) * (g₁ - g₂) + (l₁ / g₁ - l₂ / g₂) * g₂| := by congr 1; ring
        _ ≤ _ := (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_mul])
    _ ≤ B * X + U * 1 := by
      rw [abs_of_nonneg (div_nonneg hl₁ hg₁.le), abs_of_pos hg₂]
      exact add_le_add (mul_le_mul hopt₁ hδg (abs_nonneg _) hB)
        (mul_le_mul hδopt hg₂1 hg₂.le hU)
    _ = _ := by ring

/-- On the positive interval bounded above by `C`, the inverse logarithm
has Lipschitz coefficient exactly `C`. The bound is uniform in both field
values and independent of a positive lower bound. -/
theorem abs_sub_le_mul_abs_log_sub {x y C : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxC : x ≤ C) (hyC : y ≤ C) :
    |x - y| ≤ C * |Real.log x - Real.log y| := by
  have hC : 0 < C := hx.trans_le hxC
  have hlogx : Real.log x ≤ Real.log C := Real.log_le_log hx hxC
  have hlogy : Real.log y ≤ Real.log C := Real.log_le_log hy hyC
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Iic (Real.log C)) (f := Real.exp) (f' := Real.exp)
    (fun z _ => (Real.hasDerivAt_exp z).hasDerivWithinAt)
    (fun z hz => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos z)]
      exact (Real.exp_le_exp.mpr hz).trans_eq (Real.exp_log hC))
    (convex_Iic _) hlogy hlogx
  simpa only [Real.exp_log hx, Real.exp_log hy, Real.norm_eq_abs] using hb

/-- The logarithm has Lipschitz coefficient `1/c` on the positive ray
bounded below by `c`. This exact coefficient is uniform in the two values. -/
theorem abs_log_sub_le_inv_mul_abs_sub {c x y : ℝ} (hc : 0 < c)
    (hcx : c ≤ x) (hcy : c ≤ y) :
    |Real.log x - Real.log y| ≤ c⁻¹ * |x - y| := by
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Ici c) (f := Real.log) (f' := fun z => z⁻¹)
    (fun z hz => (Real.hasDerivAt_log (hc.trans_le hz).ne').hasDerivWithinAt)
    (fun z hz => by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hc.trans_le hz))]
      exact inv_le_inv₀ (hc.trans_le hz) hc |>.mpr hz)
    (convex_Ici _) hcy hcx
  simpa only [Real.norm_eq_abs] using hb

/-- Comparing two radial weights retains both the expansion difference
and the relative radius difference. The coefficient `(1 + C*k)/c`
depends only on the weight lower bound, upper bound and radius comparison
factor, uniformly in the field values and geometric error. -/
theorem radial_weight_difference_of_bounds {w₁ w₂ r₁ r₂ c C k G : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (hk : 0 ≤ k) (hG : 0 ≤ G)
    (hw₁ : c ≤ w₁) (hw₂ : 0 ≤ w₂) (hw₂C : w₂ ≤ C)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hrr : r₁ ≤ k * r₂)
    (hδw : |w₁ - w₂| ≤ G) (hδr : |r₁ - r₂| ≤ G * r₁) :
    |w₁ / r₁ - w₂ / r₂| ≤ ((1 + C * k) / c) * G * (w₁ / r₁) := by
  have heq : w₁ / r₁ - w₂ / r₂ =
      ((w₁ - w₂) + w₂ * (r₂ - r₁) / r₂) / r₁ := by
    field_simp [hr₁.ne', hr₂.ne']
    ring
  have hterm : |w₂ * (r₂ - r₁) / r₂| ≤ C * G * k := by
    rw [abs_div, abs_mul, abs_of_nonneg hw₂, abs_of_pos hr₂, abs_sub_comm]
    have hrat : r₁ / r₂ ≤ k := (div_le_iff₀ hr₂).mpr hrr
    calc
      w₂ * |r₁ - r₂| / r₂ ≤ C * (G * r₁) / r₂ := by gcongr
      _ = C * G * (r₁ / r₂) := by ring
      _ ≤ C * G * k := by gcongr
  have hscale : 1 ≤ w₁ / c := (le_div_iff₀ hc).mpr (by simpa only [one_mul] using hw₁)
  have hpos : 0 ≤ G + C * G * k := by positivity
  have hmul : G + C * G * k ≤ (G + C * G * k) * (w₁ / c) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hscale hpos
  rw [heq, abs_div, abs_of_pos hr₁]
  calc
    _ ≤ (G + C * G * k) / r₁ := div_le_div_of_nonneg_right
      ((abs_add_le _ _).trans (add_le_add hδw hterm)) hr₁.le
    _ ≤ ((G + C * G * k) * (w₁ / c)) / r₁ := div_le_div_of_nonneg_right hmul hr₁.le
    _ = _ := by ring

end EmcsfAcExtension.Local.Broad
