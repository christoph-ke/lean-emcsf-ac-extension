module

public import EmcsfAcExtension.Local.Stability.MomentsSections

/-! # Radius powers and scalar-source coefficients

The inequalities retain `r^(1-p)` until the ordered separation factor has
been extracted. The only numerical geometric loss is the fixed box factor
`4³ = 64`; it is independent of the length scale and exponent.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The radial moment keeps the vanishing factor when multiplied by its
primitive radius. The coefficient is exactly one, uniformly for `0 ≤ p ≤ 1`.
All radii and separation bounds are explicit. -/
theorem stab_radius_power_product_le {r s L a p : ℝ}
    (hr : 0 < r) (hrL : r ≤ L) (hs : 0 ≤ s) (hsa : s ≤ a)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    r * (s / r) ^ p ≤ L ^ (1 - p) * a ^ p := by
  have heq : r * (s / r) ^ p = r ^ (1 - p) * s ^ p := by
    rw [Real.div_rpow hs hr.le, Real.rpow_sub hr 1 p, Real.rpow_one]
    ring
  rw [heq]
  exact mul_le_mul
    (Real.rpow_le_rpow hr.le hrL (sub_nonneg.mpr hp1))
    (Real.rpow_le_rpow hs hsa hp0) (Real.rpow_nonneg hs p)
    (Real.rpow_nonneg (hr.le.trans hrL) (1 - p))

/-- Exact power arithmetic in the scalar-source coefficient.
The constants `64`, `4`, and `256` are universal and the length power is
`-2-p`, as required by scaling. -/
theorem stab_ordered_coefficient_eq {L ε p : ℝ} (hL : 0 < L) :
    (64 * ε / L ^ 3) * 4 * L ^ (1 - p) = 256 * ε * L ^ (-p - 2) := by
  have hp : L ^ (1 - p) / L ^ (3 : ℝ) = L ^ (-p - 2) := by
    rw [← Real.rpow_sub hL]
    congr 1
    ring
  norm_num at hp
  calc
    _ = 256 * ε * (L ^ (1 - p) / L ^ 3) := by ring
    _ = _ := by rw [hp]

/-- The scalar curvature primitive has coefficients at most `64 ε/(v-u)³`
in either transport direction. The constant is universal, independently of
`T,e,M,A`, the fields, and all derivative suprema. -/
theorem stab_scalar_primitive_coefficients_le
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ‖((S.nu u v : ℂ) * S.theta u v / (S.r u v : ℂ) ^ 2) * (S.r u v : ℂ)⁻¹‖ ≤
        64 * ε / (v - u) ^ 3 ∧
    ‖((S.lam u v : ℂ) * S.xi u v / (S.r u v : ℂ) ^ 2) * (S.r u v : ℂ)⁻¹‖ ≤
        64 * ε / (v - u) ^ 3 := by
  have hpt : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hr := hset.c1.r_pos (u, v) hpt huv
  have hl := hset.c1.lam_pos (u, v) hpt
  have hn := hset.c1.nu_neg (u, v) hpt
  have hb := hset.box.2 (u, v) hpt
  have hx : ‖S.theta u v / (S.lam u v : ℂ)‖ ≤ ε :=
    (le_add_of_nonneg_right (norm_nonneg (S.xi u v / (S.nu u v : ℂ)))).trans
      hb.2.2.2.2.2.1
  have hy : ‖S.xi u v / (S.nu u v : ℂ)‖ ≤ ε :=
    (le_add_of_nonneg_left (norm_nonneg (S.theta u v / (S.lam u v : ℂ)))).trans
      hb.2.2.2.2.2.1
  have hε : 0 ≤ ε := (norm_nonneg _).trans hx
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl] at hx
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hn] at hy
  have hθ : ‖S.theta u v‖ ≤ ε :=
    ((div_le_iff₀ hl).1 hx).trans ((mul_le_mul_of_nonneg_left hb.2.1 hε).trans_eq (mul_one _))
  have hξ : ‖S.xi u v‖ ≤ ε :=
    ((div_le_iff₀ (neg_pos.mpr hn)).1 hy).trans
      ((mul_le_mul_of_nonneg_left hb.2.2.2.1 hε).trans_eq (mul_one _))
  have heq (a : ℝ) (z : ℂ) :
      ‖((a : ℂ) * z / (S.r u v : ℂ) ^ 2) * (S.r u v : ℂ)⁻¹‖ =
        |a| * ‖z‖ / S.r u v ^ 3 := by
    simp only [norm_mul, norm_div, norm_pow, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr]
    field_simp
  have hr3 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (v - u) / 4)
    (stab_radius_bounds hset hu huv.le hvT).1 3
  have htail : ε / S.r u v ^ 3 ≤ 64 * ε / (v - u) ^ 3 := by
    calc
      _ ≤ ε / ((v - u) / 4) ^ 3 := div_le_div_of_nonneg_left hε
        (by positivity) hr3
      _ = _ := by
        field_simp
        ring
  constructor
  · rw [heq, abs_of_neg hn]
    apply le_trans _ htail
    exact div_le_div_of_nonneg_right
      ((mul_le_mul hb.2.2.2.1 hθ (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
      (pow_nonneg hr.le 3)
  · rw [heq, abs_of_pos hl]
    apply le_trans _ htail
    exact div_le_div_of_nonneg_right
      ((mul_le_mul hb.2.1 hξ (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
      (pow_nonneg hr.le 3)

end EmcsfAcExtension.Local
