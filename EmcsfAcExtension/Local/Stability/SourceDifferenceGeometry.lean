module

public import Mathlib

/-! # Differences of the radius-dependent scalar primitive coefficient

All bounds retain the inverse-cube coordinate scale. No positive lower
radius is imposed: the lower bound is the fixed box multiple of `v - u`.
-/

public section

namespace EmcsfAcExtension.Local.Stab

private theorem abs_cube_sub_le {a b L : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haL : a ≤ L) (hbL : b ≤ L) : |a ^ 3 - b ^ 3| ≤ 3 * L ^ 2 * |a - b| := by
  have hL : 0 ≤ L := ha.trans haL
  have hs : 0 ≤ a ^ 2 + a * b + b ^ 2 := by positivity
  have hsum : a ^ 2 + a * b + b ^ 2 ≤ 3 * L ^ 2 := by
    have h₁ := pow_le_pow_left₀ ha haL 2
    have h₂ := mul_le_mul haL hbL hb hL
    have h₃ := pow_le_pow_left₀ hb hbL 2
    nlinarith only [h₁, h₂, h₃]
  calc
    _ = |a - b| * (a ^ 2 + a * b + b ^ 2) := by
      rw [show a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2) by ring,
        abs_mul, abs_of_nonneg hs]
    _ ≤ |a - b| * (3 * L ^ 2) := mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ = _ := by ring

/-- The inverse-cube radius difference has universal coefficient `768`.
Both radii may approach zero together with the coordinate gap `d`.
The parameters and their scopes remain explicit. -/
theorem inverse_cube_difference_le {d r₁ r₂ G : ℝ} (hd : 0 < d)
    (hr₁ : d / 4 ≤ r₁) (hr₂ : d / 4 ≤ r₂) (hG : 0 ≤ G)
    (hδr : |r₁ - r₂| ≤ G * d) :
    |1 / r₁ ^ 3 - 1 / r₂ ^ 3| ≤ 768 * G / d ^ 3 := by
  have hr₁0 : 0 < r₁ := (div_pos hd (by norm_num)).trans_le hr₁
  have hr₂0 : 0 < r₂ := (div_pos hd (by norm_num)).trans_le hr₂
  have hr₁ne := hr₁0.ne'
  have hr₂ne := hr₂0.ne'
  have hdne := hd.ne'
  have hi₁ : 1 / r₁ ≤ 4 / d := by
    have := one_div_le_one_div_of_le (div_pos hd (by norm_num)) hr₁
    convert this using 1; field_simp [hdne]
  have hi₂ : 1 / r₂ ≤ 4 / d := by
    have := one_div_le_one_div_of_le (div_pos hd (by norm_num)) hr₂
    convert this using 1; field_simp [hdne]
  have hidiff : |1 / r₁ - 1 / r₂| ≤ 16 * G / d := by
    calc
      _ = |r₁ - r₂| * (1 / r₁) * (1 / r₂) := by
        rw [show 1 / r₁ - 1 / r₂ = -(r₁ - r₂) * (1 / r₁) * (1 / r₂) by
          field_simp [hr₁ne, hr₂ne, hdne]
          ring]
        rw [abs_mul, abs_mul, abs_neg, abs_of_pos (one_div_pos.mpr hr₁0),
          abs_of_pos (one_div_pos.mpr hr₂0)]
      _ ≤ (G * d) * (4 / d) * (4 / d) := by gcongr
      _ = _ := by field_simp [hr₁ne, hr₂ne, hdne]; ring
  have hc := abs_cube_sub_le (one_div_nonneg.mpr hr₁0.le) (one_div_nonneg.mpr hr₂0.le) hi₁ hi₂
  calc
    _ = |(1 / r₁) ^ 3 - (1 / r₂) ^ 3| := by simp only [div_pow, one_pow]
    _ ≤ 3 * (4 / d) ^ 2 * |1 / r₁ - 1 / r₂| := hc
    _ ≤ 3 * (4 / d) ^ 2 * (16 * G / d) := by gcongr
    _ = _ := by field_simp [hr₁ne, hr₂ne, hdne]; ring

/-- Norm difference of the two expansion factors and scalar ratio.
The exact constants are `1` for the ratio difference and `2` for geometry,
uniformly in all real expansion and complex scalar factors. -/
theorem norm_expansion_scalar_product_sub_le {l₁ l₂ n₁ n₂ ε G E : ℝ}
    {x₁ x₂ : ℂ} (_hε : 0 ≤ ε) (hG : 0 ≤ G) (_hE : 0 ≤ E)
    (hl₁ : |l₁| ≤ 1) (hl₂ : |l₂| ≤ 1) (_hn₁ : |n₁| ≤ 1) (hn₂ : |n₂| ≤ 1)
    (hx₁ : ‖x₁‖ ≤ ε) (_hx₂ : ‖x₂‖ ≤ ε)
    (hδl : |l₁ - l₂| ≤ G) (hδn : |n₁ - n₂| ≤ G) (hδx : ‖x₁ - x₂‖ ≤ E) :
    ‖(n₁ : ℂ) * l₁ * x₁ - (n₂ : ℂ) * l₂ * x₂‖ ≤ E + 2 * ε * G := by
  have heq : (n₁ : ℂ) * l₁ * x₁ - (n₂ : ℂ) * l₂ * x₂ =
      ((n₁ - n₂ : ℝ) : ℂ) * l₁ * x₁ +
        (n₂ : ℂ) * ((l₁ - l₂ : ℝ) : ℂ) * x₁ + (n₂ : ℂ) * l₂ * (x₁ - x₂) := by
    push_cast
    ring
  rw [heq]
  calc
    _ ≤ (‖((n₁ - n₂ : ℝ) : ℂ) * l₁ * x₁‖ +
        ‖(n₂ : ℂ) * ((l₁ - l₂ : ℝ) : ℂ) * x₁‖) +
        ‖(n₂ : ℂ) * l₂ * (x₁ - x₂)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (G * 1 * ε + 1 * G * ε) + 1 * 1 * E := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      gcongr
    _ = _ := by ring

/-- Difference of the full scalar primitive coefficients.
The fixed numerical coefficient `1024` is universal; the gap is allowed
to tend to zero, and no derivative or coordinate map is differentiated. -/
theorem scalar_primitive_coefficient_difference_le {d r₁ r₂ l₁ l₂ n₁ n₂ ε G E : ℝ}
    {x₁ x₂ : ℂ} (hd : 0 < d) (hr₁ : d / 4 ≤ r₁) (hr₂ : d / 4 ≤ r₂)
    (hε : 0 ≤ ε) (hG : 0 ≤ G) (hE : 0 ≤ E)
    (hl₁ : |l₁| ≤ 1) (hl₂ : |l₂| ≤ 1) (hn₁ : |n₁| ≤ 1) (hn₂ : |n₂| ≤ 1)
    (hx₁ : ‖x₁‖ ≤ ε) (hx₂ : ‖x₂‖ ≤ ε)
    (hδl : |l₁ - l₂| ≤ G) (hδn : |n₁ - n₂| ≤ G) (hδx : ‖x₁ - x₂‖ ≤ E)
    (hδr : |r₁ - r₂| ≤ G * d) :
    ‖(n₁ : ℂ) * l₁ * x₁ / (r₁ : ℂ) ^ 3 -
      (n₂ : ℂ) * l₂ * x₂ / (r₂ : ℂ) ^ 3‖ ≤ 1024 * (E + ε * G) / d ^ 3 := by
  have hr₁0 : 0 < r₁ := (div_pos hd (by norm_num)).trans_le hr₁
  have hr₂0 : 0 < r₂ := (div_pos hd (by norm_num)).trans_le hr₂
  have hi₁ : 1 / r₁ ≤ 4 / d := by
    have := one_div_le_one_div_of_le (div_pos hd (by norm_num)) hr₁
    convert this using 1; field_simp [hd.ne']
  have hi₃ : 1 / r₁ ^ 3 ≤ 64 / d ^ 3 := by
    have := pow_le_pow_left₀ (one_div_nonneg.mpr hr₁0.le) hi₁ 3
    norm_num only [div_pow, one_pow, show (4 : ℝ) ^ 3 = 64 by norm_num] at this
    exact this
  have hprod := norm_expansion_scalar_product_sub_le hε hG hE hl₁ hl₂ hn₁ hn₂
    hx₁ hx₂ hδl hδn hδx
  have hprod₂ : ‖(n₂ : ℂ) * l₂ * x₂‖ ≤ ε := by
    calc
      _ = |n₂| * |l₂| * ‖x₂‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 1 * 1 * ε := by gcongr
      _ = _ := by ring
  have heq : (n₁ : ℂ) * l₁ * x₁ / (r₁ : ℂ) ^ 3 -
      (n₂ : ℂ) * l₂ * x₂ / (r₂ : ℂ) ^ 3 =
    ((n₁ : ℂ) * l₁ * x₁ - (n₂ : ℂ) * l₂ * x₂) * ((1 / r₁ ^ 3 : ℝ) : ℂ) +
      ((n₂ : ℂ) * l₂ * x₂) * ((1 / r₁ ^ 3 - 1 / r₂ ^ 3 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sub, div_eq_mul_inv, one_mul,
      Complex.ofReal_pow, Complex.ofReal_inv]
    ring
  have hinv := inverse_cube_difference_le hd hr₁ hr₂ hG hδr
  have hprod₂' : |n₂| * |l₂| * ‖x₂‖ ≤ ε := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using hprod₂
  rw [heq]
  calc
    _ ≤ ‖((n₁ : ℂ) * l₁ * x₁ - (n₂ : ℂ) * l₂ * x₂) * ((1 / r₁ ^ 3 : ℝ) : ℂ)‖ +
        ‖((n₂ : ℂ) * l₂ * x₂) * ((1 / r₁ ^ 3 - 1 / r₂ ^ 3 : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ (E + 2 * ε * G) * (64 / d ^ 3) + ε * (768 * G / d ^ 3) := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (one_div_pos.mpr (pow_pos hr₁0 3))]
      gcongr
    _ = (64 * E + 896 * ε * G) / d ^ 3 := by ring
    _ ≤ _ := by
      apply (div_le_div_iff_of_pos_right (pow_pos hd 3)).2
      have hεG : 0 ≤ ε * G := mul_nonneg hε hG
      nlinarith only [hE, hεG]

end EmcsfAcExtension.Local.Stab
