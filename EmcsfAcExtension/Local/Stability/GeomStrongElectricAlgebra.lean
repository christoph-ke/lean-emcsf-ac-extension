module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Basic.Real.Basic
import EmcsfAcExtension.Local.Stability.DifferenceMomentsAlgebra
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! # Algebra of the electric curvature primitive

The normalized charge, expansion, scalar derivative and scalar field
are subtracted before the quadratic radial vanishing is integrated.
-/

public section

namespace EmcsfAcExtension.Local

/-- A bounded real multiplier preserves a complex difference with
coefficient one; the multiplier error retains the second factor.
The displayed coefficients are universal.
-/
theorem stab_real_smul_difference_le {a b G : ℝ} {x y : ℂ}
    (ha : |a| ≤ 1) (hab : |a - b| ≤ G) :
    ‖(a : ℂ) * x - (b : ℂ) * y‖ ≤ ‖x - y‖ + G * ‖y‖ := by
  have hG : 0 ≤ G := (abs_nonneg _).trans hab
  have heq : (a : ℂ) * x - (b : ℂ) * y =
      (a : ℂ) * (x - y) + ((a - b : ℝ) : ℂ) * y := by push_cast; ring
  calc
    _ ≤ ‖(a : ℂ) * (x - y)‖ + ‖((a - b : ℝ) : ℂ) * y‖ := by
      rw [heq]
      exact norm_add_le _ _
    _ = |a| * ‖x - y‖ + |a - b| * ‖y‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 1 * ‖x - y‖ + G * ‖y‖ := add_le_add
      (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
      (mul_le_mul_of_nonneg_right hab (norm_nonneg _))
    _ = _ := by ring

private theorem triple_norm_difference_aux {x₁ x₂ y₁ y₂ z₁ z₂ : ℂ}
    {X Y Z : ℝ} (hx₂ : ‖x₂‖ ≤ X) (hy₁ : ‖y₁‖ ≤ Y) (hy₂ : ‖y₂‖ ≤ Y)
    (hz₁ : ‖z₁‖ ≤ Z) :
    ‖x₁ * y₁ * z₁ - x₂ * y₂ * z₂‖ ≤
      Y * Z * ‖x₁ - x₂‖ + X * Z * ‖y₁ - y₂‖ + X * Y * ‖z₁ - z₂‖ := by
  have hX : 0 ≤ X := (norm_nonneg _).trans hx₂
  have hY : 0 ≤ Y := (norm_nonneg _).trans hy₁
  have hZ : 0 ≤ Z := (norm_nonneg _).trans hz₁
  have heq : x₁ * y₁ * z₁ - x₂ * y₂ * z₂ =
      (x₁ - x₂) * y₁ * z₁ + x₂ * (y₁ - y₂) * z₁ + x₂ * y₂ * (z₁ - z₂) := by ring
  calc
    _ ≤ ‖(x₁ - x₂) * y₁ * z₁ + x₂ * (y₁ - y₂) * z₁‖ +
        ‖x₂ * y₂ * (z₁ - z₂)‖ := by rw [heq]; exact norm_add_le _ _
    _ ≤ ‖(x₁ - x₂) * y₁ * z₁‖ + ‖x₂ * (y₁ - y₂) * z₁‖ +
        ‖x₂ * y₂ * (z₁ - z₂)‖ := add_le_add (norm_add_le _ _) le_rfl
    _ = (‖y₁‖ * ‖z₁‖) * ‖x₁ - x₂‖ + (‖x₂‖ * ‖z₁‖) * ‖y₁ - y₂‖ +
        (‖x₂‖ * ‖y₂‖) * ‖z₁ - z₂‖ := by simp only [norm_mul]; ring
    _ ≤ _ := add_le_add (add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul hy₁ hz₁ (norm_nonneg _) hY) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (mul_le_mul hx₂ hz₁ (norm_nonneg _) hX) (norm_nonneg _)))
      (mul_le_mul_of_nonneg_right (mul_le_mul hx₂ hy₂ (norm_nonneg _) hX) (norm_nonneg _))

/-- The normalized electric integrand is bounded by `2 E² ε²`,
where `E=|e|M`. The literal coefficient is universal and retains all
coupling and background factors without division by a scalar field.
-/
theorem stab_electric_integrand_norm_le {e M ε l q : ℝ} {z p : ℂ}
    (hM : 0 ≤ M) (hε : 0 ≤ ε) (hl : |l| ≤ 1)
    (hq : |q| ≤ |e| * M * ε) (hz : ‖z‖ ≤ ε) (hp : ‖p‖ ≤ M) :
    ‖((l * q ^ 2 : ℝ) : ℂ) - Complex.I * e * q * z * starRingEnd ℂ p‖ ≤
      2 * (|e| * M) ^ 2 * ε ^ 2 := by
  have hq2 : q ^ 2 ≤ (|e| * M * ε) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg q) hq 2
  calc
    _ ≤ ‖((l * q ^ 2 : ℝ) : ℂ)‖ + ‖Complex.I * e * q * z * starRingEnd ℂ p‖ :=
      norm_sub_le _ _
    _ = |l| * q ^ 2 + |e| * |q| * ‖z‖ * ‖p‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_pow,
        sq_abs, Complex.norm_I, one_mul, Complex.norm_conj]
    _ ≤ 1 * (|e| * M * ε) ^ 2 + |e| * (|e| * M * ε) * ε * M := by gcongr
    _ = _ := by ring

/-- The electric integrand difference retains all four local errors.
The coefficients `3,1,1,1` are universal. The factor `M≥1` is used only
to bound the scalar-field error by the displayed background scale.
-/
theorem stab_electric_integrand_sub_le
    {e M ε l₁ l₂ q₁ q₂ D X Φ G : ℝ} {z₁ z₂ p₁ p₂ : ℂ}
    (hM : 1 ≤ M) (hε : 0 ≤ ε) (_hD : 0 ≤ D) (_hX : 0 ≤ X) (hΦ : 0 ≤ Φ)
    (hG : 0 ≤ G) (hl₁ : |l₁| ≤ 1) (hld : |l₁ - l₂| ≤ G)
    (hq₁ : |q₁| ≤ |e| * M * ε) (hq₂ : |q₂| ≤ |e| * M * ε)
    (hqd : |q₁ - q₂| ≤ |e| * M * D)
    (hz₁ : ‖z₁‖ ≤ ε) (hz₂ : ‖z₂‖ ≤ ε) (hzd : ‖z₁ - z₂‖ ≤ X)
    (hp₁ : ‖p₁‖ ≤ M) (hpd : ‖p₁ - p₂‖ ≤ Φ) :
    ‖(((l₁ * q₁ ^ 2 : ℝ) : ℂ) - Complex.I * e * q₁ * z₁ * starRingEnd ℂ p₁) -
      (((l₂ * q₂ ^ 2 : ℝ) : ℂ) - Complex.I * e * q₂ * z₂ * starRingEnd ℂ p₂)‖ ≤
      (|e| * M) ^ 2 * (3 * ε * D + ε * X + ε ^ 2 * G + ε ^ 2 * Φ) := by
  let E := |e| * M
  have hM0 : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans hM
  have hE : 0 ≤ E := mul_nonneg (abs_nonneg _) hM0
  have heE : |e| ≤ E := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hM (abs_nonneg e)
  have hsq : |q₁ ^ 2 - q₂ ^ 2| ≤ 2 * (E * ε) * (E * D) := by
    have hh := stab_norm_sq_sub_le
      (z := (q₁ : ℂ)) (w := (q₂ : ℂ))
      (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hq₁)
      (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hq₂)
    simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hqd (by positivity))
  have hq₂sq : q₂ ^ 2 ≤ (E * ε) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg q₂) hq₂ 2
  have hlq : |l₁ * q₁ ^ 2 - l₂ * q₂ ^ 2| ≤
      2 * (E * ε) * (E * D) + G * (E * ε) ^ 2 := by
    have heq : l₁ * q₁ ^ 2 - l₂ * q₂ ^ 2 =
        l₁ * (q₁ ^ 2 - q₂ ^ 2) + (l₁ - l₂) * q₂ ^ 2 := by ring
    have hh : |l₁ * q₁ ^ 2 - l₂ * q₂ ^ 2| ≤
        |l₁ * (q₁ ^ 2 - q₂ ^ 2)| + |(l₁ - l₂) * q₂ ^ 2| := by
      rw [heq]
      exact abs_add_le _ _
    apply hh.trans
    simp only [abs_mul, abs_pow, sq_abs]
    exact add_le_add
      (by simpa only [one_mul] using mul_le_mul hl₁ hsq (abs_nonneg _) (by norm_num))
      (mul_le_mul hld hq₂sq (sq_nonneg _) hG)
  have ht := triple_norm_difference_aux
    (x₁ := (q₁ : ℂ)) (x₂ := (q₂ : ℂ)) (y₁ := z₁) (y₂ := z₂)
    (z₁ := starRingEnd ℂ p₁) (z₂ := starRingEnd ℂ p₂)
    (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hq₂) hz₁ hz₂
    (by simpa only [Complex.norm_conj] using hp₁)
  have ht' : ‖(q₁ : ℂ) * z₁ * starRingEnd ℂ p₁ -
      (q₂ : ℂ) * z₂ * starRingEnd ℂ p₂‖ ≤
      ε * M * (E * D) + (E * ε) * M * X + (E * ε) * ε * Φ := by
    apply ht.trans
    simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      ← map_sub (starRingEnd ℂ), Complex.norm_conj]
    gcongr
  have heq : (((l₁ * q₁ ^ 2 : ℝ) : ℂ) - Complex.I * e * q₁ * z₁ * starRingEnd ℂ p₁) -
      (((l₂ * q₂ ^ 2 : ℝ) : ℂ) - Complex.I * e * q₂ * z₂ * starRingEnd ℂ p₂) =
      ((l₁ * q₁ ^ 2 - l₂ * q₂ ^ 2 : ℝ) : ℂ) - Complex.I * e *
        ((q₁ : ℂ) * z₁ * starRingEnd ℂ p₁ - (q₂ : ℂ) * z₂ * starRingEnd ℂ p₂) := by
    push_cast
    ring
  rw [heq]
  calc
    _ ≤ ‖((l₁ * q₁ ^ 2 - l₂ * q₂ ^ 2 : ℝ) : ℂ)‖ + ‖Complex.I * e *
        ((q₁ : ℂ) * z₁ * starRingEnd ℂ p₁ - (q₂ : ℂ) * z₂ * starRingEnd ℂ p₂)‖ := norm_sub_le _ _
    _ ≤ (2 * (E * ε) * (E * D) + G * (E * ε) ^ 2) +
        |e| * (ε * M * (E * D) + (E * ε) * M * X + (E * ε) * ε * Φ) := by
      simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, one_mul]
      exact add_le_add hlq (mul_le_mul_of_nonneg_left ht' (abs_nonneg e))
    _ = 2 * E ^ 2 * ε * D + E ^ 2 * ε ^ 2 * G +
        E ^ 2 * ε * D + E ^ 2 * ε * X + |e| * E * ε ^ 2 * Φ := by dsimp only [E]; ring
    _ ≤ 2 * E ^ 2 * ε * D + E ^ 2 * ε ^ 2 * G +
        E ^ 2 * ε * D + E ^ 2 * ε * X + E * E * ε ^ 2 * Φ := by gcongr
    _ = _ := by dsimp only [E]; ring

end EmcsfAcExtension.Local
