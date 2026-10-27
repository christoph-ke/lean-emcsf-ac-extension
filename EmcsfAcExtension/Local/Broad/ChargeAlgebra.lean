module

public import Mathlib

/-! # Electric comparison with changing radii

The algebraic square comparison used in charged_SF_new_version.tex:L5718–5726 retains
both the charge difference and the difference of the radial denominators.
-/

public section

namespace EmcsfAcExtension.Local.Broad

/-- Squaring an undifferenced charge bound and dividing by its actual radius.
The coefficient is exactly one, and the total quotient handles zero radius. -/
theorem electric_square_le_of_charge_bound {Q r A : ℝ} (hA : 0 ≤ A)
    (hQ : |Q| ≤ A * r ^ 2) : Q ^ 2 / r ^ 2 ≤ A ^ 2 * r ^ 2 := by
  by_cases hr : r = 0
  · simp [hr]
  have hsq := (sq_le_sq₀ (abs_nonneg Q) (mul_nonneg hA (sq_nonneg r))).mpr hQ
  simp only [sq_abs, mul_pow] at hsq
  apply (div_le_iff₀ (sq_pos_of_ne_zero hr)).mpr
  exact hsq.trans_eq (by ring)

/-- Electric square comparison from the raw charge bounds. Its displayed
coefficient depends only on the radius-comparison factor `k` and the charge
comparison coefficient `K`, uniformly in all scalar values and scales. -/
theorem electric_square_difference_of_bounds
    {r₁ r₂ Q₁ Q₂ α ε E g k K : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hα : 0 ≤ α) (hε : 0 ≤ ε)
    (hE : 0 ≤ E) (hg : 0 ≤ g) (hk : 0 ≤ k) (hK : 0 ≤ K)
    (hratio : r₂ ≤ k * r₁)
    (hQ₁ : |Q₁| ≤ α * ε * r₁ ^ 2) (hQ₂ : |Q₂| ≤ α * ε * r₂ ^ 2)
    (hδQ : |Q₁ - Q₂| ≤ K * α * r₁ ^ 2 * E)
    (hδr : |r₁ - r₂| ≤ g * r₁) (hεg : ε * g ≤ E) :
    |Q₁ ^ 2 / r₁ ^ 2 - Q₂ ^ 2 / r₂ ^ 2| ≤
      (K * (1 + k ^ 2) + k ^ 2 * (1 + k)) * α ^ 2 * ε * r₁ ^ 2 * E := by
  have heq : Q₁ ^ 2 / r₁ ^ 2 - Q₂ ^ 2 / r₂ ^ 2 =
      (Q₁ - Q₂) * (Q₁ + Q₂) / r₁ ^ 2 +
        Q₂ ^ 2 * (r₂ - r₁) * (r₂ + r₁) / (r₁ ^ 2 * r₂ ^ 2) := by
    field_simp [hr₁.ne', hr₂.ne']
    ring
  have hsum : |Q₁ + Q₂| ≤ α * ε * r₁ ^ 2 + α * ε * r₂ ^ 2 :=
    (abs_add_le _ _).trans (add_le_add hQ₁ hQ₂)
  have hrev : |r₂ - r₁| ≤ g * r₁ := by
    rw [abs_sub_comm]
    exact hδr
  have hQ₂sq : Q₂ ^ 2 ≤ (α * ε * r₂ ^ 2) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg Q₂) (by positivity)).mpr hQ₂
  have hfirst : |(Q₁ - Q₂) * (Q₁ + Q₂) / r₁ ^ 2| ≤
      K * (1 + k ^ 2) * α ^ 2 * ε * r₁ ^ 2 * E := by
    calc
      _ = |Q₁ - Q₂| * |Q₁ + Q₂| / r₁ ^ 2 := by
        rw [abs_div, abs_mul, abs_of_pos (sq_pos_of_pos hr₁)]
      _ ≤ (K * α * r₁ ^ 2 * E) * (α * ε * r₁ ^ 2 + α * ε * r₂ ^ 2) / r₁ ^ 2 := by
        gcongr
      _ ≤ (K * α * r₁ ^ 2 * E) *
          (α * ε * r₁ ^ 2 + α * ε * (k * r₁) ^ 2) / r₁ ^ 2 := by gcongr
      _ = _ := by field_simp [hr₁.ne']
  have hsecond : |Q₂ ^ 2 * (r₂ - r₁) * (r₂ + r₁) / (r₁ ^ 2 * r₂ ^ 2)| ≤
      k ^ 2 * (1 + k) * α ^ 2 * ε * r₁ ^ 2 * E := by
    calc
      _ = Q₂ ^ 2 * |r₂ - r₁| * (r₂ + r₁) / (r₁ ^ 2 * r₂ ^ 2) := by
        simp only [abs_div, abs_mul, abs_of_nonneg (sq_nonneg Q₂),
          abs_of_pos (sq_pos_of_pos hr₁), abs_of_pos (sq_pos_of_pos hr₂),
          abs_of_pos (add_pos hr₂ hr₁)]
      _ ≤ (α * ε * r₂ ^ 2) ^ 2 * |r₂ - r₁| * (r₂ + r₁) / (r₁ ^ 2 * r₂ ^ 2) := by
        gcongr
      _ = α ^ 2 * ε ^ 2 * r₂ ^ 2 * |r₂ - r₁| * (r₂ + r₁) / r₁ ^ 2 := by
        field_simp [hr₁.ne', hr₂.ne']
      _ ≤ α ^ 2 * ε ^ 2 * (k * r₁) ^ 2 * (g * r₁) * (k * r₁ + r₁) / r₁ ^ 2 := by
        gcongr
      _ = k ^ 2 * (1 + k) * α ^ 2 * ε * r₁ ^ 2 * (ε * g) := by
        field_simp [hr₁.ne']
        ring
      _ ≤ _ := by gcongr
  rw [heq]
  exact ((abs_add_le _ _).trans (add_le_add hfirst hsecond)).trans_eq (by ring)

/-- Dividing the raw charge comparison by the two actual squared radii.
The exact coefficient depends only on `K,k`; the changing denominator is
retained and no positive lower radius is assumed uniformly. -/
theorem charge_quotient_difference_of_bounds {r₁ r₂ Q₁ Q₂ α ε E g k K : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hα : 0 ≤ α) (hε : 0 ≤ ε)
    (_hE : 0 ≤ E) (hg : 0 ≤ g) (hk : 0 ≤ k) (_hK : 0 ≤ K)
    (hratio : r₂ ≤ k * r₁) (hQ₂ : |Q₂| ≤ α * ε * r₂ ^ 2)
    (hδQ : |Q₁ - Q₂| ≤ K * α * r₁ ^ 2 * E)
    (hδr : |r₁ - r₂| ≤ g * r₁) (hεg : ε * g ≤ E) :
    |Q₁ / r₁ ^ 2 - Q₂ / r₂ ^ 2| ≤ (K + (1 + k)) * α * E := by
  have heq : Q₁ / r₁ ^ 2 - Q₂ / r₂ ^ 2 = (Q₁ - Q₂) / r₁ ^ 2 +
      Q₂ * (r₂ - r₁) * (r₂ + r₁) / (r₁ ^ 2 * r₂ ^ 2) := by
    field_simp [hr₁.ne', hr₂.ne']
    ring
  have hfirst : |(Q₁ - Q₂) / r₁ ^ 2| ≤ K * α * E := by
    rw [abs_div, abs_of_pos (sq_pos_of_pos hr₁)]
    exact (div_le_iff₀ (sq_pos_of_pos hr₁)).mpr (hδQ.trans_eq (by ring))
  have hsecond : |Q₂ * (r₂ - r₁) * (r₂ + r₁) / (r₁ ^ 2 * r₂ ^ 2)| ≤
      (1 + k) * α * E := by
    have hrev : |r₂ - r₁| ≤ g * r₁ := by rw [abs_sub_comm]; exact hδr
    calc
      _ = |Q₂| * |r₂ - r₁| * (r₂ + r₁) / (r₁ ^ 2 * r₂ ^ 2) := by
        simp only [abs_div, abs_mul, abs_of_pos (sq_pos_of_pos hr₁),
          abs_of_pos (sq_pos_of_pos hr₂), abs_of_pos (add_pos hr₂ hr₁)]
      _ ≤ (α * ε * r₂ ^ 2) * (g * r₁) * (k * r₁ + r₁) /
          (r₁ ^ 2 * r₂ ^ 2) := by gcongr
      _ = (1 + k) * α * (ε * g) := by field_simp [hr₁.ne', hr₂.ne']; ring
      _ ≤ _ := by gcongr
  rw [heq]
  exact ((abs_add_le _ _).trans (add_le_add hfirst hsecond)).trans_eq (by ring)

end EmcsfAcExtension.Local.Broad
