module

public import EmcsfAcExtension.Local.Stability.DifferenceMomentsAlgebra
import Mathlib.Tactic.FieldSimp

/-! # Algebra of normalized mass forcing

The electromagnetic square difference keeps one undifferenced charge,
hence the additional scalar smallness factor. The real linear mass
equation is subtracted without discarding its positive damping.
-/

public section

namespace EmcsfAcExtension.Local

/-- The electromagnetic square difference has universal coefficient
`20` under the common radial comparison. In particular its right side
retains the undifferenced normalized charge bound `K`. -/
theorem stab_charge_square_sub_le {Q₁ Q₂ r s K D G : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hK : 0 ≤ K) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hc : s ≤ 4 * r) (hQ₁ : |Q₁| ≤ K * r ^ 2) (hQ₂ : |Q₂| ≤ K * s ^ 2)
    (hδ : |Q₁ - Q₂| ≤ D * r ^ 2) (hR : |r - s| ≤ G * r) :
    |Q₁ ^ 2 / r ^ 2 - Q₂ ^ 2 / s ^ 2| ≤
      20 * K * r ^ 2 * (D + K * G) := by
  have hqr : |Q₁ / r| ≤ K * r := by
    rw [abs_div, abs_of_pos hr, div_le_iff₀ hr]
    nlinarith only [hQ₁]
  have hqs : |Q₂ / s| ≤ K * s := by
    rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
    nlinarith only [hQ₂]
  have hfirst : |(Q₁ - Q₂) / r| ≤ D * r := by
    rw [abs_div, abs_of_pos hr, div_le_iff₀ hr]
    nlinarith only [hδ]
  have hsecond : |(Q₂ / s) * ((s - r) / r)| ≤ 4 * K * G * r := by
    have hrg : |(s - r) / r| ≤ G := by
      rw [abs_div, abs_of_pos hr, div_le_iff₀ hr, abs_sub_comm]
      exact hR
    calc
      _ = |Q₂ / s| * |(s - r) / r| := abs_mul _ _
      _ ≤ (K * s) * G := mul_le_mul hqs hrg (abs_nonneg _) (mul_nonneg hK hs.le)
      _ ≤ (K * (4 * r)) * G :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hK) hG
      _ = _ := by ring
  have hratio : |Q₁ / r - Q₂ / s| ≤ r * (D + 4 * K * G) := by
    have heq : Q₁ / r - Q₂ / s = (Q₁ - Q₂) / r + (Q₂ / s) * ((s - r) / r) := by
      field_simp
      ring
    calc
      _ ≤ |(Q₁ - Q₂) / r| + |(Q₂ / s) * ((s - r) / r)| := by
        rw [heq]; exact abs_add_le _ _
      _ ≤ D * r + 4 * K * G * r := add_le_add hfirst hsecond
      _ = _ := by ring
  have hsum : |Q₁ / r + Q₂ / s| ≤ 5 * K * r := by
    have hh := mul_le_mul_of_nonneg_left hc hK
    exact (abs_add_le _ _).trans ((add_le_add hqr hqs).trans (by nlinarith only [hh]))
  calc
    _ = |Q₁ / r + Q₂ / s| * |Q₁ / r - Q₂ / s| := by
      rw [← abs_mul]
      congr 1
      field_simp
      ring
    _ ≤ (5 * K * r) * (r * (D + 4 * K * G)) :=
      mul_le_mul hsum hratio (abs_nonneg _) (by positivity)
    _ ≤ _ := by
      have hh := mul_nonneg hK (mul_nonneg (sq_nonneg r) hD)
      nlinarith only [hh]

/-- Subtract two normalized mass equations. The damping of the first
equation is kept on the left; the geometric weight error multiplies
only undifferenced second-solution quantities. This exact identity has
no estimate constant or size hypothesis. -/
theorem stab_mass_difference_identity_algebra {w₁ w₂ μ₁ μ₂ X₁ X₂ E₁ E₂ : ℝ} :
    w₁ * ((1 - μ₁) * X₁ + E₁ - μ₁) - w₂ * ((1 - μ₂) * X₂ + E₂ - μ₂) =
      (w₁ * ((1 - μ₂) * (X₁ - X₂) + (E₁ - E₂)) +
        (w₁ - w₂) * ((1 - μ₂) * X₂ + E₂ - μ₂)) -
        w₁ * (1 + X₁) * (μ₁ - μ₂) := by ring

/-- Absolute forcing in the damped mass difference has universal
geometric coefficient `20`; the scalar difference has coefficient
`2ε`. Bounds on the electromagnetic difference remain explicit. -/
theorem stab_mass_difference_forcing_le
    {w₁ w₂ μ E₁ E₂ ε G : ℝ} {x₁ x₂ : ℂ}
    (hw : 0 ≤ w₁) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) (hE : 0 ≤ E₂)
    (hx₁ : ‖x₁‖ ≤ ε) (hx₂ : ‖x₂‖ ≤ ε)
    (hweight : |w₁ - w₂| ≤ 20 * G * w₁) :
    |w₁ * ((1 - μ) * (‖x₁‖ ^ 2 - ‖x₂‖ ^ 2) + (E₁ - E₂)) +
        (w₁ - w₂) * ((1 - μ) * ‖x₂‖ ^ 2 + E₂ - μ)| ≤
      (2 * ε) * (w₁ * ‖x₁ - x₂‖) + w₁ * |E₁ - E₂| +
        (20 * G) * (w₁ * (‖x₂‖ ^ 2 + E₂ + μ)) := by
  have hγ : 0 ≤ 1 - μ := sub_nonneg.mpr hμ1
  have hγ1 : 1 - μ ≤ 1 := by linarith only [hμ]
  have hscalar := stab_norm_sq_sub_le hx₁ hx₂
  have hb : |(1 - μ) * ‖x₂‖ ^ 2 + E₂ - μ| ≤ ‖x₂‖ ^ 2 + E₂ + μ := by
    calc
      _ ≤ |(1 - μ) * ‖x₂‖ ^ 2 + E₂| + |μ| := abs_sub _ _
      _ = (1 - μ) * ‖x₂‖ ^ 2 + E₂ + μ := by
        rw [abs_of_nonneg (by positivity), abs_of_nonneg hμ]
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hγ1 (sq_nonneg ‖x₂‖)
        linarith only [hh]
  have hmain : |(1 - μ) * (‖x₁‖ ^ 2 - ‖x₂‖ ^ 2) + (E₁ - E₂)| ≤
      2 * ε * ‖x₁ - x₂‖ + |E₁ - E₂| := by
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_of_nonneg hγ]
    apply add_le_add _ le_rfl
    exact (mul_le_mul_of_nonneg_right hγ1 (abs_nonneg _)).trans
      (by simpa only [one_mul] using hscalar)
  calc
    _ ≤ |w₁ * ((1 - μ) * (‖x₁‖ ^ 2 - ‖x₂‖ ^ 2) + (E₁ - E₂))| +
        |(w₁ - w₂) * ((1 - μ) * ‖x₂‖ ^ 2 + E₂ - μ)| := abs_add_le _ _
    _ = w₁ * |(1 - μ) * (‖x₁‖ ^ 2 - ‖x₂‖ ^ 2) + (E₁ - E₂)| +
        |w₁ - w₂| * |(1 - μ) * ‖x₂‖ ^ 2 + E₂ - μ| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hw]
    _ ≤ w₁ * (2 * ε * ‖x₁ - x₂‖ + |E₁ - E₂|) +
        (20 * G * w₁) * (‖x₂‖ ^ 2 + E₂ + μ) := add_le_add
      (mul_le_mul_of_nonneg_left hmain hw)
      (mul_le_mul hweight hb (abs_nonneg _) ((abs_nonneg _).trans hweight))
    _ = _ := by ring

end EmcsfAcExtension.Local
