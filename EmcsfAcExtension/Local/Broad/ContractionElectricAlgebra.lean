module

public import Mathlib

/-! # The electric scalar source after extracting its radial factor

The three product differences are kept separate before the smallness
bounds are inserted. Every coefficient is an explicit parameter.
-/

public section

open Complex

namespace EmcsfAcExtension.Local.Broad

/-- Compare a real geometric factor, a real charge ratio and a complex
scalar. The three displayed coefficients are exact and uniform in all
field values; the callers retain their dependence on the geometric box. -/
theorem electric_product_difference_of_bounds
    {P₁ P₂ q₁ q₂ P0 PG PX α ε E G X Kq H M : ℝ} {φ₁ φ₂ : ℂ}
    (hP0 : 0 ≤ P0) (hPG : 0 ≤ PG) (hPX : 0 ≤ PX) (hα : 0 ≤ α)
    (hε : 0 ≤ ε) (hE : 0 ≤ E) (hG : 0 ≤ G) (hX : 0 ≤ X)
    (hKq : 0 ≤ Kq) (_hH : 0 ≤ H) (_hM : 0 ≤ M)
    (hP₁ : |P₁| ≤ P0) (hδP : |P₁ - P₂| ≤ PG * G + PX * X)
    (hq₁ : |q₁| ≤ α * ε) (hq₂ : |q₂| ≤ α * ε)
    (hδq : |q₁ - q₂| ≤ Kq * α * E)
    (hφ₂ : ‖φ₂‖ ≤ M) (hδφ : ‖φ₁ - φ₂‖ ≤ H) :
    ‖(P₁ : ℂ) * q₁ * φ₁ - (P₂ : ℂ) * q₂ * φ₂‖ ≤
      P0 * (α * ε) * H + P0 * (Kq * α * E) * M + (PG * G + PX * X) * (α * ε) * M := by
  have heq : (P₁ : ℂ) * q₁ * φ₁ - (P₂ : ℂ) * q₂ * φ₂ =
      (P₁ : ℂ) * q₁ * (φ₁ - φ₂) + (P₁ : ℂ) * (q₁ - q₂ : ℝ) * φ₂ +
        (P₁ - P₂ : ℝ) * (q₂ : ℂ) * φ₂ := by push_cast; ring
  rw [heq]
  apply ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  gcongr

/-- Insert the small ratio and geometric-error factors in the electric
source comparison. The coefficient is explicit and depends only on the
four preceding comparison coefficients. -/
theorem electric_error_polynomial_le {P0 PG PX α ε E G X Kq Kφ Kμ M : ℝ}
    (hP0 : 0 ≤ P0) (hPG : 0 ≤ PG) (hPX : 0 ≤ PX) (hα : 0 ≤ α)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hE : 0 ≤ E) (_hG : 0 ≤ G)
    (_hKq : 0 ≤ Kq) (hKφ : 0 ≤ Kφ) (hKμ : 0 ≤ Kμ) (hM : 1 ≤ M)
    (hεG : ε * G ≤ E) (hX : X ≤ Kμ * ε * E) :
    P0 * (α * ε) * (Kφ * E) + P0 * (Kq * α * E) * M +
        (PG * G + PX * X) * (α * ε) * M ≤
      (P0 * Kφ + P0 * Kq + PG + PX * Kμ) * α * M * E := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hsq : ε ^ 2 ≤ 1 := by simpa only [one_pow] using (sq_le_sq₀ hε zero_le_one).mpr hε1
  have hfirst : P0 * (α * ε) * (Kφ * E) ≤ P0 * Kφ * α * M * E := by
    calc
      _ ≤ P0 * (α * 1) * (Kφ * E) := by gcongr
      _ ≤ P0 * (α * M) * (Kφ * E) := by gcongr
      _ = _ := by ring
  have hGterm := mul_le_mul_of_nonneg_left hεG (show 0 ≤ PG * α * M by positivity)
  have hXterm := mul_le_mul_of_nonneg_left hX (show 0 ≤ PX * α * ε * M by positivity)
  have hXterm' := mul_le_mul_of_nonneg_left hsq (show 0 ≤ PX * α * M * Kμ * E by positivity)
  nlinarith only [hfirst, hGterm, hXterm, hXterm']

end EmcsfAcExtension.Local.Broad
