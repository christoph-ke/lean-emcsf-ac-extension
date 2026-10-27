module

public import Mathlib
import EmcsfAcExtension.Local.Stability.SourceDifferenceEMAlgebra

/-! # Algebra for the charged curvature integrand

The radius-square weight is factored before subtraction. The only scalar
background difference occurs with a charge factor, preserving `ε/M`.
-/

public section

open Complex

namespace EmcsfAcExtension.Local.Stab

/-- Charged primitive bracket comparison. `C` depends only on the fixed
charge and ratio constants `Q,D`, uniformly in all factors and parameters.
The separate individual estimate keeps its full factor `ε²`. -/
theorem em_primitive_bracket_difference_le (Q D : ℝ) (hQ : 0 < Q) (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (a M ε H Z F q₁ q₂ : ℝ) (p₁ p₂ z₁ z₂ c : ℂ),
      0 ≤ a → 1 ≤ M → 0 ≤ ε → ε ≤ 1 → 0 ≤ H → 0 ≤ Z → 0 ≤ F →
      |q₁| ≤ a * M * ε → |q₂| ≤ a * M * ε → |q₁ - q₂| ≤ Q * a * M * H →
      ‖p₁‖ ≤ M → ‖p₂‖ ≤ M → ‖p₁ - p₂‖ ≤ M * F →
      ‖z₁‖ ≤ ε → ‖z₂‖ ≤ ε → ‖z₁ - z₂‖ ≤ D * Z → ‖c‖ ≤ a →
      ‖(q₁ : ℂ) ^ 2 + c * q₁ * z₁ * starRingEnd ℂ p₁‖ ≤ 2 * a ^ 2 * M ^ 2 * ε ^ 2 ∧
      ‖((q₁ : ℂ) ^ 2 + c * q₁ * z₁ * starRingEnd ℂ p₁) -
          ((q₂ : ℂ) ^ 2 + c * q₂ * z₂ * starRingEnd ℂ p₂)‖ ≤
        C * a ^ 2 * M ^ 2 * (H + Z + ε * F) := by
  refine ⟨4 * (Q + D + 1), by positivity, ?_⟩
  intro a M ε H Z F q₁ q₂ p₁ p₂ z₁ z₂ c ha hM hε hε₁ hH hZ hF
    hq₁ hq₂ hδq hp₁ hp₂ hδp hz₁ hz₂ hδz hc
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hsq₁ : |q₁| ^ 2 ≤ (a * M * ε) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hq₁ 2
  have hnormsq : ‖(q₁ : ℂ) ^ 2‖ ≤ (a * M * ε) ^ 2 := by
    simpa only [norm_pow, norm_real, Real.norm_eq_abs] using hsq₁
  have hproduct : ‖c * q₁ * z₁ * starRingEnd ℂ p₁‖ ≤ a * (a * M * ε) * ε * M := by
    simp only [norm_mul, norm_real, Real.norm_eq_abs, RCLike.norm_conj]
    exact mul_le_mul (mul_le_mul (mul_le_mul hc hq₁ (abs_nonneg _) ha)
      hz₁ (norm_nonneg _) (by positivity)) hp₁ (norm_nonneg _) (by positivity)
  constructor
  · apply (norm_add_le _ _).trans
    nlinarith only [hnormsq, hproduct]
  have hδsquare : ‖(q₁ : ℂ) ^ 2 - (q₂ : ℂ) ^ 2‖ ≤
      2 * Q * a ^ 2 * M ^ 2 * H := by
    have heq : (q₁ : ℂ) ^ 2 - (q₂ : ℂ) ^ 2 = ((q₁ + q₂ : ℝ) : ℂ) * ((q₁ - q₂ : ℝ) : ℂ) := by
      push_cast
      ring
    rw [heq, norm_mul, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    calc
      _ ≤ (2 * a * M * ε) * (Q * a * M * H) :=
        mul_le_mul ((abs_add_le _ _).trans (by linarith only [hq₁, hq₂])) hδq
          (abs_nonneg _) (by positivity)
      _ = (2 * Q * a ^ 2 * M ^ 2 * H) * ε := by ring
      _ ≤ _ :=
          by simpa only [mul_one] using mul_le_mul_of_nonneg_left hε₁
               (by positivity : 0 ≤ 2 * Q * a ^ 2 * M ^ 2 * H)
  have hδpconj : ‖starRingEnd ℂ p₁ - starRingEnd ℂ p₂‖ ≤ M * F := by
    simpa only [← map_sub, RCLike.norm_conj] using hδp
  have hδprod : ‖c * q₁ * z₁ * starRingEnd ℂ p₁ - c * q₂ * z₂ * starRingEnd ℂ p₂‖ ≤
      a ^ 2 * M ^ 2 * (Q * H + D * Z + ε * F) := by
    have heq : c * q₁ * z₁ * starRingEnd ℂ p₁ - c * q₂ * z₂ * starRingEnd ℂ p₂ =
        c * ((q₁ - q₂ : ℝ) : ℂ) * z₁ * starRingEnd ℂ p₁ +
          c * q₂ * (z₁ - z₂) * starRingEnd ℂ p₁ +
          c * q₂ * z₂ * (starRingEnd ℂ p₁ - starRingEnd ℂ p₂) := by push_cast; ring
    rw [heq]
    apply ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    simp only [norm_mul, norm_real, Real.norm_eq_abs, RCLike.norm_conj]
    calc
      _ ≤ a * (Q * a * M * H) * ε * M +
          a * (a * M * ε) * (D * Z) * M + a * (a * M * ε) * ε * (M * F) := by
        apply add_le_add
        · apply add_le_add
          · exact mul_le_mul (mul_le_mul (mul_le_mul hc hδq (abs_nonneg _) ha)
              hz₁ (norm_nonneg _) (by positivity)) hp₁ (norm_nonneg _) (by positivity)
          · exact mul_le_mul (mul_le_mul (mul_le_mul hc hq₂ (abs_nonneg _) ha)
              hδz (norm_nonneg _) (by positivity)) hp₁ (norm_nonneg _) (by positivity)
        · exact mul_le_mul (mul_le_mul (mul_le_mul hc hq₂ (abs_nonneg _) ha)
            hz₂ (norm_nonneg _) (by positivity)) hδpconj (norm_nonneg _) (by positivity)
      _ = a ^ 2 * M ^ 2 * (Q * H * ε + D * Z * ε + (ε * F) * ε) := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add (add_le_add
          (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hε₁ (by positivity : 0 ≤ Q * H))
          (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hε₁ (by positivity : 0 ≤ D * Z)))
          (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hε₁ (by positivity : 0 ≤ ε * F))
  rw [show ((q₁ : ℂ) ^ 2 + c * q₁ * z₁ * starRingEnd ℂ p₁) -
        ((q₂ : ℂ) ^ 2 + c * q₂ * z₂ * starRingEnd ℂ p₂) =
      ((q₁ : ℂ) ^ 2 - (q₂ : ℂ) ^ 2) +
        (c * q₁ * z₁ * starRingEnd ℂ p₁ - c * q₂ * z₂ * starRingEnd ℂ p₂) by ring]
  apply (norm_add_le _ _).trans
  apply (add_le_add hδsquare hδprod).trans
  have h₁ : 3 * Q ≤ 4 * (Q + D + 1) := by linarith only [hQ, hD]
  have h₂ : D ≤ 4 * (Q + D + 1) := by linarith only [hQ, hD]
  have h₃ : 1 ≤ 4 * (Q + D + 1) := by linarith only [hQ, hD]
  have hrows := add_le_add (add_le_add
    (mul_le_mul_of_nonneg_right h₁ hH) (mul_le_mul_of_nonneg_right h₂ hZ))
    (mul_le_mul_of_nonneg_right h₃ (mul_nonneg hε hF))
  have := mul_le_mul_of_nonneg_left hrows (by positivity : 0 ≤ a ^ 2 * M ^ 2)
  nlinarith only [this]

/-- Multiplication by a varying expansion and radius square. The explicit
coefficients `6,P` are uniform in all parameters. This is the algebraic
step that cancels the inverse-cube exterior coefficient after integration. -/
theorem em_radial_integrand_difference_le {d G E ε P X : ℝ}
    {l₁ l₂ r₁ r₂ : ℝ} {z₁ z₂ : ℂ}
    (hd : 0 ≤ d) (hG : 0 ≤ G) (_hE : 0 ≤ E) (_hε : 0 ≤ ε)
    (_hP : 0 ≤ P) (_hX : 0 ≤ X)
    (_hl₁ : |l₁| ≤ 1) (hl₂ : |l₂| ≤ 1) (hδl : |l₁ - l₂| ≤ G)
    (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (hr₁d : r₁ ≤ d) (hr₂d : r₂ ≤ d)
    (hδr : |r₁ - r₂| ≤ G * d)
    (hz₁ : ‖z₁‖ ≤ 2 * E * ε ^ 2) (hδz : ‖z₁ - z₂‖ ≤ P * E * X) :
    ‖((l₁ * r₁ ^ 2 : ℝ) : ℂ) * z₁ - ((l₂ * r₂ ^ 2 : ℝ) : ℂ) * z₂‖ ≤
      E * d ^ 2 * (6 * ε ^ 2 * G + P * X) := by
  have hrsq : |r₁ ^ 2 - r₂ ^ 2| ≤ 2 * G * d ^ 2 := by
    rw [show r₁ ^ 2 - r₂ ^ 2 = (r₁ - r₂) * (r₁ + r₂) by ring,
      abs_mul, abs_of_nonneg (add_nonneg hr₁ hr₂)]
    calc
      _ ≤ (G * d) * (2 * d) := mul_le_mul hδr (by linarith only [hr₁d, hr₂d]) (by positivity)
          (by positivity)
      _ = _ := by ring
  have hc₁ : |l₁ * r₁ ^ 2 - l₂ * r₂ ^ 2| ≤ 3 * G * d ^ 2 := by
    rw [show l₁ * r₁ ^ 2 - l₂ * r₂ ^ 2 = (l₁ - l₂) * r₁ ^ 2 + l₂ * (r₁ ^ 2 - r₂ ^ 2) by ring]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg r₁)]
    have hpow := pow_le_pow_left₀ hr₁ hr₁d 2
    have h := add_le_add (mul_le_mul hδl hpow (sq_nonneg _) hG)
      (mul_le_mul hl₂ hrsq (abs_nonneg _) zero_le_one)
    nlinarith only [h]
  have hc₂ : |l₂ * r₂ ^ 2| ≤ d ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg r₂)]
    simpa only [one_mul] using mul_le_mul hl₂ (pow_le_pow_left₀ hr₂ hr₂d 2)
      (sq_nonneg _) zero_le_one
  have hn := norm_em_product_sub_le ((l₁ * r₁ ^ 2 : ℝ) : ℂ) ((l₂ * r₂ ^ 2 : ℝ) : ℂ) z₁ z₂
  rw [← ofReal_sub, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs] at hn
  apply hn.trans
  have h := add_le_add (mul_le_mul hc₁ hz₁ (norm_nonneg _) (by positivity))
    (mul_le_mul hc₂ hδz (norm_nonneg _) (sq_nonneg _))
  nlinarith only [h]

end EmcsfAcExtension.Local.Stab
