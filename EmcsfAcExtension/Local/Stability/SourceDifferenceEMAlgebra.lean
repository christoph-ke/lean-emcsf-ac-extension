module

public import Mathlib

/-! # Electromagnetic monomial differences

The three exact Maxwell-substituted families are estimated separately.
The scalar-background difference is normalized only by `M`, never by the
coupling or by the small variation parameter.
-/

public section

open Complex

namespace EmcsfAcExtension.Local.Stab

/-- Two-factor complex subtraction with exact universal coefficients one. -/
theorem norm_em_product_sub_le (a₁ a₂ b₁ b₂ : ℂ) :
    ‖a₁ * b₁ - a₂ * b₂‖ ≤ ‖a₁ - a₂‖ * ‖b₁‖ + ‖a₂‖ * ‖b₁ - b₂‖ := by
  rw [show a₁ * b₁ - a₂ * b₂ = (a₁ - a₂) * b₁ + a₂ * (b₁ - b₂) by ring]
  exact (norm_add_le _ _).trans_eq (by rw [norm_mul, norm_mul])

private theorem abs_product_sub_le (a₁ a₂ b₁ b₂ : ℝ) :
    |a₁ * b₁ - a₂ * b₂| ≤ |a₁ - a₂| * |b₁| + |a₂| * |b₁ - b₂| := by
  rw [show a₁ * b₁ - a₂ * b₂ = (a₁ - a₂) * b₁ + a₂ * (b₁ - b₂) by ring]
  exact (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_mul])

private theorem abs_square_sub_le (q₁ q₂ : ℝ) :
    |q₁ ^ 2 - q₂ ^ 2| ≤ (|q₁| + |q₂|) * |q₁ - q₂| := by
  rw [show q₁ ^ 2 - q₂ ^ 2 = (q₁ + q₂) * (q₁ - q₂) by ring, abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (abs_nonneg _)

/-- Imaginary-current subtraction, with exact universal coefficients one. -/
theorem abs_im_scalar_current_sub_le (p₁ p₂ z₁ z₂ : ℂ) :
    |(starRingEnd ℂ p₁ * z₁).im - (starRingEnd ℂ p₂ * z₂).im| ≤
      ‖p₁‖ * ‖z₁ - z₂‖ + ‖p₁ - p₂‖ * ‖z₂‖ := by
  rw [← Complex.sub_im]
  apply (Complex.abs_im_le_norm _).trans
  rw [show starRingEnd ℂ p₁ * z₁ - starRingEnd ℂ p₂ * z₂ =
      starRingEnd ℂ p₁ * (z₁ - z₂) + starRingEnd ℂ (p₁ - p₂) * z₂ by
    rw [map_sub]
    ring]
  exact (norm_add_le _ _).trans_eq (by simp only [norm_mul, RCLike.norm_conj])

/-- Difference bound for all three electromagnetic monomial families.
`C` depends only on fixed comparison constants `Q,D`, uniformly in every
physical parameter and all real or complex factors. Both signs of the
middle electromagnetic term are covered by the arbitrary coefficient `c`.
The normalized background difference `F` is bounded using `M`, not the coupling. -/
theorem em_monomial_difference_le (Q D : ℝ) (hQ : 0 < Q) (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (a M ε G H Z F b₁ b₂ q₁ q₂ : ℝ) (p₁ p₂ z₁ z₂ c d : ℂ),
      0 ≤ a → 1 ≤ M → 0 ≤ ε → ε ≤ 1 → 0 ≤ G → 0 ≤ H → 0 ≤ Z → 0 ≤ F →
      |b₁| ≤ 1 → |b₂| ≤ 1 → |b₁ - b₂| ≤ 2 * G →
      |q₁| ≤ a * M * ε → |q₂| ≤ a * M * ε → |q₁ - q₂| ≤ Q * a * M * H →
      ‖p₁‖ ≤ M → ‖p₂‖ ≤ M → ‖p₁ - p₂‖ ≤ M * F →
      ‖z₁‖ ≤ ε → ‖z₂‖ ≤ ε → ‖z₁ - z₂‖ ≤ D * Z → ‖c‖ ≤ a → ‖d‖ ≤ a ^ 2 →
      ‖(5 * b₁ * (q₁ : ℂ) ^ 2 * z₁ + c * b₁ * q₁ * (3 * z₁ + p₁) +
            d * b₁ * p₁ * (((starRingEnd ℂ p₁ * z₁).im : ℝ) : ℂ)) -
          (5 * b₂ * (q₂ : ℂ) ^ 2 * z₂ + c * b₂ * q₂ * (3 * z₂ + p₂) +
            d * b₂ * p₂ * (((starRingEnd ℂ p₂ * z₂).im : ℝ) : ℂ))‖ ≤
        C * a ^ 2 * M ^ 2 * (H + Z + ε * G + ε * F) := by
  let C := 32 * (Q + D + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro a M ε G H Z F b₁ b₂ q₁ q₂ p₁ p₂ z₁ z₂ c d ha hM hε hε₁ hG hH hZ hF
    hb₁ hb₂ hδb hq₁ hq₂ hδq hp₁ hp₂ hδp hz₁ hz₂ hδz hc hd
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hεM : ε ≤ M := hε₁.trans hM
  have hε₂ : ε ^ 2 ≤ 1 := pow_le_one₀ hε hε₁
  have hε₃ : ε ^ 3 ≤ ε := by
    convert mul_le_mul_of_nonneg_right hε₂ hε using 1 <;> ring
  have hqsum : |q₁| + |q₂| ≤ 2 * a * M * ε := by linarith only [hq₁, hq₂]
  have hq₁sq : |q₁ ^ 2| ≤ (a * M * ε) ^ 2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg q₁) hq₁ 2
  have hq₂sq : |q₂ ^ 2| ≤ (a * M * ε) ^ 2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg q₂) hq₂ 2
  have hδqsq : |q₁ ^ 2 - q₂ ^ 2| ≤ (2 * a * M * ε) * (Q * a * M * H) :=
    (abs_square_sub_le q₁ q₂).trans
      (mul_le_mul hqsum hδq (abs_nonneg _) (by positivity))
  have hA : |b₁ * q₁ ^ 2 - b₂ * q₂ ^ 2| ≤
      2 * G * (a * M * ε) ^ 2 + (2 * a * M * ε) * (Q * a * M * H) := by
    apply (abs_product_sub_le b₁ b₂ (q₁ ^ 2) (q₂ ^ 2)).trans
    calc
      _ ≤ (2 * G) * (a * M * ε) ^ 2 + 1 * ((2 * a * M * ε) * (Q * a * M * H)) := by
        gcongr
      _ = _ := by ring
  have hA₂ : |b₂ * q₂ ^ 2| ≤ (a * M * ε) ^ 2 := by
    rw [abs_mul]
    calc
      _ ≤ 1 * (a * M * ε) ^ 2 := by gcongr
      _ = _ := by ring
  have hfive : ‖(5 : ℂ)‖ = 5 := by norm_num
  have hthree : ‖(3 : ℂ)‖ = 3 := by norm_num
  have hfirst : ‖5 * b₁ * (q₁ : ℂ) ^ 2 * z₁ - 5 * b₂ * (q₂ : ℂ) ^ 2 * z₂‖ ≤
      a ^ 2 * M ^ 2 * (10 * ε * G + 10 * Q * H + 5 * D * Z) := by
    have heq : 5 * (b₁ : ℂ) * (q₁ : ℂ) ^ 2 * z₁ - 5 * b₂ * (q₂ : ℂ) ^ 2 * z₂ =
        5 * ((((b₁ * q₁ ^ 2 : ℝ) : ℂ) * z₁) - (((b₂ * q₂ ^ 2 : ℝ) : ℂ) * z₂)) := by
      push_cast
      ring
    rw [heq, norm_mul, hfive]
    have hn := norm_em_product_sub_le ((b₁ * q₁ ^ 2 : ℝ) : ℂ)
      ((b₂ * q₂ ^ 2 : ℝ) : ℂ) z₁ z₂
    rw [← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs] at hn
    calc
      _ ≤ 5 * (|b₁ * q₁ ^ 2 - b₂ * q₂ ^ 2| * ‖z₁‖ + |b₂ * q₂ ^ 2| * ‖z₁ - z₂‖) := by
        gcongr
      _ ≤ 5 * ((2 * G * (a * M * ε) ^ 2 +
          (2 * a * M * ε) * (Q * a * M * H)) * ε + (a * M * ε) ^ 2 * (D * Z)) := by
        gcongr
      _ = a ^ 2 * M ^ 2 * (10 * ε ^ 3 * G + 10 * Q * ε ^ 2 * H + 5 * D * ε ^ 2 * Z) := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h₁ := mul_le_mul_of_nonneg_right hε₃ (by positivity : 0 ≤ 10 * G)
        have h₂ := mul_le_mul_of_nonneg_right hε₂ (by positivity : 0 ≤ 10 * Q * H)
        have h₃ := mul_le_mul_of_nonneg_right hε₂ (by positivity : 0 ≤ 5 * D * Z)
        nlinarith only [h₁, h₂, h₃]
  have hBq : |b₁ * q₁ - b₂ * q₂| ≤ 2 * G * (a * M * ε) + Q * a * M * H := by
    apply (abs_product_sub_le b₁ b₂ q₁ q₂).trans
    calc
      _ ≤ (2 * G) * (a * M * ε) + 1 * (Q * a * M * H) := by gcongr
      _ = _ := by ring
  have hBq₂ : |b₂ * q₂| ≤ a * M * ε := by
    rw [abs_mul]
    calc
      _ ≤ 1 * (a * M * ε) := by gcongr
      _ = _ := by ring
  have hv₁ : ‖3 * z₁ + p₁‖ ≤ 4 * M := by
    calc
      _ ≤ 3 * ‖z₁‖ + ‖p₁‖ := by simpa only [norm_mul, hthree] using norm_add_le (3 * z₁) p₁
      _ ≤ 3 * ε + M := by gcongr
      _ ≤ _ := by linarith only [hεM]
  have hδv : ‖(3 * z₁ + p₁) - (3 * z₂ + p₂)‖ ≤ 3 * D * Z + M * F := by
    rw [show (3 * z₁ + p₁) - (3 * z₂ + p₂) = 3 * (z₁ - z₂) + (p₁ - p₂) by ring]
    calc
      _ ≤ 3 * ‖z₁ - z₂‖ + ‖p₁ - p₂‖ := by
        simpa only [norm_mul, hthree] using norm_add_le (3 * (z₁ - z₂)) (p₁ - p₂)
      _ ≤ _ := by
        convert add_le_add (mul_le_mul_of_nonneg_left hδz (by norm_num : (0 : ℝ) ≤ 3)) hδp using 1;
            ring
  have hsecond : ‖c * b₁ * q₁ * (3 * z₁ + p₁) - c * b₂ * q₂ * (3 * z₂ + p₂)‖ ≤
      a ^ 2 * M ^ 2 * (8 * ε * G + 4 * Q * H + 3 * D * Z + ε * F) := by
    have heq : c * b₁ * q₁ * (3 * z₁ + p₁) - c * b₂ * q₂ * (3 * z₂ + p₂) =
        c * ((((b₁ * q₁ : ℝ) : ℂ) * (3 * z₁ + p₁)) -
          (((b₂ * q₂ : ℝ) : ℂ) * (3 * z₂ + p₂))) := by push_cast; ring
    rw [heq, norm_mul]
    have hn := norm_em_product_sub_le ((b₁ * q₁ : ℝ) : ℂ) ((b₂ * q₂ : ℝ) : ℂ)
      (3 * z₁ + p₁) (3 * z₂ + p₂)
    rw [← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs] at hn
    calc
      _ ≤ a * (|b₁ * q₁ - b₂ * q₂| * ‖3 * z₁ + p₁‖ +
          |b₂ * q₂| * ‖(3 * z₁ + p₁) - (3 * z₂ + p₂)‖) := by gcongr
      _ ≤ a * ((2 * G * (a * M * ε) + Q * a * M * H) * (4 * M) +
          (a * M * ε) * (3 * D * Z + M * F)) := by gcongr
      _ = a ^ 2 * M ^ 2 * (8 * ε * G + 4 * Q * H + ε * F) +
          (3 * a ^ 2 * M * D * Z) * ε := by ring
      _ ≤ a ^ 2 * M ^ 2 * (8 * ε * G + 4 * Q * H + ε * F) +
          (3 * a ^ 2 * M * D * Z) * M := by gcongr
      _ = _ := by ring
  have him₁ : |(starRingEnd ℂ p₁ * z₁).im| ≤ M * ε :=
    (Complex.abs_im_le_norm _).trans (by rw [norm_mul, RCLike.norm_conj]; gcongr)
  have hδim : |(starRingEnd ℂ p₁ * z₁).im - (starRingEnd ℂ p₂ * z₂).im| ≤
      M * (D * Z) + (M * F) * ε :=
    (abs_im_scalar_current_sub_le p₁ p₂ z₁ z₂).trans (by gcongr)
  have hBφ : ‖(b₁ : ℂ) * p₁ - (b₂ : ℂ) * p₂‖ ≤ 2 * G * M + M * F := by
    have hn := norm_em_product_sub_le (b₁ : ℂ) (b₂ : ℂ) p₁ p₂
    rw [← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs] at hn
    calc
      _ ≤ |b₁ - b₂| * ‖p₁‖ + |b₂| * ‖p₁ - p₂‖ := hn
      _ ≤ (2 * G) * M + 1 * (M * F) := by gcongr
      _ = _ := by ring
  have hBφ₂ : ‖(b₂ : ℂ) * p₂‖ ≤ M := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ 1 * M := by gcongr
      _ = _ := by ring
  have hthird :
      ‖d * b₁ * p₁ * (((starRingEnd ℂ p₁ * z₁).im : ℝ) : ℂ) -
        d * b₂ * p₂ * (((starRingEnd ℂ p₂ * z₂).im : ℝ) : ℂ)‖ ≤
      a ^ 2 * M ^ 2 * (2 * ε * G + D * Z + 2 * ε * F) := by
    rw [show d * b₁ * p₁ * (((starRingEnd ℂ p₁ * z₁).im : ℝ) : ℂ) -
        d * b₂ * p₂ * (((starRingEnd ℂ p₂ * z₂).im : ℝ) : ℂ) =
      d * (((b₁ : ℂ) * p₁) * (((starRingEnd ℂ p₁ * z₁).im : ℝ) : ℂ) -
        ((b₂ : ℂ) * p₂) * (((starRingEnd ℂ p₂ * z₂).im : ℝ) : ℂ)) by ring, norm_mul]
    have hn := norm_em_product_sub_le ((b₁ : ℂ) * p₁) ((b₂ : ℂ) * p₂)
      (((starRingEnd ℂ p₁ * z₁).im : ℝ) : ℂ) (((starRingEnd ℂ p₂ * z₂).im : ℝ) : ℂ)
    rw [← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs] at hn
    calc
      _ ≤ a ^ 2 * (‖(b₁ : ℂ) * p₁ - (b₂ : ℂ) * p₂‖ * |(starRingEnd ℂ p₁ * z₁).im| +
          ‖(b₂ : ℂ) * p₂‖ * |(starRingEnd ℂ p₁ * z₁).im - (starRingEnd ℂ p₂ * z₂).im|) := by
        gcongr
      _ ≤ a ^ 2 * ((2 * G * M + M * F) * (M * ε) + M * (M * (D * Z) + (M * F) * ε)) := by
        gcongr
      _ = _ := by ring
  have h20 : 20 ≤ C := by dsimp [C]; linarith only [hQ, hD]
  have h14 : 14 * Q ≤ C := by dsimp [C]; linarith only [hQ, hD]
  have h9 : 9 * D ≤ C := by dsimp [C]; linarith only [hQ, hD]
  have h3 : 3 ≤ C := by dsimp [C]; linarith only [hQ, hD]
  have hrows : (20 * ε * G + 14 * Q * H + 9 * D * Z + 3 * ε * F) ≤
      C * (H + Z + ε * G + ε * F) := by
    have h₁ := mul_le_mul_of_nonneg_right h20 (mul_nonneg hε hG)
    have h₂ := mul_le_mul_of_nonneg_right h14 hH
    have h₃ := mul_le_mul_of_nonneg_right h9 hZ
    have h₄ := mul_le_mul_of_nonneg_right h3 (mul_nonneg hε hF)
    nlinarith only [h₁, h₂, h₃, h₄]
  have heq :
      (5 * b₁ * (q₁ : ℂ) ^ 2 * z₁ + c * b₁ * q₁ * (3 * z₁ + p₁) +
          d * b₁ * p₁ * (((starRingEnd ℂ p₁ * z₁).im : ℝ) : ℂ)) -
        (5 * b₂ * (q₂ : ℂ) ^ 2 * z₂ + c * b₂ * q₂ * (3 * z₂ + p₂) +
          d * b₂ * p₂ * (((starRingEnd ℂ p₂ * z₂).im : ℝ) : ℂ)) =
      (5 * b₁ * (q₁ : ℂ) ^ 2 * z₁ - 5 * b₂ * (q₂ : ℂ) ^ 2 * z₂) +
        (c * b₁ * q₁ * (3 * z₁ + p₁) - c * b₂ * q₂ * (3 * z₂ + p₂)) +
        (d * b₁ * p₁ * (((starRingEnd ℂ p₁ * z₁).im : ℝ) : ℂ) -
          d * b₂ * p₂ * (((starRingEnd ℂ p₂ * z₂).im : ℝ) : ℂ)) := by ring
  rw [heq]
  calc
    _ ≤ (‖5 * b₁ * (q₁ : ℂ) ^ 2 * z₁ - 5 * b₂ * (q₂ : ℂ) ^ 2 * z₂‖ +
        ‖c * b₁ * q₁ * (3 * z₁ + p₁) - c * b₂ * q₂ * (3 * z₂ + p₂)‖) +
        ‖d * b₁ * p₁ * (((starRingEnd ℂ p₁ * z₁).im : ℝ) : ℂ) -
          d * b₂ * p₂ * (((starRingEnd ℂ p₂ * z₂).im : ℝ) : ℂ)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ a ^ 2 * M ^ 2 * (10 * ε * G + 10 * Q * H + 5 * D * Z) +
        a ^ 2 * M ^ 2 * (8 * ε * G + 4 * Q * H + 3 * D * Z + ε * F) +
        a ^ 2 * M ^ 2 * (2 * ε * G + D * Z + 2 * ε * F) :=
      add_le_add (add_le_add hfirst hsecond) hthird
    _ = a ^ 2 * M ^ 2 * (20 * ε * G + 14 * Q * H + 9 * D * Z + 3 * ε * F) := by ring
    _ ≤ a ^ 2 * M ^ 2 * (C * (H + Z + ε * G + ε * F)) :=
      mul_le_mul_of_nonneg_left hrows (by positivity)
    _ = _ := by ring

end EmcsfAcExtension.Local.Stab
