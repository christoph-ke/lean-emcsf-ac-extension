module

public import EmcsfAcExtension.Local.Defs.Setting

/-! # Integrating the pure geometric derivative subtraction

The three continuous majorants are measurable before their positive
integrals are separated. Finiteness is supplied by the geometric and
quadratic budgets, rather than assumed for the derivative difference.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- A pointwise pure-derivative subtraction integrates with the exact
coefficients one. The explicit scalar `G≥0` and continuous majorants
are the only analytic inputs; there is no finite-integral premise. -/
theorem stab_pure_derivative_section_integral_le
    {a b G : ℝ} {d₁ d₂ L₁ L₂ F₁ F₂ : ℝ → ℝ} (hG : 0 ≤ G)
    (cL₁ : ContinuousOn L₁ (Icc a b)) (cL₂ : ContinuousOn L₂ (Icc a b))
    (cF₁ : ContinuousOn F₁ (Icc a b)) (cF₂ : ContinuousOn F₂ (Icc a b))
    (hpoint : ∀ t ∈ Icc a b, |d₁ t - d₂ t| ≤
      |L₁ t - L₂ t| + |F₁ t - F₂ t| + G * (|L₂ t| + |F₂ t|)) :
    (∫⁻ t in Icc a b, ‖d₁ t - d₂ t‖ₑ) ≤
      (∫⁻ t in Icc a b, ‖L₁ t - L₂ t‖ₑ) +
      (∫⁻ t in Icc a b, ‖F₁ t - F₂ t‖ₑ) +
      ENNReal.ofReal G * ((∫⁻ t in Icc a b, ‖L₂ t‖ₑ) +
        (∫⁻ t in Icc a b, ‖F₂ t‖ₑ)) := by
  have mL := (cL₁.sub cL₂).enorm.aemeasurable (μ := volume) measurableSet_Icc
  have mF := (cF₁.sub cF₂).enorm.aemeasurable (μ := volume) measurableSet_Icc
  have mL₂ := cL₂.enorm.aemeasurable (μ := volume) measurableSet_Icc
  have hp : ∀ t ∈ Icc a b, ‖d₁ t - d₂ t‖ₑ ≤
      ‖L₁ t - L₂ t‖ₑ + ‖F₁ t - F₂ t‖ₑ +
        ENNReal.ofReal G * (‖L₂ t‖ₑ + ‖F₂ t‖ₑ) := by
    intro t ht
    have hh := ENNReal.ofReal_le_ofReal (hpoint t ht)
    rw [ENNReal.ofReal_add (add_nonneg (abs_nonneg _) (abs_nonneg _))
      (mul_nonneg hG (add_nonneg (abs_nonneg _) (abs_nonneg _))),
      ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _), ENNReal.ofReal_mul hG,
      ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)] at hh
    simpa only [Real.enorm_eq_ofReal_abs] using! hh
  have hi := setLIntegral_mono' (μ := (volume : Measure ℝ)) measurableSet_Icc hp
  apply hi.trans_eq
  rw [lintegral_add_left' (f := fun t => ‖L₁ t - L₂ t‖ₑ + ‖F₁ t - F₂ t‖ₑ)
    (g := fun t => ENNReal.ofReal G * (‖L₂ t‖ₑ + ‖F₂ t‖ₑ)) (mL.add mF),
    lintegral_add_left' (f := fun t => ‖L₁ t - L₂ t‖ₑ) (g := fun t => ‖F₁ t - F₂ t‖ₑ) mL,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_add_left' (f := fun t => ‖L₂ t‖ₑ) (g := fun t => ‖F₂ t‖ₑ) mL₂]

end EmcsfAcExtension.Local
