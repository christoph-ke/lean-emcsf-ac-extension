module

public import EmcsfAcExtension.Local.Stability.SourceDifferencePrimitive

/-! # Cancellation of the charged primitive radius scale

A bounded radius-square integrand gains one factor of length on integration.
The inverse-cube exterior coefficient then cancels that full length cube.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local.Stab

/-- Charged curvature primitive comparison on an arbitrary interval.
`C` depends only on the fixed coefficient and integrand constants `B,P`;
it is independent of the interval length, small parameter, amplitudes and
all functions or derivative suprema. No positive lower radius is retained. -/
theorem em_primitive_source_uniform_difference (B P : ℝ) (hB : 0 < B) (hP : 0 < P) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (a b E ε X : ℝ) (f₁ f₂ : ℝ → ℂ) (c₁ c₂ : ℂ),
      a < b → 0 ≤ E → 0 ≤ ε → ε ≤ 1 → 0 ≤ X →
      IntervalIntegrable f₁ volume a b → IntervalIntegrable f₂ volume a b →
      ‖c₁ - c₂‖ ≤ B * X / (b - a) ^ 3 → ‖c₂‖ ≤ 64 * ε / (b - a) ^ 3 →
      (∀ w ∈ Icc a b, ‖f₁ w‖ ≤ 2 * E * ε ^ 2 * (b - a) ^ 2) →
      (∀ w ∈ Icc a b, ‖f₁ w - f₂ w‖ ≤ P * E * (b - a) ^ 2 * X) →
      ‖c₁ * ((∫ w in a..b, f₁ w) + 2 * starRingEnd ℂ (∫ w in a..b, f₁ w)) -
        c₂ * ((∫ w in a..b, f₂ w) + 2 * starRingEnd ℂ (∫ w in a..b, f₂ w))‖ ≤
          C * E * X := by
  refine ⟨3 * (2 * B + 64 * P), by positivity, ?_⟩
  intro a b E ε X f₁ f₂ c₁ c₂ hab hE hε hε₁ hX hf₁ hf₂ hδc hc₂ hnorm hδnorm
  have hd : 0 < b - a := sub_pos.mpr hab
  have hdne := (pow_pos hd 3).ne'
  have hI₁ : (∫ w in a..b, ‖f₁ w‖) ≤ 2 * E * ε ^ 2 * (b - a) ^ 3 := by
    apply (intervalIntegral.integral_mono_on hab.le hf₁.norm intervalIntegrable_const
        hnorm).trans_eq
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hIδ : (∫ w in a..b, ‖f₁ w - f₂ w‖) ≤ P * E * (b - a) ^ 3 * X := by
    apply (intervalIntegral.integral_mono_on hab.le (hf₁.sub hf₂).norm
      intervalIntegrable_const hδnorm).trans_eq
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have h₁ := mul_le_mul hδc hI₁
    (intervalIntegral.integral_nonneg hab.le (fun _ _ => norm_nonneg _)) (by positivity)
  have h₂ := mul_le_mul hc₂ hIδ
    (intervalIntegral.integral_nonneg hab.le (fun _ _ => norm_nonneg _)) (by positivity)
  have hscaled :
      (B * X / (b - a) ^ 3) * (2 * E * ε ^ 2 * (b - a) ^ 3) +
        (64 * ε / (b - a) ^ 3) * (P * E * (b - a) ^ 3 * X) =
      E * X * (2 * B * ε ^ 2 + 64 * P * ε) := by field_simp
  have hε₂ := pow_le_one₀ hε hε₁ (n := 2)
  have hsmall : 2 * B * ε ^ 2 + 64 * P * ε ≤ 2 * B + 64 * P := by
    have h₃ := mul_le_mul_of_nonneg_left hε₂ (by positivity : 0 ≤ 2 * B)
    have h₄ := mul_le_mul_of_nonneg_left hε₁ (by positivity : 0 ≤ 64 * P)
    linarith only [h₃, h₄]
  calc
    _ ≤ 3 * (‖c₁ - c₂‖ * (∫ w in a..b, ‖f₁ w‖) +
        ‖c₂‖ * (∫ w in a..b, ‖f₁ w - f₂ w‖)) :=
      scalar_primitive_source_difference_norm_le hab.le hf₁ hf₂ c₁ c₂
    _ ≤ 3 * (E * X * (2 * B * ε ^ 2 + 64 * P * ε)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 3)
      rw [← hscaled]
      exact add_le_add h₁ h₂
    _ ≤ 3 * (E * X * (2 * B + 64 * P)) := by gcongr
    _ = _ := by ring

end EmcsfAcExtension.Local.Stab
