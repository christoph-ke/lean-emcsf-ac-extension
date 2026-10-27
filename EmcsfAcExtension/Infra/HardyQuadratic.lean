/- Copyright (c) 2026. All rights reserved. -/

module

public import EmcsfAcExtension.Infra.HardyBV

/-!
# Quadratic consequences of radial Hardy bounds

A pointwise bound `M` at positive radius converts the linear Hardy integral
into the quadratic one
with constant exactly `M`. The statements also establish quadratic integrability.
-/

public section

open Set MeasureTheory Filter

namespace EmcsfAcExtension

variable {E : Type*} [NormedAddCommGroup E]

/-- Multiplication by a bounded norm converts a nonnegative weighted L¹ bound
into a weighted quadratic bound, for any measure. -/
theorem integrable_and_integral_weight_mul_norm_sq_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {k : α → ℝ} {f : α → E} {M : ℝ}
    (hf : AEStronglyMeasurable f μ) (hk : ∀ᵐ x ∂μ, 0 ≤ k x)
    (hM : ∀ᵐ x ∂μ, k x ≠ 0 → ‖f x‖ ≤ M) (hi : Integrable (fun x => k x * ‖f x‖) μ) :
    Integrable (fun x => k x * ‖f x‖ ^ 2) μ ∧
    (∫ x, k x * ‖f x‖ ^ 2 ∂μ) ≤ M * ∫ x, k x * ‖f x‖ ∂μ := by
  have hbound : ∀ᵐ x ∂μ, k x * ‖f x‖ ^ 2 ≤ M * (k x * ‖f x‖) := by
    filter_upwards [hk, hM] with x hkx hMx
    by_cases hk0 : k x = 0
    · simp only [hk0, zero_mul, mul_zero, le_refl]
    calc
      _ = (k x * ‖f x‖) * ‖f x‖ := by ring
      _ ≤ (k x * ‖f x‖) * M :=
        mul_le_mul_of_nonneg_left (hMx hk0) (mul_nonneg hkx (norm_nonneg _))
      _ = _ := by ring
  have hsq : Integrable (fun x => k x * ‖f x‖ ^ 2) μ := by
    refine (hi.const_mul M).mono' ?_ ?_
    · convert hi.aestronglyMeasurable.mul hf.norm using 1
      ext x
      simp only [Pi.mul_apply]
      ring
    · filter_upwards [hk, hbound] with x hkx hx
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hkx (sq_nonneg _))]
      exact hx
  refine ⟨hsq, ?_⟩
  rw [← integral_const_mul]
  exact integral_mono_ae hsq (hi.const_mul M) hbound

variable [NormedSpace ℝ E] [CompleteSpace E]

end EmcsfAcExtension
