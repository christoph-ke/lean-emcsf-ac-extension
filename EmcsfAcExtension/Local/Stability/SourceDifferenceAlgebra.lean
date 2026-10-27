module

public import Mathlib

/-! # Algebra of the scalar curvature primitive differences

The primitive contains both conjugate bilinear terms. The telescoping
identity keeps the radius, scalar ratio and derivative differences separate.
-/

public section

open MeasureTheory Set Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- Extended-norm version of the raw three-factor subtraction.
All three coefficients are exactly one, and infinite envelope majorants
can subsequently be substituted without converting them to real values. -/
theorem enorm_primitive_integrand_sub_le (r₁ r₂ : ℝ) (y₁ y₂ j₁ j₂ : ℂ) :
    ‖(r₁ : ℂ) * starRingEnd ℂ y₁ * j₁ - (r₂ : ℂ) * starRingEnd ℂ y₂ * j₂‖ₑ ≤
      ‖(r₁ : ℂ)‖ₑ * ‖y₁ - y₂‖ₑ * ‖j₁‖ₑ +
        ‖(r₁ : ℂ)‖ₑ * ‖y₂‖ₑ * ‖j₁ - j₂‖ₑ +
        ‖((r₁ - r₂ : ℝ) : ℂ)‖ₑ * ‖y₂‖ₑ * ‖j₂‖ₑ := by
  have heq : (r₁ : ℂ) * starRingEnd ℂ y₁ * j₁ - (r₂ : ℂ) * starRingEnd ℂ y₂ * j₂ =
      (r₁ : ℂ) * starRingEnd ℂ (y₁ - y₂) * j₁ +
        (r₁ : ℂ) * starRingEnd ℂ y₂ * (j₁ - j₂) +
        ((r₁ - r₂ : ℝ) : ℂ) * starRingEnd ℂ y₂ * j₂ := by
    simp only [map_sub, ofReal_sub]
    ring
  rw [heq]
  apply (enorm_add_le _ _).trans
  apply (add_le_add (enorm_add_le _ _) le_rfl).trans_eq
  simp only [enorm_mul, RCLike.enorm_conj]

end EmcsfAcExtension.Local.Stab
