module

public import EmcsfAcExtension.Infra.Triangle
import EmcsfAcExtension.Local.Stability.SourceDifferenceArea

/-! # Finite incoming norm area implies triangle integrability

This bridge supplies almost-everywhere integrable characteristic forcings
from the Borel representatives and the independently proved area estimates.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- The norm of a measurable zero extension is itself the measurable
zero extension of the norm, with no boundary regularity assumption. -/
theorem measurable_triangle_enorm_of_measurable_indicator {T : ℝ} {f : ℝ × ℝ → ℂ}
    (hf : Measurable ((triangle 0 T).indicator f)) :
    Measurable ((triangle 0 T).indicator (fun p => ‖f p‖ₑ)) := by
  convert hf.enorm using 1
  funext p
  by_cases hp : p ∈ triangle 0 T
  · simp only [indicator_of_mem hp]
  · simp only [indicator_of_notMem hp, enorm_zero]

/-- Subtraction commutes with measurable zero extensions on the triangle. -/
theorem measurable_triangle_sub {T : ℝ} {f g : ℝ × ℝ → ℂ}
    (hf : Measurable ((triangle 0 T).indicator f))
    (hg : Measurable ((triangle 0 T).indicator g)) :
    Measurable ((triangle 0 T).indicator (fun p => f p - g p)) := by
  convert hf.fun_sub hg using 1
  funext p
  by_cases hp : p ∈ triangle 0 T
  · simp only [indicator_of_mem hp]
  · simp only [indicator_of_notMem hp, sub_self]

/-- A measurable zero extension and finite incoming norm area imply
integrability on the triangle. Fubini then supplies the actual integrable
forcing on almost every characteristic in either orientation. -/
theorem integrableOn_triangle_of_incoming_area_ne_top {T : ℝ} {f : ℝ × ℝ → ℂ}
    (hf : Measurable ((triangle 0 T).indicator f))
    (hfinite : (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, ‖f (u, v)‖ₑ) ≠ ⊤) :
    IntegrableOn f (triangle 0 T) (volume.prod volume) := by
  have hnorm := measurable_triangle_enorm_of_measurable_indicator hf
  have harea := incoming_area_eq_product_of_indicator hnorm
  have heq : (∫⁻ p in triangle 0 T, ‖f p‖ₑ ∂(volume.prod volume)) =
      ∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, ‖f (u, v)‖ₑ := by
    rw [harea]
    apply setLIntegral_congr_fun (measurableSet_triangle 0 T)
    intro p hp
    exact (indicator_of_mem hp (fun p => ‖f p‖ₑ)).symm
  have hi : Integrable ((triangle 0 T).indicator f) (volume.prod volume) := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have hnormeq : (fun p => ‖(triangle 0 T).indicator f p‖ₑ) =
        (triangle 0 T).indicator (fun p => ‖f p‖ₑ) := by
      funext p
      by_cases hp : p ∈ triangle 0 T
      · simp only [indicator_of_mem hp]
      · simp only [indicator_of_notMem hp, enorm_zero]
    rw [hnormeq, lintegral_indicator (measurableSet_triangle 0 T), heq]
    exact lt_top_iff_ne_top.mpr hfinite
  exact (integrable_indicator_iff (measurableSet_triangle 0 T)).mp hi

/-- Integrate four measurable complex majorants in the incoming order.
All four coefficients are the exact universal one; the pointwise triangle
inequality is the only hypothesis relating the forcing to its pieces. -/
theorem incoming_area_le_sum4_norm {T : ℝ} {q f₁ f₂ f₃ f₄ : ℝ × ℝ → ℂ}
    (h₁ : Measurable ((triangle 0 T).indicator f₁))
    (h₂ : Measurable ((triangle 0 T).indicator f₂))
    (h₃ : Measurable ((triangle 0 T).indicator f₃))
    (h₄ : Measurable ((triangle 0 T).indicator f₄))
    (hbound : ∀ p ∈ triangle 0 T,
      ‖q p‖ₑ ≤ ‖f₁ p‖ₑ + ‖f₂ p‖ₑ + ‖f₃ p‖ₑ + ‖f₄ p‖ₑ) :
    (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, ‖q (u, v)‖ₑ) ≤
      (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, ‖f₁ (u, v)‖ₑ) +
      (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, ‖f₂ (u, v)‖ₑ) +
      (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, ‖f₃ (u, v)‖ₑ) +
      (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, ‖f₄ (u, v)‖ₑ) := by
  have hm₁ := measurable_triangle_enorm_of_measurable_indicator h₁
  have hm₂ := measurable_triangle_enorm_of_measurable_indicator h₂
  have hm₃ := measurable_triangle_enorm_of_measurable_indicator h₃
  have hm₄ := measurable_triangle_enorm_of_measurable_indicator h₄
  have hb := source_area_le_four_majorants (T := T) (a₁ := 1) (a₂ := 1) (a₃ := 1) (a₄ := 1)
    hm₁ hm₂ hm₃ hm₄ (F := fun p => ‖q p‖ₑ)
    (by intro p hp; simpa only [one_mul, indicator_of_mem hp] using hbound p hp)
  simpa only [one_mul, ← incoming_area_eq_product_of_indicator hm₁,
    ← incoming_area_eq_product_of_indicator hm₂, ← incoming_area_eq_product_of_indicator hm₃,
    ← incoming_area_eq_product_of_indicator hm₄] using hb

end EmcsfAcExtension.Local.Stab
