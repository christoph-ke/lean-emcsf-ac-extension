module

public import EmcsfAcExtension.Infra.Triangle

/-! # Integrating four measurable source majorants

Only the majorants need measurability. The source can be estimated first,
with its integrability and area budget obtained as conclusions.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- Four measurable nonnegative majorants can be integrated in the incoming
transport order and then in product measure. All coefficients are explicit,
with exact numerical constants `1` and no hidden parameter dependence. -/
theorem source_area_le_four_majorants {T : ℝ}
    {F K₁ K₂ K₃ K₄ : ℝ × ℝ → ℝ≥0∞} {a₁ a₂ a₃ a₄ : ℝ≥0∞}
    (hK₁ : Measurable K₁) (hK₂ : Measurable K₂)
    (hK₃ : Measurable K₃) (hK₄ : Measurable K₄)
    (hF : ∀ p ∈ triangle 0 T,
      F p ≤ a₁ * K₁ p + a₂ * K₂ p + a₃ * K₃ p + a₄ * K₄ p) :
    (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, F (u, v)) ≤
      a₁ * (∫⁻ p in triangle 0 T, K₁ p ∂(volume.prod volume)) +
        a₂ * (∫⁻ p in triangle 0 T, K₂ p ∂(volume.prod volume)) +
        a₃ * (∫⁻ p in triangle 0 T, K₃ p ∂(volume.prod volume)) +
        a₄ * (∫⁻ p in triangle 0 T, K₄ p ∂(volume.prod volume)) := by
  have hm₁ : Measurable (fun p => a₁ * K₁ p) := measurable_const.mul hK₁
  have hm₂ : Measurable (fun p => a₂ * K₂ p) := measurable_const.mul hK₂
  have hm₃ : Measurable (fun p => a₃ * K₃ p) := measurable_const.mul hK₃
  have hm₄ : Measurable (fun p => a₄ * K₄ p) := measurable_const.mul hK₄
  have hm₁₂ : Measurable (fun p => a₁ * K₁ p + a₂ * K₂ p) := by fun_prop
  have hm₁₂₃ : Measurable (fun p => a₁ * K₁ p + a₂ * K₂ p + a₃ * K₃ p) := by fun_prop
  calc
    _ ≤ ∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v,
        a₁ * K₁ (u, v) + a₂ * K₂ (u, v) + a₃ * K₃ (u, v) + a₄ * K₄ (u, v) := by
      apply setLIntegral_mono' measurableSet_Icc
      intro v hv
      apply setLIntegral_mono' measurableSet_Icc
      intro u hu
      exact hF (u, v) ⟨hu.1, hu.2, hv.2⟩
    _ = ∫⁻ p in triangle 0 T,
        a₁ * K₁ p + a₂ * K₂ p + a₃ * K₃ p + a₄ * K₄ p ∂(volume.prod volume) :=
      (lintegral_triangle_eq_lintegral_lintegral_symm
        (((hm₁.add hm₂).add hm₃).add hm₄)).symm
    _ = _ := by
      rw [lintegral_add_left hm₁₂₃,
        lintegral_add_left hm₁₂, lintegral_add_left hm₁,
        lintegral_const_mul _ hK₁, lintegral_const_mul _ hK₂,
        lintegral_const_mul _ hK₃, lintegral_const_mul _ hK₄]

/-- A continuous field on the triangle has a measurable zero-extended
norm. No regularity of the field outside that triangle is assumed. -/
theorem measurable_triangle_enorm_indicator {E : Type*} [NormedAddCommGroup E]
    {a b : ℝ} {f : ℝ × ℝ → E} (hf : ContinuousOn f (triangle a b)) :
    Measurable ((triangle a b).indicator (fun p => ‖f p‖ₑ)) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact hf.enorm.measurable_piecewise continuousOn_const (measurableSet_triangle a b)

/-- Incoming area equals product area of a measurable zero extension.
Values outside the triangle play no role in either expression. -/
theorem incoming_area_eq_product_of_indicator {T : ℝ} {F : ℝ × ℝ → ℝ≥0∞}
    (hF : Measurable ((triangle 0 T).indicator F)) :
    (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, F (u, v)) =
      ∫⁻ p in triangle 0 T, (triangle 0 T).indicator F p ∂(volume.prod volume) := by
  rw [lintegral_triangle_eq_lintegral_lintegral_symm hF]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro v hv
  apply setLIntegral_congr_fun measurableSet_Icc
  intro u hu
  dsimp only
  exact (indicator_of_mem (show (u, v) ∈ triangle 0 T from ⟨hu.1, hu.2, hv.2⟩) F).symm

/-- Add two incoming areas once their zero extensions are measurable.
There is no implicit finiteness requirement; the equality holds in `ℝ≥0∞`. -/
theorem incoming_area_add_of_measurable_indicators {T : ℝ} {F G : ℝ × ℝ → ℝ≥0∞}
    (hF : Measurable ((triangle 0 T).indicator F))
    (hG : Measurable ((triangle 0 T).indicator G)) :
    (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, F (u, v) + G (u, v)) =
      (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, F (u, v)) +
        ∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, G (u, v) := by
  have hsum : Measurable (fun p => (triangle 0 T).indicator F p +
      (triangle 0 T).indicator G p) := hF.fun_add hG
  calc
    _ = ∫⁻ p in triangle 0 T, ((triangle 0 T).indicator F p +
        (triangle 0 T).indicator G p) ∂(volume.prod volume) := by
      rw [lintegral_triangle_eq_lintegral_lintegral_symm hsum]
      apply setLIntegral_congr_fun measurableSet_Icc
      intro v hv
      apply setLIntegral_congr_fun measurableSet_Icc
      intro u hu
      dsimp only
      simp only [indicator_of_mem (show (u, v) ∈ triangle 0 T from ⟨hu.1, hu.2, hv.2⟩)]
    _ = _ := by
      rw [lintegral_add_left hF,
        ← incoming_area_eq_product_of_indicator hF, ← incoming_area_eq_product_of_indicator hG]

/-- Exchange the two characteristic integration orders for a measurable
zero extension. This equality holds for extended integrals without finiteness. -/
theorem outgoing_area_eq_incoming_of_measurable_indicator {T : ℝ} {F : ℝ × ℝ → ℝ≥0∞}
    (hF : Measurable ((triangle 0 T).indicator F)) :
    (∫⁻ u in Icc 0 T, ∫⁻ v in Icc u T, F (u, v)) =
      ∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, F (u, v) := by
  calc
    _ = ∫⁻ p in triangle 0 T, (triangle 0 T).indicator F p ∂(volume.prod volume) := by
      rw [lintegral_triangle_eq_lintegral_lintegral hF]
      apply setLIntegral_congr_fun measurableSet_Icc
      intro u hu
      apply setLIntegral_congr_fun measurableSet_Icc
      intro v hv
      dsimp only
      exact (indicator_of_mem (show (u, v) ∈ triangle 0 T from ⟨hu.1, hv.1, hv.2⟩) F).symm
    _ = _ := (incoming_area_eq_product_of_indicator hF).symm

end EmcsfAcExtension.Local.Stab
