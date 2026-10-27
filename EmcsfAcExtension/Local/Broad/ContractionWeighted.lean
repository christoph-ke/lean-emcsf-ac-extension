module

public import EmcsfAcExtension.Local.Broad.ContractionIntegrals

/-! # Nonnegative radial domination for scalar coefficients

The weighted electric square is controlled by its radial moment. All
integrability conclusions precede the corresponding real estimates.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local.Broad

/-- A quadratic radial majorant cancels the singular radial weight.
The coefficient is exactly the supplied `B`, uniformly in all traces. -/
theorem weighted_quadratic_integral_of_bounds {a b B R : ℝ} {w r f : ℝ → ℝ}
    (hab : a ≤ b) (_hB : 0 ≤ B)
    (cw : ContinuousOn w (Icc a b)) (cr : ContinuousOn r (Icc a b))
    (hf : AEStronglyMeasurable f (volume.restrict (Icc a b)))
    (hw : ∀ x ∈ Icc a b, 0 ≤ w x) (hr : ∀ x ∈ Icc a b, 0 ≤ r x)
    (hbound : ∀ x ∈ Icc a b, 0 ≤ f x ∧ f x ≤ B * r x ^ 2)
    (hmom : (∫ x in a..b, w x * r x) = R ^ 2 / 2) :
    IntervalIntegrable (fun x => w x / r x * f x) volume a b ∧
      (∫ x in a..b, w x / r x * f x) ≤ B * R ^ 2 / 2 := by
  have hm := ((cw.aestronglyMeasurable measurableSet_Icc).div₀
    (cr.aestronglyMeasurable measurableSet_Icc)).mul hf
  obtain ⟨ii, hi⟩ := integral_of_nonneg_le_majorant hab hm
    (fun x hx => mul_nonneg (div_nonneg (hw x hx) (hr x hx)) (hbound x hx).1)
    ((ContinuousOn.intervalIntegrable_of_Icc hab (cw.mul cr)).const_mul B)
    (fun x hx => by
      change w x / r x * f x ≤ B * (w x * r x)
      by_cases hz : r x = 0
      · simp [hz]
      calc
        _ ≤ w x / r x * (B * r x ^ 2) :=
          mul_le_mul_of_nonneg_left (hbound x hx).2 (div_nonneg (hw x hx) (hr x hx))
        _ = _ := by field_simp)
  refine ⟨ii, hi.trans_eq ?_⟩
  change (∫ x in a..b, B * (w x * r x)) = B * R ^ 2 / 2
  rw [intervalIntegral.integral_const_mul, hmom]
  ring

/-- Changing from the second radial weight to the first costs their
comparison factor `W`. This statement is uniform in all budgets and traces. -/
theorem weighted_integral_of_weight_comparison {a b W A : ℝ} {d₁ d₂ f : ℝ → ℝ}
    (hab : a ≤ b) (hW : 0 ≤ W)
    (hd₁ : AEStronglyMeasurable d₁ (volume.restrict (Icc a b)))
    (hf : AEStronglyMeasurable f (volume.restrict (Icc a b)))
    (hd0 : ∀ x ∈ Icc a b, 0 ≤ d₁ x) (hf0 : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hcomp : ∀ x ∈ Icc a b, d₁ x ≤ W * d₂ x)
    (ii : IntervalIntegrable (fun x => d₂ x * f x) volume a b)
    (hA : (∫ x in a..b, d₂ x * f x) ≤ A) :
    IntervalIntegrable (fun x => d₁ x * f x) volume a b ∧
      (∫ x in a..b, d₁ x * f x) ≤ W * A := by
  obtain ⟨ij, hj⟩ := integral_of_nonneg_le_majorant hab (hd₁.mul hf)
    (fun x hx => mul_nonneg (hd0 x hx) (hf0 x hx)) (ii.const_mul W)
    (fun x hx => by
      change d₁ x * f x ≤ W * (d₂ x * f x)
      exact (mul_le_mul_of_nonneg_right (hcomp x hx) (hf0 x hx)).trans_eq (by ring))
  refine ⟨ij, hj.trans ?_⟩
  change (∫ x in a..b, W * (d₂ x * f x)) ≤ W * A
  rw [intervalIntegral.integral_const_mul]
  exact mul_le_mul_of_nonneg_left hA hW

end EmcsfAcExtension.Local.Broad
