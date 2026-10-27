/- Copyright (c) 2026. All rights reserved. -/

module

public import EmcsfAcExtension.Infra.Hardy

/-!
# Monotone weighted averages

Nonnegative monotone functions have nonnegative monotone radial averages.
Their derivative controls the weighted deviation, including intervals on which
the radius is zero. This is the scalar majorant for continuous BV Hardy bounds.
-/

public section

open Set MeasureTheory Filter

namespace EmcsfAcExtension

/-- Multiplying an integrable weight by a nonnegative monotone function on a
compact interval preserves integrability. -/
theorem intervalIntegrable_weight_mul_monotone {w F : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hw : IntervalIntegrable w volume a b)
    (hF : MonotoneOn F (Icc a b)) (hF0 : ∀ x ∈ Icc a b, 0 ≤ F x) :
    IntervalIntegrable (fun x => w x * F x) volume a b := by
  have hFi : IntervalIntegrable F volume a b :=
    (by simpa only [uIcc_of_le hab] using hF : MonotoneOn F (uIcc a b)).intervalIntegrable
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab] at hw hFi ⊢
  refine hw.mul_bdd (c := F b) hFi.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (hF0 x hx)]
  exact hF hx (right_mem_Icc.mpr hab) hx.2

/-- A nonnegative function has a nonnegative radial average for nonnegative weights. -/
theorem radialAverage_nonneg {w F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x) (hF0 : ∀ x ∈ Icc a b, 0 ≤ F x) :
    0 ≤ radialAverage w F a b := by
  apply mul_nonneg
  · exact inv_nonneg.mpr (intervalIntegral.integral_nonneg hab hw0)
  · exact intervalIntegral.integral_nonneg hab (fun x hx => mul_nonneg (hw0 x hx) (hF0 x hx))

/-- A nonnegative monotone function bounds its radial average from above. -/
theorem radialAverage_le_of_monotoneOn {w F : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hw : IntervalIntegrable w volume a b)
    (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x)
    (hF : MonotoneOn F (Icc a b)) (hF0 : ∀ x ∈ Icc a b, 0 ≤ F x) :
    radialAverage w F a b ≤ F b := by
  have hWF := intervalIntegrable_weight_mul_monotone hab hw hF hF0
  have hr0 : 0 ≤ ∫ s in a..b, w s := intervalIntegral.integral_nonneg hab hw0
  rcases eq_or_lt_of_le hr0 with hr | hr
  · simp only [radialAverage, ← hr, inv_zero, zero_smul]
    exact hF0 b (right_mem_Icc.mpr hab)
  · change (∫ s in a..b, w s)⁻¹ * (∫ s in a..b, w s * F s) ≤ F b
    rw [← div_eq_inv_mul, div_le_iff₀ hr]
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hab hWF (hw.const_mul (F b))
      (fun x hx => by
        rw [mul_comm (F b)]
        exact mul_le_mul_of_nonneg_left (hF hx (right_mem_Icc.mpr hab) hx.2) (hw0 x hx))

/-- The radial averages of a nonnegative monotone function are monotone,
without any strict positivity assumption on the weight or its primitive. -/
theorem monotoneOn_radialAverage {w F : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hw : IntervalIntegrable w volume a b)
    (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x)
    (hF : MonotoneOn F (Icc a b)) (hF0 : ∀ x ∈ Icc a b, 0 ≤ F x) :
    MonotoneOn (radialAverage w F a) (Icc a b) := by
  have hWF := intervalIntegrable_weight_mul_monotone hab hw hF hF0
  have hRmono := monotoneOn_integral_weight hw hw0
  intro x hx y hy hxy
  have hax : uIcc a x ⊆ uIcc a b := uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc hx)
  have hxy' : uIcc x y ⊆ uIcc a b := uIcc_subset_uIcc (Icc_subset_uIcc hx) (Icc_subset_uIcc hy)
  have hrx : 0 ≤ ∫ s in a..x, w s := intervalIntegral.integral_nonneg hx.1
    (fun t ht => hw0 t ⟨ht.1, ht.2.trans hx.2⟩)
  rcases eq_or_lt_of_le hrx with hrx | hrx
  · change radialAverage w F a x ≤ radialAverage w F a y
    simp only [radialAverage, ← hrx, inv_zero, zero_smul]
    exact radialAverage_nonneg hy.1
      (fun t ht => hw0 t ⟨ht.1, ht.2.trans hy.2⟩)
      (fun t ht => hF0 t ⟨ht.1, ht.2.trans hy.2⟩)
  · have hry : 0 < ∫ t in a..y, w t := hrx.trans_le (hRmono hx hy hxy)
    have hMx : radialAverage w F a x ≤ F x :=
      radialAverage_le_of_monotoneOn hx.1 (hw.mono_set hax)
        (fun t ht => hw0 t ⟨ht.1, ht.2.trans hx.2⟩)
        (hF.mono (Icc_subset_Icc le_rfl hx.2))
        (fun t ht => hF0 t ⟨ht.1, ht.2.trans hx.2⟩)
    have hlocal := intervalIntegral.integral_mono_on hxy
      ((hw.mono_set hxy').const_mul (radialAverage w F a x)) (hWF.mono_set hxy')
      (fun t ht => by
        rw [mul_comm (w t)]
        exact mul_le_mul_of_nonneg_right
          (hMx.trans (hF hx ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩ ht.1))
          (hw0 t ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩))
    simp only [intervalIntegral.integral_const_mul] at hlocal
    have hN := intervalIntegral.integral_add_adjacent_intervals
      (hWF.mono_set hax) (hWF.mono_set hxy')
    have hR := intervalIntegral.integral_add_adjacent_intervals
      (hw.mono_set hax) (hw.mono_set hxy')
    have hcancel : radialAverage w F a x * (∫ t in a..x, w t) = ∫ t in a..x, w t * F t := by
      dsimp only [radialAverage, smul_eq_mul]
      field_simp
    change radialAverage w F a x ≤ (∫ t in a..y, w t)⁻¹ * (∫ t in a..y, w t * F t)
    rw [← div_eq_inv_mul, le_div_iff₀ hry]
    rw [← hR, mul_add, hcancel, ← hN]
    exact add_le_add le_rfl hlocal

end EmcsfAcExtension
