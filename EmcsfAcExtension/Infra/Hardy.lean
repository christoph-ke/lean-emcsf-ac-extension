/- Copyright (c) 2026. All rights reserved. -/

module

public import EmcsfAcExtension.Infra.AC.Variation
public import EmcsfAcExtension.Infra.AC.Quotient

/-!
# Weighted radial averages

The radius is the primitive of a nonnegative integrable weight. The weighted
average is totalized by zero where that primitive vanishes. Statements involving
its deviation at a point require positive radius; weighted integral statements
use the totalized ratio `w / ρ`.

These estimates supply the radial reconstruction at `charged_SF_new_version.tex:L4595–L4613`.
All numerical constants are universal and independent of the weight and interval.
-/

public section

open Set MeasureTheory Filter

namespace EmcsfAcExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The weighted radial average, with Lean's zero reciprocal at zero radius. -/
@[expose] noncomputable def radialAverage (w : ℝ → ℝ) (f : ℝ → E) (a x : ℝ) : E :=
  (∫ s in a..x, w s)⁻¹ • ∫ s in a..x, w s • f s

/-- The radial average is zero at its base point. -/
@[simp] theorem radialAverage_self (w : ℝ → ℝ) (f : ℝ → E) (a : ℝ) :
    radialAverage w f a a = 0 := by
  simp only [radialAverage, intervalIntegral.integral_same, inv_zero, zero_smul]

/-- The primitive of a nonnegative integrable weight is nondecreasing. -/
theorem monotoneOn_integral_weight {w : ℝ → ℝ} {a b : ℝ}
    (hw : IntervalIntegrable w volume a b) (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x) :
    MonotoneOn (fun x => ∫ s in a..x, w s) (Icc a b) := by
  intro x hx y hy hxy
  have hx' : x ∈ uIcc a b := Icc_subset_uIcc hx
  have hy' : y ∈ uIcc a b := Icc_subset_uIcc hy
  dsimp only
  rw [← sub_nonneg, intervalIntegral.integral_interval_sub_left
    (hw.mono_set (uIcc_subset_uIcc left_mem_uIcc hy'))
    (hw.mono_set (uIcc_subset_uIcc left_mem_uIcc hx'))]
  exact intervalIntegral.integral_nonneg hxy (fun s hs => hw0 s ⟨hx.1.trans hs.1, hs.2.trans hy.2⟩)

/-- Integration by parts identifies the weighted deviation with its derivative moment.
This Banach space version accepts an integrable a.e. derivative density. -/
theorem integral_weight_smul_sub_eq_integral_moment [CompleteSpace E]
    {w : ℝ → ℝ} {f h : ℝ → E} {a b : ℝ}
    (hw : IntervalIntegrable w volume a b)
    (hf : AbsolutelyContinuousOnInterval f a b) (hh : IntervalIntegrable h volume a b)
    (hdf : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f (h x) x) :
    (∫ s in a..b, w s) • f b - (∫ s in a..b, w s • f s) =
      ∫ s in a..b, (∫ t in a..s, w t) • h s := by
  let r := fun x => ∫ s in a..x, w s
  have hr := hw.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hprod : AbsolutelyContinuousOnInterval (fun x => r x • f x) a b := hr.smul hf
  have hwf := hw.smul_continuousOn hf.continuousOn
  have hrh := hh.continuousOn_smul hr.continuousOn
  have hd : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt (fun y => r y • f y)
      (r x • h x + w x • f x) x := by
    filter_upwards [hw.ae_hasDerivAt_integral, hdf] with x hx hfx hmem
    exact (hx hmem a left_mem_uIcc).smul (hfx hmem)
  have hi := hprod.integral_eq_sub_of_ae_hasDerivAt_normed (hrh.add hwf) hd
  rw [intervalIntegral.integral_add hrh hwf] at hi
  have hra : r a = 0 := intervalIntegral.integral_same
  rw [hra, zero_smul, sub_zero] at hi
  dsimp only [r] at hi ⊢
  exact (eq_sub_iff_add_eq.mpr hi).symm

/-- The outgoing Hardy moment bound for Banach space curves with an integrable
specified derivative. The constant is exactly one. -/
theorem norm_sub_radialAverage_le_moment [CompleteSpace E]
    {w : ℝ → ℝ} {f h : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hw : IntervalIntegrable w volume a b) (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x)
    (hf : AbsolutelyContinuousOnInterval f a b) (hh : IntervalIntegrable h volume a b)
    (hdf : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f (h x) x)
    (hr : 0 < ∫ s in a..b, w s) :
    ‖f b - radialAverage w f a b‖ ≤
      (∫ s in a..b, w s)⁻¹ * ∫ s in a..b, (∫ t in a..s, w t) * ‖h s‖ := by
  have heq := integral_weight_smul_sub_eq_integral_moment hw hf hh hdf
  have hdev : f b - radialAverage w f a b =
      (∫ s in a..b, w s)⁻¹ • ∫ s in a..b, (∫ t in a..s, w t) • h s := by
    rw [← heq, smul_sub, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    rfl
  rw [hdev, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hr.le)
  calc
    _ ≤ ∫ s in a..b, ‖(∫ t in a..s, w t) • h s‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro s hs
      dsimp only
      rw [uIcc_of_le hab] at hs
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg]
      exact intervalIntegral.integral_nonneg hs.1
        (fun t ht => hw0 t ⟨ht.1, ht.2.trans hs.2⟩)

/-- A nonnegative weighted radial average preserves a uniform norm bound,
including the totalized zero-radius case. -/
theorem norm_radialAverage_le_of_bound [CompleteSpace E]
    {w : ℝ → ℝ} {f : ℝ → E} {a b M : ℝ} (hab : a ≤ b)
    (hw : IntervalIntegrable w volume a b) (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x)
    (hf : ContinuousOn f (Icc a b)) (hM0 : 0 ≤ M) (hM : ∀ x ∈ Icc a b, ‖f x‖ ≤ M) :
    ‖radialAverage w f a b‖ ≤ M := by
  have hfu : ContinuousOn f (uIcc a b) := by rwa [uIcc_of_le hab]
  have hwi := hw.smul_continuousOn hfu
  have hr0 : 0 ≤ ∫ s in a..b, w s := intervalIntegral.integral_nonneg hab hw0
  rcases eq_or_lt_of_le hr0 with hr | hr
  · simpa only [radialAverage, ← hr, inv_zero, zero_smul, norm_zero] using hM0
  · change ‖(∫ s in a..b, w s)⁻¹ • (∫ s in a..b, w s • f s)‖ ≤ M
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    calc
      _ ≤ (∫ s in a..b, w s)⁻¹ * ∫ s in a..b, ‖w s • f s‖ :=
        mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm hab)
          (inv_nonneg.mpr hr.le)
      _ ≤ (∫ s in a..b, w s)⁻¹ * ∫ s in a..b, w s * M := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hr.le)
        apply intervalIntegral.integral_mono_on hab hwi.norm (hw.mul_const M)
        intro s hs
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 s hs)]
        exact mul_le_mul_of_nonneg_left (hM s hs) (hw0 s hs)
      _ = M := by
        rw [intervalIntegral.integral_mul_const, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]

end EmcsfAcExtension
