module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Integrability and variation bounds for derivatives of BV curves

The cumulative variation is monotone and dominates increments of a curve. Its
almost everywhere derivative therefore dominates the speed of the curve. The
integral of that speed is bounded by the total variation, even without AC.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

variable {E : Type*} [NormedAddCommGroup E]

/-- Increments of a BV curve are bounded by increments of its cumulative variation. -/
theorem variationOnFromTo.norm_sub_le_sub_of_le {f : ℝ → E} {s : Set ℝ}
    (hf : BoundedVariationOn f s)
    {a x y : ℝ} (ha : a ∈ s) (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≤ y) :
    ‖f y - f x‖ ≤ variationOnFromTo f s a y - variationOnFromTo f s a x := by
  rw [← variationOnFromTo.add hf.locallyBoundedVariationOn ha hx hy, add_sub_cancel_left,
    variationOnFromTo.eq_of_le _ _ hxy]
  have h : BoundedVariationOn f (s ∩ Icc x y) := hf.mono inter_subset_left
  simpa only [dist_eq_norm] using h.dist_le ⟨hy, hxy, le_rfl⟩ ⟨hx, le_rfl, hxy⟩

variable [NormedSpace ℝ E]

/-- At a common differentiability point, the cumulative variation dominates the speed. -/
theorem BoundedVariationOn.norm_deriv_le_deriv_variationOnFromTo
    {f : ℝ → E} {a b x : ℝ} (hf : BoundedVariationOn f (Icc a b))
    (hx : x ∈ Ioo a b) (hdf : DifferentiableAt ℝ f x)
    (hdv : DifferentiableAt ℝ (variationOnFromTo f (Icc a b) a) x) :
    ‖deriv f x‖ ≤ deriv (variationOnFromTo f (Icc a b) a) x := by
  apply le_of_tendsto_of_tendsto
    (hdf.hasDerivAt.tendsto_slope.mono_left (nhdsGT_le_nhdsNE x)).norm
    (hdv.hasDerivAt.tendsto_slope.mono_left (nhdsGT_le_nhdsNE x))
  filter_upwards [self_mem_nhdsWithin,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Icc_mem_nhds hx.1 hx.2)] with y hy hy'
  change x < y at hy
  have h := variationOnFromTo.norm_sub_le_sub_of_le hf
    ⟨le_rfl, hx.1.le.trans hx.2.le⟩ ⟨hx.1.le, hx.2.le⟩ hy' hy.le
  simpa only [slope_def_module, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos (sub_pos.mpr hy), smul_eq_mul] using mul_le_mul_of_nonneg_left h
      (inv_nonneg.mpr (sub_nonneg.mpr hy.le))

variable [FiniteDimensional ℝ E]

/-- The derivative of cumulative variation bounds the derivative norm almost everywhere. -/
theorem BoundedVariationOn.ae_norm_deriv_le_deriv_variationOnFromTo
    {f : ℝ → E} {a b : ℝ} (hf : BoundedVariationOn f (Icc a b)) (hab : a ≤ b) :
    ∀ᵐ x ∂volume.restrict (Icc a b),
      ‖deriv f x‖ ≤ deriv (variationOnFromTo f (Icc a b) a) x := by
  have hmono := variationOnFromTo.monotoneOn hf.locallyBoundedVariationOn (left_mem_Icc.mpr hab)
  have hf' : BoundedVariationOn f (uIcc a b) := by rwa [uIcc_of_le hab]
  have hne_a : ∀ᵐ x : ℝ, x ≠ a := by simp [ae_iff, measure_singleton]
  have hne_b : ∀ᵐ x : ℝ, x ≠ b := by simp [ae_iff, measure_singleton]
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hf'.ae_differentiableAt_of_mem_uIcc,
    hmono.ae_differentiableWithinAt_of_mem, hne_a, hne_b] with x hdf hdv hxa hxb hx
  have hx' : x ∈ Ioo a b := ⟨lt_of_le_of_ne hx.1 hxa.symm, lt_of_le_of_ne hx.2 hxb⟩
  exact hf.norm_deriv_le_deriv_variationOnFromTo hx' (hdf (by rwa [uIcc_of_le hab]))
    ((hdv hx).differentiableAt (Icc_mem_nhds hx'.1 hx'.2))

/-- Derivatives of finite dimensional real BV curves are interval integrable. -/
theorem BoundedVariationOn.intervalIntegrable_deriv_finiteDimensional
    {f : ℝ → E} {a b : ℝ} (hf : BoundedVariationOn f (Icc a b)) (hab : a ≤ b) :
    IntervalIntegrable (deriv f) volume a b := by
  have hmono := variationOnFromTo.monotoneOn hf.locallyBoundedVariationOn (left_mem_Icc.mpr hab)
  have hv : IntervalIntegrable (deriv (variationOnFromTo f (Icc a b) a)) volume a b :=
    (by simpa only [uIcc_of_le hab] using hmono : MonotoneOn _ (uIcc a b)).intervalIntegrable_deriv
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
  exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).1 hv).mono'
    (aestronglyMeasurable_deriv _ _) (hf.ae_norm_deriv_le_deriv_variationOnFromTo hab)

/-- The integral of the derivative norm is bounded by total variation for BV curves. -/
theorem BoundedVariationOn.integral_norm_deriv_le {f : ℝ → E} {a b : ℝ}
    (hf : BoundedVariationOn f (Icc a b)) (hab : a ≤ b) :
    (∫ x in a..b, ‖deriv f x‖) ≤ (eVariationOn f (Icc a b)).toReal := by
  have hmono := variationOnFromTo.monotoneOn hf.locallyBoundedVariationOn (left_mem_Icc.mpr hab)
  have hmono' : MonotoneOn (variationOnFromTo f (Icc a b) a) (uIcc a b) := by
    rwa [uIcc_of_le hab]
  have hv := hmono'.intervalIntegrable_deriv
  have hbound := intervalIntegral.integral_mono_ae_restrict hab
    (hf.intervalIntegrable_deriv_finiteDimensional hab).norm hv
    (hf.ae_norm_deriv_le_deriv_variationOnFromTo hab)
  have hup := hmono'.intervalIntegral_deriv_mem_uIcc
  have hnonneg := sub_nonneg.mpr (hmono (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab)
  rw [uIcc_of_le hnonneg] at hup
  apply hbound.trans
  simpa only [variationOnFromTo.self, sub_zero, variationOnFromTo.eq_of_le _ _ hab,
    inter_self] using hup.2
