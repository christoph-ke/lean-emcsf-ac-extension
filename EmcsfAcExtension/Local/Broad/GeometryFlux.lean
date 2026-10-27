module

public import EmcsfAcExtension.Local.Broad.MassFluxCore
import EmcsfAcExtension.Local.Broad.PotentialAlgebra

/-! # Quadratic optical fluxes from finite BV Hardy budgets

The weight comparison keeps the radial denominator error. The estimates
are in ordinary finite integrals, with explicit coefficients throughout.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local.Broad

/-- Domination transfers a Hardy integral between comparable nonnegative
weights. The coefficient `W` is explicit and independent of the trace. -/
theorem hardy_integral_of_comparable_weight {a b W : ℝ} {d d' : ℝ → ℝ}
    {f : ℝ → ℂ} (hab : a ≤ b) (_hW : 0 ≤ W)
    (hd : AEStronglyMeasurable d (volume.restrict (Icc a b)))
    (cf : ContinuousOn f (Icc a b)) (hd0 : ∀ x ∈ Icc a b, 0 ≤ d x)
    (hcomp : ∀ x ∈ Icc a b, d x ≤ W * d' x)
    (hi : IntervalIntegrable (fun x => d' x * ‖f x‖) volume a b) :
    IntervalIntegrable (fun x => d x * ‖f x‖) volume a b ∧
      (∫ x in a..b, d x * ‖f x‖) ≤ W * (∫ x in a..b, d' x * ‖f x‖) := by
  have ii : IntervalIntegrable (fun x => d x * ‖f x‖) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    apply (((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hi).const_mul W).mono'
      (hd.mul (cf.norm.aestronglyMeasurable measurableSet_Icc))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    change ‖d x * ‖f x‖‖ ≤ W * (d' x * ‖f x‖)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hd0 x hx) (norm_nonneg _))]
    exact (mul_le_mul_of_nonneg_right (hcomp x hx) (norm_nonneg _)).trans_eq (by ring)
  refine ⟨ii, ?_⟩
  have hh := intervalIntegral.integral_mono_on hab ii (hi.const_mul W) (fun x hx =>
    (mul_le_mul_of_nonneg_right (hcomp x hx) (norm_nonneg _)).trans_eq (by ring))
  simpa only [intervalIntegral.integral_const_mul] using hh

/-- A bounded scalar ratio turns its finite linear Hardy integral into a
finite quadratic optical flux. The exact coefficient is the ratio bound. -/
theorem quadratic_flux_of_hardy {a b ε : ℝ} {d : ℝ → ℝ} {f : ℝ → ℂ}
    (hab : a ≤ b) (_hε : 0 ≤ ε)
    (hd : AEStronglyMeasurable d (volume.restrict (Icc a b)))
    (cf : ContinuousOn f (Icc a b)) (hd0 : ∀ x ∈ Icc a b, 0 ≤ d x)
    (hf : ∀ x ∈ Icc a b, ‖f x‖ ≤ ε)
    (hi : IntervalIntegrable (fun x => d x * ‖f x‖) volume a b) :
    IntervalIntegrable (fun x => d x * ‖f x‖ ^ 2) volume a b ∧
      (∫ x in a..b, d x * ‖f x‖ ^ 2) ≤ ε * (∫ x in a..b, d x * ‖f x‖) := by
  have hbound x (hx : x ∈ Icc a b) : d x * ‖f x‖ ^ 2 ≤ ε * (d x * ‖f x‖) := by
    have hm := mul_le_mul_of_nonneg_left (hf x hx) (mul_nonneg (hd0 x hx) (norm_nonneg (f x)))
    nlinarith only [hm]
  have ii : IntervalIntegrable (fun x => d x * ‖f x‖ ^ 2) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    apply (((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hi).const_mul ε).mono'
      (hd.mul ((cf.norm.pow 2).aestronglyMeasurable measurableSet_Icc))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    change ‖d x * ‖f x‖ ^ 2‖ ≤ ε * (d x * ‖f x‖)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hd0 x hx) (sq_nonneg _))]
    exact hbound x hx
  refine ⟨ii, ?_⟩
  have hh := intervalIntegral.integral_mono_on hab ii (hi.const_mul ε) hbound
  simpa only [intervalIntegral.integral_const_mul] using hh

/-- A quadratic flux comparison with every weight error retained. The
coefficients `W,KB` are fixed weight-comparison constants; `A₁,A₂` are
the two matching finite Hardy budgets. All dependence is explicit and
uniform in the interval, weights, complex traces and errors. -/
theorem quadratic_flux_difference_of_bounds {a b ε H G W KB A₁ A₂ : ℝ}
    {d₁ d₂ : ℝ → ℝ} {f₁ f₂ : ℝ → ℂ}
    (hab : a ≤ b) (hε : 0 ≤ ε) (hH : 0 ≤ H) (hG : 0 ≤ G)
    (hW : 0 ≤ W) (hKB : 0 ≤ KB)
    (hd₁ : AEStronglyMeasurable d₁ (volume.restrict (Icc a b)))
    (hd₂ : AEStronglyMeasurable d₂ (volume.restrict (Icc a b)))
    (cf₁ : ContinuousOn f₁ (Icc a b)) (cf₂ : ContinuousOn f₂ (Icc a b))
    (hd₁0 : ∀ x ∈ Icc a b, 0 ≤ d₁ x) (hd₂0 : ∀ x ∈ Icc a b, 0 ≤ d₂ x)
    (hcomp : ∀ x ∈ Icc a b, d₁ x ≤ W * d₂ x)
    (hδd : ∀ x ∈ Icc a b, |d₁ x - d₂ x| ≤ KB * G * d₁ x)
    (hf₁ : ∀ x ∈ Icc a b, ‖f₁ x‖ ≤ ε)
    (hf₂ : ∀ x ∈ Icc a b, ‖f₂ x‖ ≤ ε)
    (hδf : ∀ x ∈ Icc a b, ‖f₁ x - f₂ x‖ ≤ H)
    (i₁ : IntervalIntegrable (fun x => d₁ x * ‖f₁ x‖) volume a b)
    (i₂ : IntervalIntegrable (fun x => d₂ x * ‖f₂ x‖) volume a b)
    (hA₁ : (∫ x in a..b, d₁ x * ‖f₁ x‖) ≤ A₁)
    (hA₂ : (∫ x in a..b, d₂ x * ‖f₂ x‖) ≤ A₂) :
    IntervalIntegrable (fun x => d₁ x * ‖f₁ x‖ ^ 2 - d₂ x * ‖f₂ x‖ ^ 2) volume a b ∧
      |∫ x in a..b, d₁ x * ‖f₁ x‖ ^ 2 - d₂ x * ‖f₂ x‖ ^ 2| ≤
        H * A₁ + (H + KB * G * ε) * W * A₂ := by
  have iq₁ := (quadratic_flux_of_hardy hab hε hd₁ cf₁ hd₁0 hf₁ i₁).1
  have iq₂ := (quadratic_flux_of_hardy hab hε hd₂ cf₂ hd₂0 hf₂ i₂).1
  obtain ⟨imix, hmix⟩ := hardy_integral_of_comparable_weight hab hW hd₁ cf₂ hd₁0 hcomp i₂
  have hcoef : 0 ≤ H + KB * G * ε := by positivity
  let N := fun x => H * (d₁ x * ‖f₁ x‖) + (H + KB * G * ε) * (d₁ x * ‖f₂ x‖)
  have iN : IntervalIntegrable N volume a b := (i₁.const_mul H).add (imix.const_mul _)
  have hmaj x (hx : x ∈ Icc a b) :
      |d₁ x * ‖f₁ x‖ ^ 2 - d₂ x * ‖f₂ x‖ ^ 2| ≤ N x := by
    have hs := scalar_mass_difference_le_linear (g₁ := 1) (g₂ := 1)
      (H := H) (X := 0) zero_le_one le_rfl hH le_rfl (hδf x hx) (by simp)
    simp only [one_mul, zero_mul, add_zero] at hs
    apply (abs_product_sub_le _ _ _ _).trans
    rw [abs_of_nonneg (hd₁0 x hx), abs_of_nonneg (sq_nonneg ‖f₂ x‖)]
    calc
      _ ≤ d₁ x * (H * (‖f₁ x‖ + ‖f₂ x‖)) + (KB * G * d₁ x) * (ε * ‖f₂ x‖) := by
        have hsq : ‖f₂ x‖ ^ 2 ≤ ε * ‖f₂ x‖ := by
          nlinarith only [mul_le_mul_of_nonneg_right (hf₂ x hx) (norm_nonneg (f₂ x))]
        exact add_le_add (mul_le_mul_of_nonneg_left hs (hd₁0 x hx))
          (mul_le_mul (hδd x hx) hsq (sq_nonneg _) (mul_nonneg (mul_nonneg hKB hG) (hd₁0 x hx)))
      _ = _ := by dsimp [N]; ring
  have hnorm := (intervalIntegral.norm_integral_le_integral_norm hab).trans
    (intervalIntegral.integral_mono_on hab (iq₁.sub iq₂).norm iN (fun x hx => by
      simpa only [Real.norm_eq_abs] using hmaj x hx))
  refine ⟨iq₁.sub iq₂, ?_⟩
  change |∫ x in a..b, d₁ x * ‖f₁ x‖ ^ 2 - d₂ x * ‖f₂ x‖ ^ 2| ≤
    ∫ x in a..b, H * (d₁ x * ‖f₁ x‖) + (H + KB * G * ε) * (d₁ x * ‖f₂ x‖) at hnorm
  rw [intervalIntegral.integral_add (f := fun x => H * (d₁ x * ‖f₁ x‖))
    (g := fun x => (H + KB * G * ε) * (d₁ x * ‖f₂ x‖)) (i₁.const_mul H) (imix.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hnorm
  apply hnorm.trans
  have hmixA := hmix.trans (mul_le_mul_of_nonneg_left hA₂ hW)
  calc
    _ ≤ H * A₁ + (H + KB * G * ε) * (W * A₂) := by gcongr
    _ = _ := by ring

end EmcsfAcExtension.Local.Broad
