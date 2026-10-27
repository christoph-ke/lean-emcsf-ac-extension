module

public import EmcsfAcExtension.Local.Broad.ContractionCoefficient

/-! # Weighted coefficient budgets without derivative envelopes

Nonnegative domination establishes integrability before the finite real
integral is estimated. All reciprocal gap coefficients remain explicit.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local.Broad

/-- A measurable nonnegative function dominated by an integrable majorant
has an ordinary finite interval integral. The comparison coefficient is one. -/
theorem integral_of_nonneg_le_majorant {a b : ℝ} {f N : ℝ → ℝ}
    (hab : a ≤ b) (hf : AEStronglyMeasurable f (volume.restrict (Icc a b)))
    (h0 : ∀ x ∈ Icc a b, 0 ≤ f x) (iN : IntervalIntegrable N volume a b)
    (hN : ∀ x ∈ Icc a b, f x ≤ N x) :
    IntervalIntegrable f volume a b ∧ (∫ x in a..b, f x) ≤ ∫ x in a..b, N x := by
  have ii : IntervalIntegrable f volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    apply ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp iN).mono' hf
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 x hx)]
    exact hN x hx
  exact ⟨ii, intervalIntegral.integral_mono_on hab ii iN hN⟩

/-- Weighted scalar-coefficient control from the undifferenced mass and
electric budgets. The coefficient is exactly `1/c`, uniformly in all
traces, weights and budgets. -/
theorem coefficient_integral_of_mass_electric_bounds {a b c M Q : ℝ}
    {d μ q : ℝ → ℝ} (hab : a ≤ b) (hc : 0 < c)
    (hd : AEStronglyMeasurable d (volume.restrict (Icc a b)))
    (hμ : AEStronglyMeasurable μ (volume.restrict (Icc a b)))
    (hq : AEStronglyMeasurable q (volume.restrict (Icc a b)))
    (hd0 : ∀ x ∈ Icc a b, 0 ≤ d x)
    (hμ0 : ∀ x ∈ Icc a b, 0 ≤ μ x) (hq0 : ∀ x ∈ Icc a b, 0 ≤ q x)
    (hgap : ∀ x ∈ Icc a b, c ≤ 1 - μ x)
    (im : IntervalIntegrable (fun x => d x * μ x) volume a b)
    (iq : IntervalIntegrable (fun x => d x * q x) volume a b)
    (hM : (∫ x in a..b, d x * μ x) ≤ M) (hQ : (∫ x in a..b, d x * q x) ≤ Q) :
    IntervalIntegrable (fun x => d x * |(μ x - q x) / (1 - μ x)|) volume a b ∧
      (∫ x in a..b, d x * |(μ x - q x) / (1 - μ x)|) ≤ c⁻¹ * (M + Q) := by
  have h1 : AEStronglyMeasurable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Icc a b)) :=
    aestronglyMeasurable_const
  have hmeas : AEStronglyMeasurable (fun x => d x * |(μ x - q x) / (1 - μ x)|)
      (volume.restrict (Icc a b)) := by
    have hm := hd.mul (((hμ.sub hq).div₀ (h1.sub hμ)).norm)
    apply hm.congr
    filter_upwards [] with x
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.div_apply, Real.norm_eq_abs]
  obtain ⟨ii, hi⟩ := integral_of_nonneg_le_majorant hab hmeas
    (fun x hx => mul_nonneg (hd0 x hx) (abs_nonneg _))
    ((im.add iq).const_mul c⁻¹) (fun x hx => by
      change d x * |(μ x - q x) / (1 - μ x)| ≤ c⁻¹ * (d x * μ x + d x * q x)
      have hh := mul_le_mul_of_nonneg_left
        (mass_charge_coefficient_le hc (hgap x hx) (hμ0 x hx) (hq0 x hx)) (hd0 x hx)
      exact hh.trans_eq (by ring))
  refine ⟨ii, hi.trans ?_⟩
  change (∫ x in a..b, c⁻¹ * (d x * μ x + d x * q x)) ≤ c⁻¹ * (M + Q)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add im iq]
  exact mul_le_mul_of_nonneg_left (add_le_add hM hQ) (inv_nonneg.mpr hc.le)

/-- Weighted scalar-coefficient differences from matching mass and electric
difference budgets. The explicit constant depends only on `c,Qmax` and
precedes all traces and budgets. -/
theorem coefficient_difference_integral_of_bounds {a b c Qmax M Q : ℝ}
    {d μ₁ μ₂ q₁ q₂ : ℝ → ℝ} (hab : a ≤ b) (hc : 0 < c)
    (hd : AEStronglyMeasurable d (volume.restrict (Icc a b)))
    (hμ₁ : AEStronglyMeasurable μ₁ (volume.restrict (Icc a b)))
    (hμ₂ : AEStronglyMeasurable μ₂ (volume.restrict (Icc a b)))
    (hq₁ : AEStronglyMeasurable q₁ (volume.restrict (Icc a b)))
    (hq₂ : AEStronglyMeasurable q₂ (volume.restrict (Icc a b)))
    (hd0 : ∀ x ∈ Icc a b, 0 ≤ d x)
    (hμ₂box : ∀ x ∈ Icc a b, 0 ≤ μ₂ x ∧ μ₂ x ≤ 1)
    (hq₂box : ∀ x ∈ Icc a b, 0 ≤ q₂ x ∧ q₂ x ≤ Qmax)
    (hgap : ∀ x ∈ Icc a b, c ≤ 1 - μ₁ x ∧ c ≤ 1 - μ₂ x)
    (im : IntervalIntegrable (fun x => d x * |μ₁ x - μ₂ x|) volume a b)
    (iq : IntervalIntegrable (fun x => d x * |q₁ x - q₂ x|) volume a b)
    (hM : (∫ x in a..b, d x * |μ₁ x - μ₂ x|) ≤ M)
    (hQ : (∫ x in a..b, d x * |q₁ x - q₂ x|) ≤ Q) :
    IntervalIntegrable (fun x => d x * |(μ₁ x - q₁ x) / (1 - μ₁ x) -
      (μ₂ x - q₂ x) / (1 - μ₂ x)|) volume a b ∧
      (∫ x in a..b, d x * |(μ₁ x - q₁ x) / (1 - μ₁ x) -
        (μ₂ x - q₂ x) / (1 - μ₂ x)|) ≤ (c⁻¹ + (1 + Qmax) / c ^ 2) * (M + Q) := by
  let K := c⁻¹ + (1 + Qmax) / c ^ 2
  have hQmax : 0 ≤ Qmax := (hq₂box a ⟨le_rfl, hab⟩).1.trans (hq₂box a ⟨le_rfl, hab⟩).2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have h1 : AEStronglyMeasurable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Icc a b)) :=
    aestronglyMeasurable_const
  have hmeas : AEStronglyMeasurable (fun x => d x * |(μ₁ x - q₁ x) / (1 - μ₁ x) -
      (μ₂ x - q₂ x) / (1 - μ₂ x)|) (volume.restrict (Icc a b)) := by
    have hm := hd.mul
      ((((hμ₁.sub hq₁).div₀ (h1.sub hμ₁)).sub
        ((hμ₂.sub hq₂).div₀ (h1.sub hμ₂))).norm)
    apply hm.congr
    filter_upwards [] with x
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.div_apply, Real.norm_eq_abs]
  obtain ⟨ii, hi⟩ := integral_of_nonneg_le_majorant hab hmeas
    (fun x hx => mul_nonneg (hd0 x hx) (abs_nonneg _))
    ((im.add iq).const_mul K) (fun x hx => by
      change d x * |(μ₁ x - q₁ x) / (1 - μ₁ x) - (μ₂ x - q₂ x) / (1 - μ₂ x)| ≤
        K * (d x * |μ₁ x - μ₂ x| + d x * |q₁ x - q₂ x|)
      have hh := mul_le_mul_of_nonneg_left
        (mass_charge_coefficient_difference_of_bounds (q₁ := q₁ x) hc
        (hgap x hx).1 (hgap x hx).2 (hμ₂box x hx).1 (hμ₂box x hx).2
        (hq₂box x hx).1 (hq₂box x hx).2) (hd0 x hx)
      exact hh.trans_eq (by dsimp [K]; ring))
  refine ⟨ii, hi.trans ?_⟩
  change (∫ x in a..b, K * (d x * |μ₁ x - μ₂ x| + d x * |q₁ x - q₂ x|)) ≤ K * (M + Q)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add im iq]
  exact mul_le_mul_of_nonneg_left (add_le_add hM hQ) hK

end EmcsfAcExtension.Local.Broad
