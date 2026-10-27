module

public import EmcsfAcExtension.Local.Broad.GeometryFlux

/-! # Integral comparison of the undifferentiated geometric scalar source

The three terms are the scalar difference, coefficient difference and
radial-weight difference. No wrong-orientation scalar Hardy integral is
used: the ratio multiplying the mass coefficient needs only a bound.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local.Broad

/-- The three-factor scalar-source comparison from internal project record (SG).
Every coefficient is explicit, uniformly in the interval and traces.
The actual weighted coefficient budgets are supplied by the matching
mass and electric estimates in the solution-level callers. -/
theorem geometric_scalar_source_difference_of_bounds {a b H ε KB G A₁ A₂ Ad : ℝ}
    {d₁ d₂ F₁ F₂ : ℝ → ℝ} {z₁ z₂ : ℝ → ℂ}
    (hab : a ≤ b) (hH : 0 ≤ H) (hε : 0 ≤ ε) (hKB : 0 ≤ KB) (hG : 0 ≤ G)
    (hd₁ : ∀ x ∈ Icc a b, 0 ≤ d₁ x)
    (hδd : ∀ x ∈ Icc a b, |d₁ x - d₂ x| ≤ KB * G * d₁ x)
    (hz₂ : ∀ x ∈ Icc a b, ‖z₂ x‖ ≤ ε)
    (hδz : ∀ x ∈ Icc a b, ‖z₁ x - z₂ x‖ ≤ H)
    (hFmeas : AEStronglyMeasurable
      (fun x => (d₁ x : ℂ) * F₁ x * z₁ x - (d₂ x : ℂ) * F₂ x * z₂ x)
      (volume.restrict (Icc a b)))
    (i₁ : IntervalIntegrable (fun x => d₁ x * |F₁ x|) volume a b)
    (i₂ : IntervalIntegrable (fun x => d₁ x * |F₂ x|) volume a b)
    (id : IntervalIntegrable (fun x => d₁ x * |F₁ x - F₂ x|) volume a b)
    (hA₁ : (∫ x in a..b, d₁ x * |F₁ x|) ≤ A₁)
    (hA₂ : (∫ x in a..b, d₁ x * |F₂ x|) ≤ A₂)
    (hAd : (∫ x in a..b, d₁ x * |F₁ x - F₂ x|) ≤ Ad) :
    IntervalIntegrable (fun x => (d₁ x : ℂ) * F₁ x * z₁ x - (d₂ x : ℂ) * F₂ x * z₂ x)
      volume a b ∧
      (∫ x in a..b, ‖(d₁ x : ℂ) * F₁ x * z₁ x - (d₂ x : ℂ) * F₂ x * z₂ x‖) ≤
        H * A₁ + ε * Ad + KB * G * ε * A₂ := by
  let N := fun x => H * (d₁ x * |F₁ x|) + ε * (d₁ x * |F₁ x - F₂ x|) +
    (KB * G * ε) * (d₁ x * |F₂ x|)
  have iN : IntervalIntegrable N volume a b := ((i₁.const_mul H).add (id.const_mul ε)).add
    (i₂.const_mul (KB * G * ε))
  have hmaj x (hx : x ∈ Icc a b) :
      ‖(d₁ x : ℂ) * F₁ x * z₁ x - (d₂ x : ℂ) * F₂ x * z₂ x‖ ≤ N x := by
    have heq : (d₁ x : ℂ) * F₁ x * z₁ x - (d₂ x : ℂ) * F₂ x * z₂ x =
        (d₁ x : ℂ) * F₁ x * (z₁ x - z₂ x) +
        (d₁ x : ℂ) * (F₁ x - F₂ x : ℝ) * z₂ x +
        (d₁ x - d₂ x : ℝ) * (F₂ x : ℂ) * z₂ x := by push_cast; ring
    rw [heq]
    apply ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hd₁ x hx)]
    have hb₁ := mul_le_mul_of_nonneg_left (hδz x hx)
      (mul_nonneg (hd₁ x hx) (abs_nonneg (F₁ x)))
    have hbd := mul_le_mul_of_nonneg_left (hz₂ x hx)
      (mul_nonneg (hd₁ x hx) (abs_nonneg (F₁ x - F₂ x)))
    have hb₂ := mul_le_mul (hδd x hx) (hz₂ x hx) (norm_nonneg _)
      (mul_nonneg (mul_nonneg hKB hG) (hd₁ x hx))
    have hb₂' := mul_le_mul_of_nonneg_right hb₂ (abs_nonneg (F₂ x))
    dsimp [N]
    nlinarith only [hb₁, hbd, hb₂']
  have ii : IntervalIntegrable
      (fun x => (d₁ x : ℂ) * F₁ x * z₁ x - (d₂ x : ℂ) * F₂ x * z₂ x) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    apply ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp iN).mono' hFmeas
    exact (ae_restrict_mem measurableSet_Icc).mono (fun x hx => hmaj x hx)
  have hi := intervalIntegral.integral_mono_on hab ii.norm iN (fun x hx => hmaj x hx)
  refine ⟨ii, hi.trans ?_⟩
  change (∫ x in a..b, H * (d₁ x * |F₁ x|) + ε * (d₁ x * |F₁ x - F₂ x|) +
    (KB * G * ε) * (d₁ x * |F₂ x|)) ≤ H * A₁ + ε * Ad + KB * G * ε * A₂
  rw [intervalIntegral.integral_add (f := fun x => H * (d₁ x * |F₁ x|) + ε * (d₁ x * |F₁ x - F₂ x|))
    (g := fun x => (KB * G * ε) * (d₁ x * |F₂ x|)) ((i₁.const_mul H).add (id.const_mul ε))
    (i₂.const_mul (KB * G * ε)), intervalIntegral.integral_add (f := fun x => H * (d₁ x * |F₁ x|))
    (g := fun x => ε * (d₁ x * |F₁ x - F₂ x|)) (i₁.const_mul H) (id.const_mul ε)]
  simp only [intervalIntegral.integral_const_mul]
  exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hA₁ hH)
    (mul_le_mul_of_nonneg_left hAd hε)) (mul_le_mul_of_nonneg_left hA₂ (by positivity))

end EmcsfAcExtension.Local.Broad
