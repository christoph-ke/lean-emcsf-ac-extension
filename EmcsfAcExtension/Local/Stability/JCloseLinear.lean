module

public import EmcsfAcExtension.Infra.LinearTransport
import EmcsfAcExtension.Infra.Null.IntegralForm

/-! # Linear complex transport with a real amplification budget

Only the real part of the coefficient enters the estimate. This retains
unitary gauge transport and the coefficient-one damped incoming bound.
-/

public section

open Set MeasureTheory Complex Filter

namespace EmcsfAcExtension.Local.Stab

/-- Continuous transport with an integrable classical interior derivative
is absolutely continuous. This statement includes both interval endpoints. -/
theorem ac_of_continuous_transport {a b : ℝ} {g c q : ℝ → ℂ} (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b))
    (hc : IntervalIntegrable c volume a b) (hq : IntervalIntegrable q volume a b)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt g (c x * g x + q x) x) :
    AbsolutelyContinuousOnInterval g a b := by
  have hi : IntervalIntegrable (fun x => c x * g x + q x) volume a b := by
    simpa only [Pi.mul_def, Pi.add_def] using!
      (hc.mul_continuousOn (by simpa only [uIcc_of_le hab] using hg)).add hq
  apply absolutelyContinuousOnInterval_of_integralForm_on hab
  · intro t ht
    have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
    have hisub : IntervalIntegrable (fun x => c x * g x + q x) volume a t := hi.mono_set
        (by simpa only [uIcc_of_le hab, uIcc_of_le ht.1] using hsub)
    refine ⟨hisub, ?_⟩
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 (hg.mono hsub)
      (fun x hx => hd x ⟨hx.1, hx.2.trans_le ht.2⟩) hisub).symm

/-- Variation-of-constants norm estimate with universal coefficient one.
`B` explicitly bounds every real propagator integral; no norm of the
imaginary connection, length, or derivative supremum enters the constant. -/
theorem norm_transport_le_exp_budget {a b B : ℝ} {g c q : ℝ → ℂ} (hab : a ≤ b)
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hc : IntervalIntegrable c volume a b) (hq : IntervalIntegrable q volume a b)
    (hd : ∀ᵐ x ∂volume.restrict (Icc a b), deriv g x = c x * g x + q x)
    (hB : ∀ s ∈ Icc a b, ∀ t ∈ Icc s b, (∫ x in s..t, c x).re ≤ B) :
    ∀ t ∈ Icc a b, ‖g t‖ ≤ Real.exp B * (‖g a‖ + ∫ x in a..t, ‖q x‖) := by
  intro t ht
  let C := fun s => ∫ x in a..s, c x
  let E := Complex.exp (C t)
  let f := fun s => Complex.exp (-C s) * q s
  have hC := hc.absolutelyContinuousOnInterval_intervalIntegral_complex left_mem_uIcc
  have hf : IntervalIntegrable f volume a b := hq.continuousOn_mul hC.neg.cexp.continuousOn
  have hsub : uIcc a t ⊆ uIcc a b := by
    rw [uIcc_of_le ht.1, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl ht.2
  have hfsub := hf.mono_set hsub
  have hqsub := hq.mono_set hsub
  have hprop (s : ℝ) (hs : s ∈ Icc a t) :
      E * Complex.exp (-C s) = Complex.exp (∫ x in s..t, c x) := by
    have hsab : s ∈ uIcc a b := by
      rw [uIcc_of_le hab]
      exact ⟨hs.1, hs.2.trans ht.2⟩
    have his := hc.mono_set (uIcc_subset_uIcc left_mem_uIcc hsab)
    dsimp [E, C]
    rw [← Complex.exp_add, ← sub_eq_add_neg,
      intervalIntegral.integral_interval_sub_left (hc.mono_set hsub) his]
  have hnorm (s : ℝ) (hs : s ∈ Icc a t) : ‖E * f s‖ ≤ Real.exp B * ‖q s‖ := by
    dsimp only [f]
    rw [← mul_assoc, hprop s hs, norm_mul, Complex.norm_exp]
    exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (hB s ⟨hs.1, hs.2.trans ht.2⟩ t ⟨hs.2, ht.2⟩)) (norm_nonneg _)
  have hEnorm : ‖E‖ ≤ Real.exp B := by
    dsimp [E, C]
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (hB a ⟨le_rfl, hab⟩ t ht)
  have hformula := eq_integratingFactor_of_ac_deriv_eq_complex hab hg hc hq hd t ht
  change g t = E * (g a + ∫ x in a..t, f x) at hformula
  rw [hformula, mul_add, ← intervalIntegral.integral_const_mul]
  calc
    _ ≤ ‖E * g a‖ + ‖∫ x in a..t, E * f x‖ := norm_add_le _ _
    _ ≤ Real.exp B * ‖g a‖ + ∫ x in a..t, ‖E * f x‖ := by
      apply add_le_add
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hEnorm (norm_nonneg _)
      · exact intervalIntegral.norm_integral_le_integral_norm ht.1
    _ ≤ Real.exp B * ‖g a‖ + ∫ x in a..t, Real.exp B * ‖q x‖ := by
      apply add_le_add le_rfl
      exact intervalIntegral.integral_mono_on ht.1 (hfsub.const_mul E).norm
        (hqsub.norm.const_mul (Real.exp B)) hnorm
    _ = _ := by rw [intervalIntegral.integral_const_mul]; ring

/-- Interior classical transport supplies the almost-everywhere equation
needed by linear variation of constants. The only exceptional points are
the two endpoints, which have zero Lebesgue measure. -/
theorem ae_deriv_eq_of_transport {a b : ℝ} {g c q : ℝ → ℂ}
    (hd : ∀ x ∈ Ioo a b, HasDerivAt g (c x * g x + q x) x) :
    ∀ᵐ x ∂volume.restrict (Icc a b), deriv g x = c x * g x + q x := by
  have hna : ∀ᵐ x : ℝ, x ≠ a := by simp [ae_iff, measure_singleton]
  have hnb : ∀ᵐ x : ℝ, x ≠ b := by simp [ae_iff, measure_singleton]
  filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hna,
    ae_restrict_of_ae hnb] with x hx hxa hxb
  exact (hd x ⟨lt_of_le_of_ne hx.1 hxa.symm, lt_of_le_of_ne hx.2 hxb⟩).deriv

end EmcsfAcExtension.Local.Stab
