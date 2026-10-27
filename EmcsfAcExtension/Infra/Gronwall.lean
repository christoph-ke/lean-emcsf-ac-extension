/- Copyright (c) 2026. All rights reserved. -/

module

public import EmcsfAcExtension.Infra.AC.Intervals
public import EmcsfAcExtension.Infra.AC.Quotient

/-!
# Integral Grönwall inequalities with integrable coefficients

The integrating factor gives an exact variation-of-constants upper bound for a real
absolutely continuous subsolution. The coefficient and forcing may have either sign.
The integral comparison results use a nonnegative coefficient and continuous subsolutions.
All constants and exponential factors are displayed; there are no implicit constants.
-/

public section

open Set MeasureTheory Filter

namespace EmcsfAcExtension

/-- Variation of constants for an AC differential subsolution with integrable coefficients.
Neither the coefficient nor the forcing needs a sign assumption. -/
theorem le_integratingFactor_of_ac_deriv_le {f k q : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hk : IntervalIntegrable k volume a b) (hq : IntervalIntegrable q volume a b)
    (hineq : ∀ᵐ x ∂volume.restrict (Icc a b), deriv f x ≤ k x * f x + q x) :
    ∀ t ∈ Icc a b, f t ≤ Real.exp (∫ s in a..t, k s) *
      (f a + ∫ s in a..t, Real.exp (-(∫ v in a..s, k v)) * q s) := by
  let K := fun x => ∫ s in a..x, k s
  let w := fun x => Real.exp (-K x)
  have hK := hk.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hw : AbsolutelyContinuousOnInterval w a b := hK.neg.exp
  have hprod := hw.mul_normed_ring hf
  have hwq : IntervalIntegrable (fun x => w x * q x) volume a b :=
    hq.continuousOn_mul hw.continuousOn
  have hderiv : ∀ᵐ x, x ∈ Icc a b →
      deriv (fun y => w y * f y) x ≤ w x * q x := by
    have hi := (ae_restrict_iff' measurableSet_Icc).mp hineq
    filter_upwards [hk.ae_hasDerivAt_integral, hf.ae_differentiableAt, hi] with x hx hfx hix hmem
    have hmem' : x ∈ uIcc a b := by rwa [uIcc_of_le hab]
    have hdw : HasDerivAt w (w x * (-k x)) x := (hx hmem' a left_mem_uIcc).neg.exp
    have hdprod : HasDerivAt (fun y => w y * f y)
        (w x * (-k x) * f x + w x * deriv f x) x := by
      simpa only [Pi.mul_apply] using! hdw.mul (hfx hmem').hasDerivAt
    rw [hdprod.deriv]
    have hi' := mul_le_mul_of_nonneg_left (hix hmem) (Real.exp_pos (-K x)).le
    dsimp only [w] at *
    nlinarith only [hi']
  intro t ht
  have hsub : uIcc a t ⊆ uIcc a b := by
    rw [uIcc_of_le ht.1, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl ht.2
  have hle := intervalIntegral.integral_mono_ae_restrict ht.1
    (hprod.intervalIntegrable_deriv.mono_set hsub) (hwq.mono_set hsub)
    ((ae_restrict_iff' measurableSet_Icc).mpr (hderiv.mono fun x hx hxt =>
      hx ⟨hxt.1, hxt.2.trans ht.2⟩))
  rw [(hprod.mono hsub).integral_deriv_eq_sub] at hle
  have hwa : w a = 1 := by simp only [w, K, intervalIntegral.integral_same, neg_zero, Real.exp_zero]
  rw [hwa, one_mul] at hle
  have hmul := mul_le_mul_of_nonneg_left hle (Real.exp_pos (K t)).le
  have he : Real.exp (K t) * w t = 1 := by
    dsimp only [w]
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [mul_sub, ← mul_assoc, he, one_mul] at hmul
  dsimp only [K, w] at hmul ⊢
  linarith only [hmul]

/-- Homogeneous AC Grönwall inequality, with an arbitrary signed integrable coefficient. -/
theorem le_exp_integral_of_ac_deriv_le {f k : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hk : IntervalIntegrable k volume a b)
    (hineq : ∀ᵐ x ∂volume.restrict (Icc a b), deriv f x ≤ k x * f x) :
    ∀ t ∈ Icc a b, f t ≤ f a * Real.exp (∫ s in a..t, k s) := by
  have h := le_integratingFactor_of_ac_deriv_le hab hf hk (intervalIntegrable_const (c := (0 : ℝ)))
    (hineq.mono fun x hx => by simpa only [add_zero] using hx)
  simpa only [mul_zero, zero_mul, intervalIntegral.integral_zero, add_zero, mul_comm] using h

/-- Integral Grönwall for a continuous real subsolution and an a.e. nonnegative L¹ coefficient.
The initial constant may have either sign. -/
theorem le_exp_integral_of_le_integral {f k : ℝ → ℝ} {a b C : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hk : IntervalIntegrable k volume a b)
    (hk0 : ∀ᵐ x ∂volume.restrict (Icc a b), 0 ≤ k x)
    (hineq : ∀ t ∈ Icc a b, f t ≤ C + ∫ s in a..t, k s * f s) :
    ∀ t ∈ Icc a b, f t ≤ C * Real.exp (∫ s in a..t, k s) := by
  have hkf : IntervalIntegrable (fun s => k s * f s) volume a b :=
    hk.mul_continuousOn (by rwa [uIcc_of_le hab])
  let G := fun x => C + ∫ s in a..x, k s * f s
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => C) a b :=
    (LipschitzWith.const C).lipschitzOnWith.absolutelyContinuousOnInterval
  have hG : AbsolutelyContinuousOnInterval G a b :=
    hc.fun_add (hkf.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)
  have hGle : ∀ᵐ x ∂volume.restrict (Icc a b), deriv G x ≤ k x * G x := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    have hk0' := (ae_restrict_iff' measurableSet_Icc).mp hk0
    filter_upwards [hkf.ae_hasDerivAt_integral, hk0'] with x hx hx0 hmem
    have hmem' : x ∈ uIcc a b := by rwa [uIcc_of_le hab]
    have hd : HasDerivAt G (k x * f x) x := (hx hmem' a left_mem_uIcc).const_add C
    rw [hd.deriv]
    exact mul_le_mul_of_nonneg_left (hineq x hmem) (hx0 hmem)
  intro t ht
  have h := le_exp_integral_of_ac_deriv_le hab hG hk hGle t ht
  have hGa : G a = C := by simp only [G, intervalIntegral.integral_same, add_zero]
  rw [hGa] at h
  exact (hineq t ht).trans h

/-- Integral Grönwall with a nondecreasing forcing term. The forcing need not be
continuous, integrable, or nonnegative; it is frozen at the observation time. -/
theorem le_exp_integral_of_le_integral_monotone {f k m : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hk : IntervalIntegrable k volume a b)
    (hk0 : ∀ᵐ x ∂volume.restrict (Icc a b), 0 ≤ k x)
    (hm : MonotoneOn m (Icc a b))
    (hineq : ∀ t ∈ Icc a b, f t ≤ m t + ∫ s in a..t, k s * f s) :
    ∀ t ∈ Icc a b, f t ≤ m t * Real.exp (∫ s in a..t, k s) := by
  intro t ht
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hksub : IntervalIntegrable k volume a t :=
    hk.mono_set (by simpa only [uIcc_of_le ht.1, uIcc_of_le hab] using hsub)
  have hk0sub : ∀ᵐ x ∂volume.restrict (Icc a t), 0 ≤ k x :=
    hk0.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  apply le_exp_integral_of_le_integral ht.1 (hf.mono hsub) hksub hk0sub ?_ t ⟨ht.1, le_rfl⟩
  intro s hs
  exact (hineq s (hsub hs)).trans
    (add_le_add (hm (hsub hs) ht hs.2) le_rfl)

/-- Integral Grönwall with a constant plus the primitive of a nonnegative integrable
forcing. All coefficients are exact and uniform in the functions and interval. -/
theorem le_exp_integral_of_le_integral_forcing {f k q : ℝ → ℝ} {a b C : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hk : IntervalIntegrable k volume a b) (hq : IntervalIntegrable q volume a b)
    (hk0 : ∀ᵐ x ∂volume.restrict (Icc a b), 0 ≤ k x)
    (hq0 : ∀ᵐ x ∂volume.restrict (Icc a b), 0 ≤ q x)
    (hineq : ∀ t ∈ Icc a b,
      f t ≤ (C + ∫ s in a..t, q s) + ∫ s in a..t, k s * f s) :
    ∀ t ∈ Icc a b, f t ≤ (C + ∫ s in a..t, q s) * Real.exp (∫ s in a..t, k s) := by
  apply le_exp_integral_of_le_integral_monotone hab hf hk hk0 ?_ hineq
  intro s hs t ht hst
  dsimp only
  apply add_le_add le_rfl
  have has : IntervalIntegrable q volume a s :=
    hq.mono_set (by
      rw [uIcc_of_le hs.1, uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl hs.2)
  have hstq : IntervalIntegrable q volume s t :=
    hq.mono_set (by
      rw [uIcc_of_le hst, uIcc_of_le hab]
      exact Icc_subset_Icc hs.1 ht.2)
  have hpos : 0 ≤ ∫ x in s..t, q x := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hst
    exact hq0.filter_mono
      (ae_mono (Measure.restrict_mono (Icc_subset_Icc hs.1 ht.2) le_rfl))
  rw [← intervalIntegral.integral_add_adjacent_intervals has hstq]
  exact le_add_of_nonneg_right hpos

end EmcsfAcExtension
