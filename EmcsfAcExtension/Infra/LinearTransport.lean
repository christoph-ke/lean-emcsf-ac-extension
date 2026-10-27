/- Copyright (c) 2026. All rights reserved. -/

module

public import EmcsfAcExtension.Infra.AC.Complex
public import EmcsfAcExtension.Infra.AC.Quotient

/-!
# Complex linear transport with integrable coefficients

The integrating factor is absolutely continuous even for merely integrable
coefficients. The exact formula uses the complex FTC from `Infra.AC.Complex`.
-/

public section

open Set MeasureTheory Filter

namespace AbsolutelyContinuousOnInterval

/-- The complex exponential preserves absolute continuity on a compact interval. -/
theorem cexp {g : ℝ → ℂ} {a b : ℝ} (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun x => Complex.exp (g x)) a b := by
  apply (hg.re.exp.ofReal.mul_normed_ring hg.im.unit_phase).congr
  intro x hx
  dsimp only
  rw [Complex.ofReal_exp, ← Complex.exp_add, mul_comm Complex.I, Complex.re_add_im]

end AbsolutelyContinuousOnInterval

namespace EmcsfAcExtension

/-- Exact variation of constants for complex AC transport, with arbitrary integrable
complex coefficient and forcing. No constants or sign restrictions are implicit. -/
theorem eq_integratingFactor_of_ac_deriv_eq_complex {g c q : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hg : AbsolutelyContinuousOnInterval g a b)
    (hc : IntervalIntegrable c volume a b) (hq : IntervalIntegrable q volume a b)
    (heq : ∀ᵐ x ∂volume.restrict (Icc a b), deriv g x = c x * g x + q x) :
    ∀ t ∈ Icc a b, g t = Complex.exp (∫ s in a..t, c s) *
      (g a + ∫ s in a..t, Complex.exp (-(∫ v in a..s, c v)) * q s) := by
  let C := fun x => ∫ s in a..x, c s
  let w := fun x => Complex.exp (-C x)
  have hC := hc.absolutelyContinuousOnInterval_intervalIntegral_complex left_mem_uIcc
  have hw : AbsolutelyContinuousOnInterval w a b := hC.neg.cexp
  have hwg := hw.mul_normed_ring hg
  have hwq : IntervalIntegrable (fun x => w x * q x) volume a b :=
    hq.continuousOn_mul hw.continuousOn
  have hd : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt (fun y => w y * g y) (w x * q x) x := by
    have heq' := (ae_restrict_iff' measurableSet_Icc).mp heq
    filter_upwards [hc.ae_hasDerivAt_integral, hg.ae_differentiableAt_of_mem_uIcc, heq']
      with x hx hgx heqx hmem
    have hdw : HasDerivAt w (w x * (-c x)) x := (hx hmem a left_mem_uIcc).neg.cexp
    have hprod : HasDerivAt (fun y => w y * g y)
        (w x * (-c x) * g x + w x * deriv g x) x := by
      simpa only [Pi.mul_apply] using! hdw.mul (hgx hmem).hasDerivAt
    rw [heqx (by rwa [uIcc_of_le hab] at hmem)] at hprod
    convert hprod using 1
    ring
  intro t ht
  have hsub : uIcc a t ⊆ uIcc a b := by
    rw [uIcc_of_le ht.1, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl ht.2
  have hftc := (hwg.mono hsub).integral_eq_sub_of_ae_hasDerivAt_complex
    (hwq.mono_set hsub) (hd.mono fun x hx hmem => hx (hsub hmem))
  have hwa : w a = 1 := by
    simp only [w, C, intervalIntegral.integral_same, neg_zero, Complex.exp_zero]
  rw [hwa, one_mul] at hftc
  have he : Complex.exp (C t) * w t = 1 := by
    dsimp only [w]
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hmul := congrArg (fun z => Complex.exp (C t) * z) hftc
  rw [mul_sub, ← mul_assoc, he, one_mul] at hmul
  dsimp only [C, w] at hmul ⊢
  linear_combination -hmul

end EmcsfAcExtension
