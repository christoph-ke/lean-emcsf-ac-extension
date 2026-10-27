/- Copyright (c) 2026. All rights reserved. -/

module

public import EmcsfAcExtension.Infra.DampedRadial
public import EmcsfAcExtension.Infra.AC.Rpow

/-!
# Damped radial comparison with integrable weighted forcing

The integrating factor `ρ^p` is AC at the axis for every `p > 0` because `ρ`
is monotone AC. Only `ρ^p q` needs to be integrable for pointwise comparison.
-/

public section

open Set MeasureTheory Filter

namespace EmcsfAcExtension

/-- The damped radial kernel estimate needs only integrability of the weighted
forcing, which is strictly weaker than integrability of the forcing itself. -/
theorem le_damped_radial_kernel_of_integrable_moment {w y q : ℝ → ℝ} {a b p : ℝ}
    (hab : a ≤ b) (hp : 0 < p) (hw : IntervalIntegrable w volume a b)
    (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x) (hy : AbsolutelyContinuousOnInterval y a b)
    (hya : y a = 0) (hrb : 0 < ∫ s in a..b, w s)
    (hQ : IntervalIntegrable (fun x => (∫ s in a..x, w s) ^ p * q x) volume a b)
    (hineq : ∀ᵐ x ∂volume.restrict (Icc a b),
      deriv y x + p * (w x / (∫ s in a..x, w s) * y x) ≤ q x) :
    y b ≤ ∫ x in a..b, ((∫ s in a..x, w s) / (∫ s in a..b, w s)) ^ p * q x := by
  let R := fun x => ∫ s in a..x, w s
  let K := fun x => (R x) ^ p
  have hR := hw.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hm : MonotoneOn R (uIcc a b) := by
    simpa only [uIcc_of_le hab] using monotoneOn_integral_weight hw hw0
  have hK : AbsolutelyContinuousOnInterval K a b := hR.rpow_of_monotoneOn hm hp
  have hprod := hK.mul_normed_ring hy
  have hR0 : ∀ x ∈ Icc a b, 0 ≤ R x := by
    intro x hx
    exact intervalIntegral.integral_nonneg hx.1
      (fun s hs => hw0 s ⟨hs.1, hs.2.trans hx.2⟩)
  have hd : ∀ᵐ x ∂volume.restrict (Icc a b),
      deriv (fun x => K x * y x) x ≤ K x * q x := by
    have hI := (ae_restrict_iff' measurableSet_Icc).mp hineq
    have hne_a : ∀ᵐ x : ℝ, x ≠ a := by simp [ae_iff, measure_singleton]
    have hne_b : ∀ᵐ x : ℝ, x ≠ b := by simp [ae_iff, measure_singleton]
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hw.ae_hasDerivAt_integral, hK.ae_differentiableAt,
      hy.ae_differentiableAt, hI, hne_a, hne_b] with x hx hKx hyx hix hxa hxb hmem
    have hx' : x ∈ uIcc a b := Icc_subset_uIcc hmem
    have hdp : HasDerivAt (fun x => K x * y x)
        (deriv K x * y x + K x * deriv y x) x := by
      simpa only [Pi.mul_apply] using! (hKx hx').hasDerivAt.mul (hyx hx').hasDerivAt
    rw [hdp.deriv]
    by_cases hz : R x = 0
    · have hKzero : K x = 0 := by simp only [K, hz, Real.zero_rpow hp.ne']
      have hmin : IsLocalMin K x := by
        filter_upwards [Icc_mem_nhds (lt_of_le_of_ne hmem.1 hxa.symm)
          (lt_of_le_of_ne hmem.2 hxb)] with s hs
        rw [hKzero]
        exact Real.rpow_nonneg (hR0 s hs) p
      simp only [hmin.deriv_eq_zero, hKzero, zero_mul, zero_add, le_refl]
    · have hdK : deriv K x = w x * p * (R x) ^ (p - 1) :=
        ((hx hx' a left_mem_uIcc).rpow_const (Or.inl hz)).deriv
      rw [hdK, Real.rpow_sub_one hz]
      have hm' := mul_le_mul_of_nonneg_left (hix hmem) (Real.rpow_nonneg (hR0 x hmem) p)
      convert hm' using 1
      dsimp only [K]
      ring
  have hi := intervalIntegral.integral_mono_ae_restrict hab
    hprod.intervalIntegrable_deriv hQ hd
  rw [hprod.integral_deriv_eq_sub, hya, mul_zero, sub_zero] at hi
  have hKb : 0 < K b := Real.rpow_pos_of_pos hrb p
  have hdiv := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hKb.le)
  rw [← mul_assoc, inv_mul_cancel₀ hKb.ne', one_mul] at hdiv
  rw [← intervalIntegral.integral_const_mul] at hdiv
  convert hdiv using 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc a b := by rwa [uIcc_of_le hab] at hs
  dsimp only [K, R]
  rw [Real.div_rpow (hR0 s hs') hrb.le]
  ring

/-- The finite real-integral damped radial kernel bound with L¹ forcing.
The solution and forcing may have either sign, and every `p > 0` is allowed. -/
theorem le_damped_radial_kernel {w y q : ℝ → ℝ} {a b p : ℝ}
    (hab : a ≤ b) (hp : 0 < p) (hw : IntervalIntegrable w volume a b)
    (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x) (hy : AbsolutelyContinuousOnInterval y a b)
    (hya : y a = 0) (hq : IntervalIntegrable q volume a b)
    (hrb : 0 < ∫ s in a..b, w s)
    (hineq : ∀ᵐ x ∂volume.restrict (Icc a b),
      deriv y x + p * (w x / (∫ s in a..x, w s) * y x) ≤ q x) :
    y b ≤ ∫ x in a..b, ((∫ s in a..x, w s) / (∫ s in a..b, w s)) ^ p * q x := by
  have hR := hw.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hQ := hq.continuousOn_mul
    ((Real.continuous_rpow_const hp.le).comp_continuousOn hR.continuousOn)
  exact le_damped_radial_kernel_of_integrable_moment hab hp hw hw0 hy hya hrb hQ hineq

end EmcsfAcExtension
