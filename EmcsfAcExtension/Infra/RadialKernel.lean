/- Copyright (c) 2026. All rights reserved. -/

module

public import EmcsfAcExtension.Infra.AC.Intervals
public import EmcsfAcExtension.Infra.AC.Quotient

/-!
# A radial inverse-cube kernel

For a positive increasing AC radius with a.e. derivative `λ`, the inverse-square
primitive computes the integral of `λ / r³` exactly. This gives the numerical constant
`1/2` in the area estimate at `charged_SF_new_version.tex:L4710–L4713`, uniformly in the radius,
its derivative, and the interval.
-/

public section

open Set MeasureTheory Filter

namespace EmcsfAcExtension

/-- Exact inverse-cube kernel integral for an increasing positive AC radius.
The derivative is specified only almost everywhere. -/
theorem integral_radial_inv_cube_eq {r lam : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hr : AbsolutelyContinuousOnInterval r a b)
    (hra : 0 < r a) (hmono : MonotoneOn r (Icc a b))
    (hderiv : ∀ᵐ x ∂volume.restrict (Icc a b), deriv r x = lam x) :
    (∫ x in a..b, lam x / r x ^ 3) = 1 / (2 * r a ^ 2) - 1 / (2 * r b ^ 2) := by
  have hlo : ∀ x ∈ uIcc a b, r a ≤ r x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact hmono ⟨le_rfl, hab⟩ hx hx.1
  have hrpos : ∀ x ∈ uIcc a b, 0 < r x := fun x hx => hra.trans_le (hlo x hx)
  have hinv := hr.inv_of_le_norm hra (fun x hx => (hlo x hx).trans (le_abs_self _))
  have hH : AbsolutelyContinuousOnInterval (fun x => (-1 / 2 : ℝ) * (r x)⁻¹ ^ 2) a b := by
    simpa only [smul_eq_mul, pow_two] using
      (hinv.mul_normed_ring hinv).const_smul (-1 / 2 : ℝ)
  have hd : ∀ᵐ x, x ∈ uIcc a b →
      HasDerivAt (fun x => (-1 / 2 : ℝ) * (r x)⁻¹ ^ 2) (lam x / r x ^ 3) x := by
    have hd' := (ae_restrict_iff' measurableSet_Icc).mp hderiv
    filter_upwards [hr.ae_differentiableAt, hd'] with x hx hdx hmem
    have hne : r x ≠ 0 := ne_of_gt (hrpos x hmem)
    have hd1 := (((hx hmem).hasDerivAt.inv hne).pow 2).const_mul (-1 / 2 : ℝ)
    have hdeq := hdx (by rwa [uIcc_of_le hab] at hmem)
    have hd2 : HasDerivAt (fun x => (-1 / 2 : ℝ) * (r x)⁻¹ ^ 2)
        ((-1 / 2 : ℝ) * (2 * (r x)⁻¹ ^ (2 - 1) * (-deriv r x / r x ^ 2))) x := by
      simpa only [Pi.inv_apply] using! hd1
    convert hd2 using 1
    rw [hdeq]
    norm_num only [Nat.reduceSub, pow_one]
    field_simp [hne]
  rw [hH.integral_eq_sub_of_ae_hasDerivAt_real hd]
  have hna : r a ≠ 0 := ne_of_gt hra
  have hnb : r b ≠ 0 := ne_of_gt (hrpos b right_mem_uIcc)
  (field_simp [hna, hnb]; ring)

/-- The radial inverse-cube kernel is bounded by the initial inverse-square radius,
with the exact universal constant `1/2`. -/
theorem integral_radial_inv_cube_le {r lam : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hr : AbsolutelyContinuousOnInterval r a b)
    (hra : 0 < r a) (hmono : MonotoneOn r (Icc a b))
    (hderiv : ∀ᵐ x ∂volume.restrict (Icc a b), deriv r x = lam x) :
    (∫ x in a..b, lam x / r x ^ 3) ≤ 1 / (2 * r a ^ 2) := by
  rw [integral_radial_inv_cube_eq hab hr hra hmono hderiv]
  exact sub_le_self _ (by positivity)

end EmcsfAcExtension
