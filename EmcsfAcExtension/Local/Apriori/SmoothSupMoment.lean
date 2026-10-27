module

public import EmcsfAcExtension.Infra.DampedRadialKernel
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Complex radial comparison with a unitary connection

The singular integrating-factor argument of internal project record (M2) and
`charged_SF_new_version.tex:L4946–4946`, `L6209–6216`. The radial damping is not
assumed integrable at the axis. Its positive power is the integrating factor.
-/

public section

open Set MeasureTheory Complex Filter
open scoped RealInnerProductSpace

namespace EmcsfAcExtension.Local

private theorem inner_damping_aux (z q : ℂ) (c A : ℝ) :
    inner ℝ z ((-c : ℂ) * z - (I * A) * z + q) =
      -c * ‖z‖ ^ 2 + inner ℝ z q := by
  rw [real_inner_eq_re_inner ℂ, real_inner_eq_re_inner ℂ,
    RCLike.inner_apply, RCLike.inner_apply]
  change (((-c : ℂ) * z - (I * A) * z + q) * starRingEnd ℂ z).re =
    -c * ‖z‖ ^ 2 + (q * starRingEnd ℂ z).re
  simp only [Complex.add_re, Complex.sub_re, Complex.add_im, Complex.sub_im,
    Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

private theorem norm_damping_aux {z : ℝ → ℂ} {x c A : ℝ} {q : ℂ}
    (hz : HasDerivAt z ((-c : ℂ) * z x - (I * A) * z x + q) x)
    (hy : DifferentiableAt ℝ (fun t => ‖z t‖) x) :
    deriv (fun t => ‖z t‖) x + c * ‖z x‖ ≤ ‖q‖ := by
  by_cases hzero : z x = 0
  · have hmin : IsLocalMin (fun t => ‖z t‖) x :=
      Filter.Eventually.of_forall (fun t => by simp only [hzero, norm_zero]; exact norm_nonneg _)
    rw [hmin.deriv_eq_zero, hzero, norm_zero, mul_zero, add_zero]
    exact norm_nonneg _
  have hn : 0 < ‖z x‖ := norm_pos_iff.mpr hzero
  have heq := hz.norm_sq.unique (hy.hasDerivAt.pow 2)
  rw [inner_damping_aux] at heq
  norm_num only [Nat.reduceSub, pow_one] at heq
  have hcs := real_inner_le_norm (z x) q
  have hi : (deriv (fun t => ‖z t‖) x + c * ‖z x‖) * ‖z x‖ ≤ ‖q‖ * ‖z x‖ := by
    nlinarith only [heq, hcs]
  exact (mul_le_mul_iff_left₀ hn).mp hi

/-- Complex singular radial comparison from the exact transport identity.
The numerical coefficient is one, uniformly in all functions and endpoints;
only the displayed positive exponent enters the weight. A real connection
`A` contributes no growth. Only the real majorant `Q` must be integrable.
This analytic `_of_identity` helper asserts no EMCSF graph-node closure. -/
theorem smooth_radial_kernel_of_identity {w c A Q : ℝ → ℝ} {z q : ℝ → ℂ}
    {a b p : ℝ} (hab : a ≤ b) (hp : 0 < p)
    (hw : IntervalIntegrable w volume a b) (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x)
    (hz : AbsolutelyContinuousOnInterval z a b) (hza : z a = 0)
    (hQ : IntervalIntegrable Q volume a b) (hrb : 0 < ∫ s in a..b, w s)
    (hc : ∀ x ∈ Icc a b, p ≤ c x)
    (hbound : ∀ᵐ x ∂volume.restrict (Icc a b), ‖q x‖ ≤ Q x)
    (hidentity : ∀ᵐ x ∂volume.restrict (Icc a b),
      HasDerivAt z
        ((-(w x / (∫ s in a..x, w s) * c x) : ℂ) * z x -
          (I * A x) * z x + q x) x) :
    ‖z b‖ ≤ ∫ x in a..b,
      ((∫ s in a..x, w s) / (∫ s in a..b, w s)) ^ p * Q x := by
  have hy : AbsolutelyContinuousOnInterval (fun x => ‖z x‖) a b :=
    lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval hz
  apply le_damped_radial_kernel hab hp hw hw0 hy (by rw [hza, norm_zero]) hQ hrb
  have hd : ∀ᵐ x ∂volume.restrict (Icc a b),
      x ∈ uIcc a b → DifferentiableAt ℝ (fun t => ‖z t‖) x :=
    ae_restrict_of_ae hy.ae_differentiableAt
  filter_upwards [hd, hidentity, hbound, ae_restrict_mem measurableSet_Icc] with x hx hi hb hxmem
  have hx' : x ∈ uIcc a b := Icc_subset_uIcc hxmem
  have hnorm := norm_damping_aux (c := w x / (∫ s in a..x, w s) * c x)
    (A := A x) (q := q x) (by
      simpa only [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_div] using hi) (hx hx')
  have hr0 : 0 ≤ ∫ s in a..x, w s := intervalIntegral.integral_nonneg hxmem.1
    (fun s hs => hw0 s ⟨hs.1, hs.2.trans hxmem.2⟩)
  have hcoef := mul_le_mul_of_nonneg_right (hc x hxmem)
    (mul_nonneg (div_nonneg (hw0 x hxmem) hr0) (norm_nonneg (z x)))
  nlinarith only [hnorm, hcoef, hb]

end EmcsfAcExtension.Local
