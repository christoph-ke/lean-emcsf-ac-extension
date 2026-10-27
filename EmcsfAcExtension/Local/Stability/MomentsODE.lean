module

public import EmcsfAcExtension.Infra.DampedRadialExtended
import Mathlib

/-! # Complex analytic core of the radial stability moments

The imaginary connection coefficient cancels in the derivative of the norm.
The damping remains `p * w / ρ`, including at a singular axis. This file
uses an arbitrary AC curve and has no field-equation or graph-node theorem.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal RealInnerProductSpace

namespace EmcsfAcExtension.Local

private theorem norm_deriv_damped_le {f : ℝ → ℂ} {q : ℂ} {d α t : ℝ}
    (hf : HasDerivAt f (q - d • f t - α • (Complex.I * f t)) t)
    (hy : DifferentiableAt ℝ (fun s => ‖f s‖) t) :
    deriv (fun s => ‖f s‖) t + d * ‖f t‖ ≤ ‖q‖ := by
  by_cases hz : f t = 0
  · have hm : IsLocalMin (fun s => ‖f s‖) t := by
      exact Filter.Eventually.of_forall (fun s => by
        simp only [hz, norm_zero]
        exact norm_nonneg _)
    rw [hm.deriv_eq_zero, hz, norm_zero, mul_zero, zero_add]
    exact norm_nonneg _
  · have hinner : inner ℝ (f t) (q - d • f t - α • (Complex.I * f t)) =
        inner ℝ (f t) q - d * ‖f t‖ ^ 2 := by
      simp only [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
      have h : inner ℝ (f t) (Complex.I * f t) = 0 :=
        real_inner_I_smul_self (𝕜 := ℂ) (f t)
      rw [h, mul_zero, sub_zero]
    have heq := hf.norm_sq.deriv
    have heq' : deriv (fun s => ‖f s‖ ^ 2) t =
        2 * ‖f t‖ * deriv (fun s => ‖f s‖) t := by
      have hd := (hy.hasDerivAt.pow 2).deriv
      have hfun : ((fun s => ‖f s‖) ^ 2) = (fun s => ‖f s‖ ^ 2) :=
        funext (fun s => Pi.pow_apply _ _ _)
      rw [hfun] at hd
      simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using hd
    have hi := real_inner_le_norm (f t) q
    rw [hinner] at heq
    have hpos : 0 < ‖f t‖ := norm_pos_iff.mpr hz
    have h : ‖f t‖ * (deriv (fun s => ‖f s‖) t + d * ‖f t‖) ≤ ‖f t‖ * ‖q‖ := by
      nlinarith only [heq, heq', hi]
    exact (mul_le_mul_iff_right₀ hpos).mp h

private theorem ae_norm_damped_le_of_identity
    {f q : ℝ → ℂ} {w d α : ℝ → ℝ} {a b p : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ t ∈ Ioo a b, p * (w t / ∫ s in a..t, w s) ≤ d t)
    (hidentity : ∀ t ∈ Ioo a b,
      HasDerivWithinAt f (q t - d t • f t - α t • (Complex.I * f t)) (Icc a b) t) :
    ∀ᵐ t ∂volume.restrict (Icc a b),
      deriv (fun s => ‖f s‖) t +
        p * (w t / (∫ s in a..t, w s) * ‖f t‖) ≤ ‖q t‖ := by
  have hy : AbsolutelyContinuousOnInterval (fun t => ‖f t‖) a b :=
    lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval hf
  have hne_a : ∀ᵐ t : ℝ, t ≠ a := by simp [ae_iff, measure_singleton]
  have hne_b : ∀ᵐ t : ℝ, t ≠ b := by simp [ae_iff, measure_singleton]
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hy.ae_differentiableAt, hne_a, hne_b] with t hyt hta htb ht
  have ht' : t ∈ Ioo a b :=
    ⟨lt_of_le_of_ne ht.1 hta.symm, lt_of_le_of_ne ht.2 htb⟩
  have hn := norm_deriv_damped_le
    ((hidentity t ht').hasDerivAt (Icc_mem_nhds ht'.1 ht'.2))
    (hyt (Icc_subset_uIcc ht))
  have hmul := mul_le_mul_of_nonneg_right (hd t ht') (norm_nonneg (f t))
  calc
    _ = deriv (fun s => ‖f s‖) t +
        (p * (w t / (∫ s in a..t, w s))) * ‖f t‖ := by ring
    _ ≤ deriv (fun s => ‖f s‖) t + d t * ‖f t‖ := add_le_add le_rfl hmul
    _ ≤ ‖q t‖ := hn

/-- Complex radial moment from its sectional differential identity.
The coefficient is exactly `1`, uniformly in the endpoints, curve, real
connection `α`, and all radial weights. The damping exponent is any `p > 0`.
The forcing needs only a measurable norm; its integral may be infinite. -/
theorem stab_radial_moment_of_identity
    {f q : ℝ → ℂ} {w d α : ℝ → ℝ} {a b p : ℝ}
    (hab : a ≤ b) (hp : 0 < p)
    (hw : IntervalIntegrable w volume a b) (hw0 : ∀ t ∈ Icc a b, 0 ≤ w t)
    (hf : AbsolutelyContinuousOnInterval f a b) (hfa : f a = 0)
    (hrb : 0 < ∫ s in a..b, w s)
    (hq : AEStronglyMeasurable (fun t => ‖q t‖) (volume.restrict (Ioc a b)))
    (hd : ∀ t ∈ Ioo a b, p * (w t / ∫ s in a..t, w s) ≤ d t)
    (hidentity : ∀ t ∈ Ioo a b,
      HasDerivWithinAt f (q t - d t • f t - α t • (Complex.I * f t)) (Icc a b) t) :
    ENNReal.ofReal ‖f b‖ ≤ ∫⁻ t in Ioc a b,
      ENNReal.ofReal (((∫ s in a..t, w s) / (∫ s in a..b, w s)) ^ p * ‖q t‖) := by
  apply ofReal_le_lintegral_damped_radial_kernel hab hp hw hw0
    (lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval hf)
    (by simp only [Function.comp_apply, hfa, norm_zero]) hrb hq (fun t _ => norm_nonneg _)
  exact ae_norm_damped_le_of_identity hf hd hidentity

/-- The weighted Hardy bound from the same complex sectional identity.
The coefficient is exactly `1/p`, uniformly in endpoints, curves, and the
real connection `α`. Integrability at the axis is obtained by comparison. -/
theorem stab_radial_hardy_of_identity
    {f q : ℝ → ℂ} {w d α : ℝ → ℝ} {a b p : ℝ}
    (hab : a ≤ b) (hp : 0 < p)
    (hw : IntervalIntegrable w volume a b) (hw0 : ∀ t ∈ Icc a b, 0 ≤ w t)
    (hf : AbsolutelyContinuousOnInterval f a b) (hfa : f a = 0)
    (hq : AEStronglyMeasurable (fun t => ‖q t‖) (volume.restrict (Ioc a b)))
    (hd : ∀ t ∈ Ioo a b, p * (w t / ∫ s in a..t, w s) ≤ d t)
    (hidentity : ∀ t ∈ Ioo a b,
      HasDerivWithinAt f (q t - d t • f t - α t • (Complex.I * f t)) (Icc a b) t) :
    (∫⁻ t in Ioc a b, ENNReal.ofReal (w t / (∫ s in a..t, w s) * ‖f t‖)) ≤
      ENNReal.ofReal p⁻¹ * ∫⁻ t in Ioc a b, ENNReal.ofReal ‖q t‖ := by
  apply lintegral_damped_radial_le hab hp hw hw0
    (lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval hf)
    (fun t _ => norm_nonneg _) (by simp only [Function.comp_apply, hfa, norm_zero]) hq
    (fun t _ => norm_nonneg _)
  exact ae_norm_damped_le_of_identity hf hd hidentity

end EmcsfAcExtension.Local
