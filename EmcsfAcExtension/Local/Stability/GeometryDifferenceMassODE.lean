module

public import EmcsfAcExtension.Infra.DampedRadialExtended
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Real damped comparison for normalized mass

The normalized mass equation has positive linear damping. These analytic
helpers retain that damping in the absolute difference, including its
zero set, and give both the uniform and weighted estimates.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem abs_deriv_linear_aux {f : ℝ → ℝ} {q a t : ℝ}
    (hd : HasDerivAt f (q - a * f t) t)
    (_hy : DifferentiableAt ℝ (fun s => |f s|) t) :
    deriv (fun s => |f s|) t + a * |f t| ≤ |q| := by
  rcases lt_trichotomy (f t) 0 with hneg | hz | hpos
  · have hh := ((hasDerivAt_abs_neg hneg).comp t hd).deriv
    change deriv (fun s => |f s|) t = -1 * (q - a * f t) at hh
    rw [hh, abs_of_neg hneg]
    linarith only [neg_abs_le q]
  · have hmin : IsLocalMin (fun s => |f s|) t :=
      Filter.Eventually.of_forall (fun s => by simpa only [hz, abs_zero] using abs_nonneg (f s))
    rw [hmin.deriv_eq_zero, hz, abs_zero, mul_zero, add_zero]
    exact abs_nonneg q
  · have hh := ((hasDerivAt_abs_pos hpos).comp t hd).deriv
    change deriv (fun s => |f s|) t = 1 * (q - a * f t) at hh
    rw [hh, abs_of_pos hpos]
    linarith only [le_abs_self q]

/-- The absolute value of a real linear equation preserves any smaller
nonnegative damping coefficient, with literal constant `1`. No
integrability of the forcing is assumed in this conditional helper. -/
theorem stab_ae_abs_linear_damping
    {f q w d : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ t ∈ Ioo a b, w t / (∫ s in a..t, w s) ≤ d t)
    (hidentity : ∀ t ∈ Ioo a b,
      HasDerivWithinAt f (q t - d t * f t) (Icc a b) t) :
    ∀ᵐ t ∂volume.restrict (Icc a b),
      deriv (fun s => |f s|) t +
        w t / (∫ s in a..t, w s) * |f t| ≤ |q t| := by
  have hy : AbsolutelyContinuousOnInterval (fun s => |f s|) a b := by
    simpa only [Real.norm_eq_abs] using!
      lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval hf
  have hna : ∀ᵐ t : ℝ, t ≠ a := by simp [ae_iff, measure_singleton]
  have hnb : ∀ᵐ t : ℝ, t ≠ b := by simp [ae_iff, measure_singleton]
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hy.ae_differentiableAt, hna, hnb] with t hyt hta htb ht
  have ht' : t ∈ Ioo a b :=
    ⟨lt_of_le_of_ne ht.1 hta.symm, lt_of_le_of_ne ht.2 htb⟩
  exact (add_le_add le_rfl (mul_le_mul_of_nonneg_right (hd t ht') (abs_nonneg _))).trans
    (abs_deriv_linear_aux ((hidentity t ht').hasDerivAt (Icc_mem_nhds ht'.1 ht'.2))
      (hyt (Icc_subset_uIcc ht)))

/-- A real linear equation with at least the radial damping controls
its absolute weighted integral by the absolute forcing, with constant
`1` independent of the interval, weight and curves. -/
theorem stab_mass_hardy_of_identity
    {f q w d : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hw : IntervalIntegrable w volume a b)
    (hw0 : ∀ t ∈ Icc a b, 0 ≤ w t)
    (hf : AbsolutelyContinuousOnInterval f a b) (ha : f a = 0)
    (hq : AEStronglyMeasurable (fun t => |q t|) (volume.restrict (Ioc a b)))
    (hd : ∀ t ∈ Ioo a b, w t / (∫ s in a..t, w s) ≤ d t)
    (hidentity : ∀ t ∈ Ioo a b,
      HasDerivWithinAt f (q t - d t * f t) (Icc a b) t) :
    (∫⁻ t in Ioc a b, ENNReal.ofReal
      (w t / (∫ s in a..t, w s) * |f t|)) ≤
        ∫⁻ t in Ioc a b, ENNReal.ofReal |q t| := by
  have hy : AbsolutelyContinuousOnInterval (fun s => |f s|) a b := by
    simpa only [Real.norm_eq_abs] using!
      lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval hf
  have hh := lintegral_damped_radial_le (p := 1) hab (by norm_num) hw hw0 hy
    (fun t _ => abs_nonneg _) (by simp only [ha, abs_zero]) hq (fun t _ => abs_nonneg _)
    (by simpa only [one_mul] using stab_ae_abs_linear_damping hf hd hidentity)
  simpa only [inv_one, ENNReal.ofReal_one, one_mul] using hh

/-- The same damped real equation bounds the terminal absolute value
by the unweighted absolute forcing integral. The constant `1` is
uniform in every analytic parameter, including the terminal radius. -/
theorem stab_mass_point_of_identity
    {f q w d : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hw : IntervalIntegrable w volume a b)
    (hw0 : ∀ t ∈ Icc a b, 0 ≤ w t)
    (hf : AbsolutelyContinuousOnInterval f a b) (ha : f a = 0)
    (hrb : 0 < ∫ s in a..b, w s)
    (hq : AEStronglyMeasurable (fun t => |q t|) (volume.restrict (Ioc a b)))
    (hd : ∀ t ∈ Ioo a b, w t / (∫ s in a..t, w s) ≤ d t)
    (hidentity : ∀ t ∈ Ioo a b,
      HasDerivWithinAt f (q t - d t * f t) (Icc a b) t) :
    ENNReal.ofReal |f b| ≤ ∫⁻ t in Ioc a b, ENNReal.ofReal |q t| := by
  have hy : AbsolutelyContinuousOnInterval (fun s => |f s|) a b := by
    simpa only [Real.norm_eq_abs] using!
      lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval hf
  apply (ofReal_le_lintegral_damped_radial_kernel (p := 1) hab (by norm_num) hw hw0 hy
    (by simp only [ha, abs_zero]) hrb hq (fun t _ => abs_nonneg _)
    (by simpa only [one_mul] using stab_ae_abs_linear_damping hf hd hidentity)).trans
  apply setLIntegral_mono' measurableSet_Ioc
  intro t ht
  apply ENNReal.ofReal_le_ofReal
  rw [Real.rpow_one]
  apply mul_le_of_le_one_left (abs_nonneg _)
  apply (div_le_one hrb).mpr
  apply intervalIntegral.integral_mono_interval le_rfl ht.1.le ht.2 ?_ hw
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact hw0 s ⟨hs.1.le, hs.2⟩

end EmcsfAcExtension.Local
