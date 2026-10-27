module

public import Mathlib
import EmcsfAcExtension.Infra.AC.Variation

/-! # Characteristic variation from an integrable interior speed bound

The continuous primitive is retained at both endpoints. An integrable speed
majorant supplies its integral representation, hence absolute continuity and
variation, without differentiating a radius quotient on the axis.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

/-- A continuous real curve with a continuous interior derivative and an
integrable majorant of its speed is AC on the complete interval, and its
variation is bounded by the integral of that majorant. The exact coefficient
one is uniform in all functions and endpoints. No endpoint derivative is
assumed. This is the endpoint repair in approved internal project record (38). -/
theorem ac_and_variation_le_of_interior_speed {a b : ℝ} {f g B : ℝ → ℝ}
    (hab : a ≤ b) (cf : ContinuousOn f (Icc a b)) (cg : ContinuousOn g (Ioo a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x)
    (iB : IntervalIntegrable B volume a b) (hB : ∀ x ∈ Ioo a b, |g x| ≤ B x) :
    AbsolutelyContinuousOnInterval f a b ∧
      eVariationOn f (Icc a b) ≤ ENNReal.ofReal (∫ x in a..b, B x) := by
  have mg : AEStronglyMeasurable g (volume.restrict (Icc a b)) := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact cg.aestronglyMeasurable measurableSet_Ioo
  have hspeed : ∀ᵐ x ∂volume.restrict (Icc a b), ‖g x‖ ≤ B x := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simpa only [Real.norm_eq_abs] using hB x hx
  have ig : IntervalIntegrable g volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp iB).mono' mg hspeed)
  have hfg (x : ℝ) (hx : x ∈ Icc a b) : f x = f a + ∫ t in a..x, g t := by
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
      (cf.mono (Icc_subset_Icc le_rfl hx.2))
      (fun t ht => hd t ⟨ht.1, ht.2.trans_le hx.2⟩)
      (ig.mono_set (by rw [uIcc_of_le hx.1, uIcc_of_le hab]
                       exact Icc_subset_Icc le_rfl hx.2))
    linarith only [hi]
  have hp := ig.absolutelyContinuousOnInterval_intervalIntegral_normed left_mem_uIcc
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => f a) a b :=
    (LipschitzWith.const (f a)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hac := (hc.fun_add hp).congr
    (fun x hx => (hfg x (by simpa only [uIcc_of_le hab] using hx)).symm)
  refine ⟨hac, ?_⟩
  rw [ig.eVariationOn_eq_integral_norm_of_eq_integral hab hfg]
  apply ENNReal.ofReal_le_ofReal
  exact intervalIntegral.integral_mono_ae_restrict hab ig.norm iB hspeed

end EmcsfAcExtension.Local
