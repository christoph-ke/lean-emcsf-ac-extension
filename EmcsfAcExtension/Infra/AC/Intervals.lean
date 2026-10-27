module

public import EmcsfAcExtension.Infra.AC.Complex
public import EmcsfAcExtension.Infra.BV.Basic

/-!
# Concatenation of absolutely continuous intervals

The real gluing proof integrates the derivative on the two consecutive intervals.
The complex result follows by gluing real and imaginary parts. Restriction is supplied
by Mathlib's `AbsolutelyContinuousOnInterval.mono` and `BoundedVariationOn.mono`;
the BV gluing and exact variation additivity are in `Infra.BV.Basic`.
-/

public section

open Set MeasureTheory

namespace AbsolutelyContinuousOnInterval

/-- A real function AC on consecutive intervals is AC on their union. -/
theorem trans_real {f : ℝ → ℝ} {a b c : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval f b c)
    (hab : a ≤ b) (hbc : b ≤ c) : AbsolutelyContinuousOnInterval f a c := by
  apply (iff_exists_integral_real (hab.trans hbc)).mpr
  refine ⟨deriv f, hf.intervalIntegrable_deriv.trans hg.intervalIntegrable_deriv, ?_⟩
  intro x hx
  by_cases hxb : x ≤ b
  · have hsub : uIcc a x ⊆ uIcc a b := by
      rw [uIcc_of_le hx.1, uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl hxb
    rw [(hf.mono hsub).integral_deriv_eq_sub]
    abel
  · have hbx : b ≤ x := (lt_of_not_ge hxb).le
    have hsub : uIcc b x ⊆ uIcc b c := by
      rw [uIcc_of_le hbx, uIcc_of_le hbc]
      exact Icc_subset_Icc le_rfl hx.2
    rw [← intervalIntegral.integral_add_adjacent_intervals hf.intervalIntegrable_deriv
      (hg.intervalIntegrable_deriv.mono_set hsub), hf.integral_deriv_eq_sub,
      (hg.mono hsub).integral_deriv_eq_sub]
    abel

/-- A complex function AC on consecutive intervals is AC on their union. -/
theorem trans_complex {f : ℝ → ℂ} {a b c : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval f b c)
    (hab : a ≤ b) (hbc : b ≤ c) : AbsolutelyContinuousOnInterval f a c :=
  of_re_im (hf.re.trans_real hg.re hab hbc) (hf.im.trans_real hg.im hab hbc)

/-- The real FTC accepts an almost everywhere derivative of an AC function. -/
theorem integral_eq_sub_of_ae_hasDerivAt_real {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hfg : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f (g x) x) :
    (∫ x in a..b, g x) = f b - f a := by
  rw [← hf.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hfg] with x hx hmem
  exact (hx (uIoc_subset_uIcc hmem)).deriv.symm

end AbsolutelyContinuousOnInterval
