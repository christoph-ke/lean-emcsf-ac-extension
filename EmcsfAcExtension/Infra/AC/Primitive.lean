module

public import EmcsfAcExtension.Infra.AC.Complex
public import EmcsfAcExtension.Infra.BV.Deriv

/-!
# Normed space primitives and finite dimensional AC calculus

An integrable density has an AC primitive: its increments are dominated by those
of the real primitive of its norm. Together with BV derivative integrability,
this gives the fundamental theorem for finite dimensional real normed targets,
including both real and complex scalars.
-/

public section

open Set Filter MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An integrable normed space valued density has an absolutely continuous primitive. -/
theorem IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_normed
    {g : ℝ → E} {a b c : ℝ} (hg : IntervalIntegrable g volume a b) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ t in c..x, g t) a b := by
  have hnorm := hg.norm.absolutelyContinuousOnInterval_intervalIntegral hc
  rw [absolutelyContinuousOnInterval_iff] at hnorm ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := hnorm ε hε
  refine ⟨δ, hδ, ?_⟩
  rintro ⟨n, I⟩ hI hlen
  apply lt_of_le_of_lt _ (hδε (n, I) hI hlen)
  apply Finset.sum_le_sum
  intro i hi
  have hx := hg.mono_set (uIcc_subset_uIcc hc (hI.1 i hi).1)
  have hy := hg.mono_set (uIcc_subset_uIcc hc (hI.1 i hi).2)
  rw [dist_eq_norm, intervalIntegral.integral_interval_sub_left hx hy,
    Real.dist_eq, intervalIntegral.integral_interval_sub_left hx.norm hy.norm]
  exact intervalIntegral.norm_integral_le_abs_integral_norm

namespace AbsolutelyContinuousOnInterval

/-- The normed space FTC with a specified integrable almost everywhere derivative. -/
theorem integral_eq_sub_of_ae_hasDerivAt_normed [CompleteSpace E]
    {f g : ℝ → E} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : IntervalIntegrable g volume a b)
    (hfg : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f (g x) x) :
    (∫ x in a..b, g x) = f b - f a := by
  have hp := hg.absolutelyContinuousOnInterval_intervalIntegral_normed left_mem_uIcc
  have hz : ∀ᵐ x, x ∈ uIcc a b →
      HasDerivAt (fun y => f y - ∫ t in a..y, g t) 0 x := by
    filter_upwards [hfg, hg.ae_hasDerivAt_integral] with x hx hy hmem
    simpa only [sub_self, Pi.sub_apply] using!
      (hx hmem).sub (hy hmem a left_mem_uIcc)
  obtain ⟨C, hC⟩ := (hf.sub hp).const_of_ae_hasDerivAt_zero hz
  have ha := hC a left_mem_uIcc
  have hb := hC b right_mem_uIcc
  simp only [Pi.sub_apply, intervalIntegral.integral_same, sub_zero] at ha hb
  rw [← ha] at hb
  calc
    (∫ x in a..b, g x) = f b - (f b - ∫ x in a..b, g x) := by abel
    _ = f b - f a := by rw [hb]

variable [FiniteDimensional ℝ E]

/-- The derivative of an AC curve in a finite dimensional real space is integrable. -/
theorem intervalIntegrable_deriv_finiteDimensional {f : ℝ → E} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    IntervalIntegrable (deriv f) volume a b := by
  rcases le_total a b with hab | hba
  · exact (by simpa only [uIcc_of_le hab] using hf.boundedVariationOn :
      BoundedVariationOn f (Icc a b)).intervalIntegrable_deriv_finiteDimensional hab
  · exact ((by simpa only [uIcc_of_ge hba] using hf.boundedVariationOn :
      BoundedVariationOn f (Icc b a)).intervalIntegrable_deriv_finiteDimensional hba).symm

/-- Fundamental theorem of calculus for finite dimensional real normed targets. -/
theorem integral_deriv_eq_sub_finiteDimensional {f : ℝ → E} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    (∫ x in a..b, deriv f x) = f b - f a :=
  hf.integral_eq_sub_of_ae_hasDerivAt_normed hf.intervalIntegrable_deriv_finiteDimensional
    (hf.ae_differentiableAt_of_mem_uIcc.mono fun _ hx hmem => (hx hmem).hasDerivAt)

end AbsolutelyContinuousOnInterval
