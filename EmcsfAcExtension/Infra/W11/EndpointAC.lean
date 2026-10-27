module

public import EmcsfAcExtension.Infra.AC.Variation

/-!
# Absolute continuity at the final endpoint

Local absolute continuity on every initial compact segment and integrability of
its derivative give a primitive representation on the half-open interval.
Continuity at the final endpoint extends that representation to the closed segment.
A uniform finite variation bound on the initial segments also suffices, because
it gives bounded variation and hence derivative integrability on the closed segment.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.W11

/-- The integral representation extends to the closed interval from local AC and
an integrable derivative on the half-open interval. No quantitative constant is used. -/
theorem eq_integral_of_local_ac {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b))
    (hloc : ∀ c ∈ Ico a b, AbsolutelyContinuousOnInterval f a c)
    (hd : IntegrableOn (deriv f) (Ico a b)) :
    ∀ x ∈ Icc a b, f x = f a + ∫ t in a..x, deriv f t := by
  rcases hab.eq_or_lt with rfl | hab
  · intro x hx
    have hxa : x = a := by simpa only [Icc_self, mem_singleton_iff] using hx
    subst x
    simp
  have hi : IntervalIntegrable (deriv f) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ico_of_le hab.le).2 hd
  have hp := hi.absolutelyContinuousOnInterval_intervalIntegral_normed left_mem_uIcc
  have hpc : ContinuousOn (fun x => f a + ∫ t in a..x, deriv f t) (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using! continuousOn_const.add hp.continuousOn
  have heq : EqOn f (fun x => f a + ∫ t in a..x, deriv f t) (Ico a b) := by
    intro x hx
    dsimp only
    rw [(hloc x hx).integral_deriv_eq_sub_complex]
    abel
  exact heq.of_subset_closure hc hpc Ico_subset_Icc_self
    (by rw [closure_Ico hab.ne])

/-- Local AC and a half-open integrable derivative imply AC on the closed interval,
provided the curve is continuous there. -/
theorem ac_of_local_ac_of_integrableOn_deriv {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b))
    (hloc : ∀ c ∈ Ico a b, AbsolutelyContinuousOnInterval f a c)
    (hd : IntegrableOn (deriv f) (Ico a b)) :
    AbsolutelyContinuousOnInterval f a b := by
  apply (AbsolutelyContinuousOnInterval.iff_exists_integral_complex hab).2
  exact ⟨deriv f, (intervalIntegrable_iff_integrableOn_Ico_of_le hab).2 hd,
    eq_integral_of_local_ac hab hc hloc hd⟩

/-- A uniform extended variation bound on initial segments bounds the half-open
variation, with coefficient one independent of the curve, interval, and bound. -/
theorem eVariationOn_Ico_le_of_initial_bounds {f : ℝ → ℂ} {a b : ℝ} {C : ℝ≥0∞}
    (hC : ∀ c ∈ Ico a b, eVariationOn f (Icc a c) ≤ C) :
    eVariationOn f (Ico a b) ≤ C := by
  rw [eVariationOn.eVariationOn_eq_strictMonoOn]
  apply iSup_le
  rintro ⟨n, u, hu, hs⟩
  apply le_trans (eVariationOn.sum_le_of_monotoneOn_Iic hu.monotoneOn ?_)
    (hC (u n) (hs n (mem_Iic.mpr le_rfl)))
  intro i hi
  exact ⟨(hs i hi).1, hu.monotoneOn hi (mem_Iic.mpr le_rfl) (mem_Iic.mp hi)⟩

/-- Continuity at the endpoint passes a uniform finite variation bound from the
initial segments to the full closed interval. The coefficient one is universal. -/
theorem boundedVariationOn_of_initial_bounds {f : ℝ → ℂ} {a b : ℝ} {C : ℝ≥0∞}
    (hab : a ≤ b) (hc : ContinuousOn f (Icc a b)) (hCfin : C ≠ ⊤)
    (hC : ∀ c ∈ Ico a b, eVariationOn f (Icc a c) ≤ C) :
    BoundedVariationOn f (Icc a b) := by
  rcases hab.eq_or_lt with rfl | hab
  · simp only [Icc_self]
    exact BoundedVariationOn.of_subsingleton (f := f) subsingleton_singleton
  have heq := eVariationOn.eVariationOn_Ico_eq_Icc_of_continuousWithinAt (a := b) (b := a)
    ((continuousWithinAt_Icc_iff_Iic hab).1 (hc b (right_mem_Icc.mpr hab.le)))
  exact ne_top_of_le_ne_top hCfin (heq ▸ eVariationOn_Ico_le_of_initial_bounds hC)

/-- Continuous, locally AC curves with uniformly finite initial variation are AC
up to the final endpoint. No modulus or equiintegrability assumption is added. -/
theorem ac_of_local_ac_of_initial_variation_bounds {f : ℝ → ℂ} {a b : ℝ} {C : ℝ≥0∞}
    (hab : a ≤ b) (hc : ContinuousOn f (Icc a b))
    (hloc : ∀ c ∈ Ico a b, AbsolutelyContinuousOnInterval f a c)
    (hCfin : C ≠ ⊤) (hC : ∀ c ∈ Ico a b, eVariationOn f (Icc a c) ≤ C) :
    AbsolutelyContinuousOnInterval f a b := by
  have hd := (boundedVariationOn_of_initial_bounds hab hc hCfin hC
    ).intervalIntegrable_deriv_finiteDimensional hab
  exact ac_of_local_ac_of_integrableOn_deriv hab hc hloc
    ((intervalIntegrable_iff_integrableOn_Ico_of_le hab).1 hd)

end EmcsfAcExtension.W11
