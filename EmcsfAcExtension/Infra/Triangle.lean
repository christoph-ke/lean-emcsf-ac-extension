/- Copyright (c) 2026. All rights reserved. -/

module

public import EmcsfAcExtension.Frozen.Triangle

/-!
# Ordered triangle integration

Fubini and Tonelli on the frozen closed triangle `{a ≤ u ≤ v ≤ b}`.
Integrability is required only on the triangle, so integrable singular kernels are allowed.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension

/-- The frozen ordered triangle is closed. -/
theorem isClosed_triangle (a b : ℝ) : IsClosed (triangle a b) :=
  (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_fst continuous_snd).inter
      (isClosed_le continuous_snd continuous_const))

/-- The frozen ordered triangle is measurable. -/
theorem measurableSet_triangle (a b : ℝ) : MeasurableSet (triangle a b) :=
  (isClosed_triangle a b).measurableSet

/-- The frozen ordered triangle is compact, including when it is empty. -/
theorem isCompact_triangle (a b : ℝ) : IsCompact (triangle a b) := by
  apply ((isCompact_Icc : IsCompact (Icc a b)).prod
    (isCompact_Icc : IsCompact (Icc a b))).of_isClosed_subset (isClosed_triangle a b)
  rintro ⟨u, v⟩ ⟨hau, huv, hvb⟩
  exact ⟨⟨hau, huv.trans hvb⟩, ⟨hau.trans huv, hvb⟩⟩

private theorem triangle_indicator_left {E : Type*} [Zero E] (F : ℝ × ℝ → E)
    (a b u v : ℝ) :
    (triangle a b).indicator F (u, v) =
      (Icc a b).indicator (fun u => (Icc u b).indicator (fun v => F (u, v)) v) u := by
  classical
  simp only [indicator_apply, triangle, mem_ofPred_eq, mem_Icc]
  split_ifs <;> first | rfl | grind

private theorem triangle_indicator_right {E : Type*} [Zero E] (F : ℝ × ℝ → E)
    (a b u v : ℝ) :
    (triangle a b).indicator F (u, v) =
      (Icc a b).indicator (fun v => (Icc a v).indicator (fun u => F (u, v)) u) v := by
  classical
  simp only [indicator_apply, triangle, mem_ofPred_eq, mem_Icc]
  split_ifs <;> first | rfl | grind

private theorem integral_triangle_indicator_left {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : ℝ × ℝ → E) (a b : ℝ) :
    (∫ u, ∫ v, (triangle a b).indicator F (u, v)) =
      ∫ u in Icc a b, ∫ v in Icc u b, F (u, v) := by
  classical
  simp_rw [triangle_indicator_left]
  simp_rw [integral_indicator₂, integral_indicator measurableSet_Icc]

private theorem integral_triangle_indicator_right {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : ℝ × ℝ → E) (a b : ℝ) :
    (∫ v, ∫ u, (triangle a b).indicator F (u, v)) =
      ∫ v in Icc a b, ∫ u in Icc a v, F (u, v) := by
  classical
  simp_rw [triangle_indicator_right]
  simp_rw [integral_indicator₂, integral_indicator measurableSet_Icc]

/-- Integrating on the triangle by outgoing sections. -/
theorem integral_triangle_eq_integral_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {F : ℝ × ℝ → E} {a b : ℝ}
    (hF : IntegrableOn F (triangle a b) (volume.prod volume)) :
    (∫ p in triangle a b, F p ∂(volume.prod volume)) =
      ∫ u in Icc a b, ∫ v in Icc u b, F (u, v) := by
  rw [← integral_indicator (measurableSet_triangle a b)]
  rw [integral_prod _ (hF.integrable_indicator (measurableSet_triangle a b))]
  exact integral_triangle_indicator_left F a b

/-- Integrating on the triangle by incoming sections. -/
theorem integral_triangle_eq_integral_integral_symm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {F : ℝ × ℝ → E} {a b : ℝ}
    (hF : IntegrableOn F (triangle a b) (volume.prod volume)) :
    (∫ p in triangle a b, F p ∂(volume.prod volume)) =
      ∫ v in Icc a b, ∫ u in Icc a v, F (u, v) := by
  rw [← integral_indicator (measurableSet_triangle a b)]
  rw [integral_prod_symm _ (hF.integrable_indicator (measurableSet_triangle a b))]
  exact integral_triangle_indicator_right F a b

/-- Fubini on the closed triangle in the two displayed orders, in set-integral form. -/
theorem integral_integral_swap_triangle_set {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {F : ℝ × ℝ → E} {a b : ℝ}
    (hF : IntegrableOn F (triangle a b) (volume.prod volume)) :
    (∫ u in Icc a b, ∫ v in Icc u b, F (u, v)) =
      ∫ v in Icc a b, ∫ u in Icc a v, F (u, v) :=
  (integral_triangle_eq_integral_integral hF).symm.trans
    (integral_triangle_eq_integral_integral_symm hF)

/-- Fubini on the triangle, with oriented interval integrals and the order explicit. -/
theorem integral_integral_swap_triangle {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {F : ℝ × ℝ → E} {a b : ℝ}
    (hab : a ≤ b) (hF : IntegrableOn F (triangle a b) (volume.prod volume)) :
    (∫ u in a..b, ∫ v in u..b, F (u, v)) =
      ∫ v in a..b, ∫ u in a..v, F (u, v) := by
  have hleft : (∫ u in Icc a b, ∫ v in Icc u b, F (u, v)) =
      ∫ u in a..b, ∫ v in u..b, F (u, v) := by
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    dsimp only
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hu.2]
  have hright : (∫ v in Icc a b, ∫ u in Icc a v, F (u, v)) =
      ∫ v in a..b, ∫ u in a..v, F (u, v) := by
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro v hv
    dsimp only
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hv.1.le]
  rw [← hleft, ← hright]
  exact integral_integral_swap_triangle_set hF

/-- Almost every outgoing section of a triangle-integrable function is integrable. -/
theorem ae_integrableOn_triangle_left {E : Type*} [NormedAddCommGroup E]
    {F : ℝ × ℝ → E} {a b : ℝ}
    (hF : IntegrableOn F (triangle a b) (volume.prod volume)) :
    ∀ᵐ u ∂volume.restrict (Icc a b), IntegrableOn (fun v => F (u, v)) (Icc u b) := by
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  filter_upwards [(hF.integrable_indicator (measurableSet_triangle a b)).prod_right_ae]
    with u hu humem
  have heq : (fun v => (triangle a b).indicator F (u, v)) =
      (Icc u b).indicator (fun v => F (u, v)) := by
    funext v
    rw [triangle_indicator_left, indicator_of_mem humem]
  rw [heq] at hu
  exact (integrable_indicator_iff measurableSet_Icc).mp hu

/-- Almost every incoming section of a triangle-integrable function is integrable. -/
theorem ae_integrableOn_triangle_right {E : Type*} [NormedAddCommGroup E]
    {F : ℝ × ℝ → E} {a b : ℝ}
    (hF : IntegrableOn F (triangle a b) (volume.prod volume)) :
    ∀ᵐ v ∂volume.restrict (Icc a b), IntegrableOn (fun u => F (u, v)) (Icc a v) := by
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  filter_upwards [(hF.integrable_indicator (measurableSet_triangle a b)).prod_left_ae]
    with v hv hvmem
  have heq : (fun u => (triangle a b).indicator F (u, v)) =
      (Icc a v).indicator (fun u => F (u, v)) := by
    funext u
    rw [triangle_indicator_right, indicator_of_mem hvmem]
  rw [heq] at hv
  exact (integrable_indicator_iff measurableSet_Icc).mp hv

/-- Almost every outgoing section is interval integrable, with its displayed endpoints. -/
theorem ae_intervalIntegrable_triangle_left {E : Type*} [NormedAddCommGroup E]
    {F : ℝ × ℝ → E} {a b : ℝ}
    (hF : IntegrableOn F (triangle a b) (volume.prod volume)) :
    ∀ᵐ u ∂volume.restrict (Icc a b), IntervalIntegrable (fun v => F (u, v)) volume u b := by
  filter_upwards [ae_integrableOn_triangle_left hF, ae_restrict_mem measurableSet_Icc]
    with u hu humem
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le humem.2).mpr hu

/-- Almost every incoming section is interval integrable, with its displayed endpoints. -/
theorem ae_intervalIntegrable_triangle_right {E : Type*} [NormedAddCommGroup E]
    {F : ℝ × ℝ → E} {a b : ℝ}
    (hF : IntegrableOn F (triangle a b) (volume.prod volume)) :
    ∀ᵐ v ∂volume.restrict (Icc a b), IntervalIntegrable (fun u => F (u, v)) volume a v := by
  filter_upwards [ae_integrableOn_triangle_right hF, ae_restrict_mem measurableSet_Icc]
    with v hv hvmem
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hvmem.1).mpr hv

private theorem lintegral_triangle_indicator_left (F : ℝ × ℝ → ℝ≥0∞) (a b : ℝ) :
    (∫⁻ u, ∫⁻ v, (triangle a b).indicator F (u, v)) =
      ∫⁻ u in Icc a b, ∫⁻ v in Icc u b, F (u, v) := by
  classical
  rw [← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro u
  simp_rw [triangle_indicator_left]
  by_cases hu : u ∈ Icc a b
  · simp only [indicator_of_mem hu, lintegral_indicator measurableSet_Icc]
  · simp only [indicator_of_notMem hu, lintegral_zero]

private theorem lintegral_triangle_indicator_right (F : ℝ × ℝ → ℝ≥0∞) (a b : ℝ) :
    (∫⁻ v, ∫⁻ u, (triangle a b).indicator F (u, v)) =
      ∫⁻ v in Icc a b, ∫⁻ u in Icc a v, F (u, v) := by
  classical
  rw [← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro v
  simp_rw [triangle_indicator_right]
  by_cases hv : v ∈ Icc a b
  · simp only [indicator_of_mem hv, lintegral_indicator measurableSet_Icc]
  · simp only [indicator_of_notMem hv, lintegral_zero]

/-- Tonelli on the triangle in outgoing order, without any finiteness assumption. -/
theorem lintegral_triangle_eq_lintegral_lintegral {F : ℝ × ℝ → ℝ≥0∞} {a b : ℝ}
    (hF : Measurable F) :
    (∫⁻ p in triangle a b, F p ∂(volume.prod volume)) =
      ∫⁻ u in Icc a b, ∫⁻ v in Icc u b, F (u, v) := by
  rw [← lintegral_indicator (measurableSet_triangle a b),
    lintegral_prod _ (hF.indicator (measurableSet_triangle a b)).aemeasurable]
  exact lintegral_triangle_indicator_left F a b

/-- Tonelli on the triangle in incoming order, without any finiteness assumption. -/
theorem lintegral_triangle_eq_lintegral_lintegral_symm {F : ℝ × ℝ → ℝ≥0∞} {a b : ℝ}
    (hF : Measurable F) :
    (∫⁻ p in triangle a b, F p ∂(volume.prod volume)) =
      ∫⁻ v in Icc a b, ∫⁻ u in Icc a v, F (u, v) := by
  rw [← lintegral_indicator (measurableSet_triangle a b),
    lintegral_prod_symm _ (hF.indicator (measurableSet_triangle a b)).aemeasurable]
  exact lintegral_triangle_indicator_right F a b

/-- Tonelli exchanges the displayed orders on the triangle for measurable nonnegative
extended-real integrands. The integrals are permitted to be infinite. -/
theorem lintegral_lintegral_swap_triangle {F : ℝ × ℝ → ℝ≥0∞} {a b : ℝ}
    (hF : Measurable F) :
    (∫⁻ u in Icc a b, ∫⁻ v in Icc u b, F (u, v)) =
      ∫⁻ v in Icc a b, ∫⁻ u in Icc a v, F (u, v) :=
  (lintegral_triangle_eq_lintegral_lintegral hF).symm.trans
    (lintegral_triangle_eq_lintegral_lintegral_symm hF)


/-- The Lebesgue area of the closed triangle is `(b - a)² / 2`. -/
theorem volume_triangle {a b : ℝ} (hab : a ≤ b) :
    volume (triangle a b) = ENNReal.ofReal ((b - a) ^ 2 / 2) := by
  rw [Measure.volume_eq_prod]
  have hfin := (isCompact_triangle a b).measure_lt_top (μ := volume.prod volume)
  have hF : IntegrableOn (fun _ : ℝ × ℝ => (1 : ℝ)) (triangle a b) (volume.prod volume) :=
    integrableOn_const hfin.ne
  have hi := integral_triangle_eq_integral_integral hF
  rw [setIntegral_one_eq_measureReal] at hi
  have hinner : (∫ u in Icc a b, ∫ v in Icc u b, (1 : ℝ)) = (b - a)^2 / 2 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    have heq : (∫ u in a..b, ∫ v in Icc u b, (1 : ℝ)) = ∫ u in a..b, b - u := by
      apply intervalIntegral.integral_congr
      intro u hu
      dsimp only
      rw [uIcc_of_le hab] at hu
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hu.2]
      simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
    rw [heq, intervalIntegral.integral_sub (f := fun _ : ℝ => b) (g := fun u : ℝ => u)
      intervalIntegrable_const (continuous_id.intervalIntegrable a b)]
    rw [intervalIntegral.integral_const, integral_id]
    simp only [smul_eq_mul]
    ring
  rw [hinner] at hi
  change ((volume.prod volume) (triangle a b)).toReal = (b - a)^2 / 2 at hi
  calc
    _ = ENNReal.ofReal (((volume.prod volume) (triangle a b)).toReal) :=
      (ENNReal.ofReal_toReal hfin.ne).symm
    _ = _ := congrArg ENNReal.ofReal hi

end EmcsfAcExtension
