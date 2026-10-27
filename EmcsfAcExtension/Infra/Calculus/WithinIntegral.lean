/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Infra.Calculus.PartialsC1

/-! # Leibniz differentiation on closed rectangles

internal project record infrastructure. Source functions and their parameter derivatives are
assumed regular only within the given closed rectangle. The parameter may be
an endpoint: no extension of the source outside the rectangle is assumed.
-/

public section

namespace EmcsfAcExtension

open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem continuousOn_integral_section {F : ℝ → ℝ → E} {a b c d : ℝ}
    (hF : ContinuousOn (Function.uncurry F) (Icc a b ×ˢ uIcc c d)) :
    ContinuousOn (fun x => ∫ t in c..d, F x t) (Icc a b) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_uIcc).exists_bound_of_continuousOn hF
  have hsec (x : ℝ) (hx : x ∈ Icc a b) : ContinuousOn (F x) (uIcc c d) :=
    hF.comp (continuousOn_const.prodMk continuousOn_id) (fun _ ht => ⟨hx, ht⟩)
  intro x hx
  apply intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun _ => C)
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact ((hsec y hy).aestronglyMeasurable measurableSet_uIcc).mono_set uIoc_subset_uIcc
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact Filter.Eventually.of_forall (fun t ht => hC (y, t) ⟨hy, uIoc_subset_uIcc ht⟩)
  · exact intervalIntegrable_const
  · apply Filter.Eventually.of_forall
    intro t ht
    exact (hF.comp (continuousOn_id.prodMk continuousOn_const)
      (fun _ hy => ⟨hy, uIoc_subset_uIcc ht⟩)) x hx

/-- Leibniz differentiation within the closed parameter interval `[a,b]`.
The source and its continuous parameter partial are required only on
`Icc a b × uIcc c d`. Compactness supplies uniform domination. -/
theorem hasDerivWithinAt_integral_rectangle {F F' : ℝ → ℝ → E} {a b c d x : ℝ}
    (hab : a < b)
    (hF : ContinuousOn (Function.uncurry F) (Icc a b ×ˢ uIcc c d))
    (hF' : ContinuousOn (Function.uncurry F') (Icc a b ×ˢ uIcc c d))
    (hd : ∀ y ∈ Icc a b, ∀ t ∈ uIcc c d,
      HasDerivWithinAt (fun z => F z t) (F' y t) (Icc a b) y)
    (hx : x ∈ Icc a b) :
    HasDerivWithinAt (fun y => ∫ t in c..d, F y t)
      (∫ t in c..d, F' x t) (Icc a b) x := by
  let J (y : ℝ) := ∫ t in c..d, F y t
  let K (y : ℝ) := ∫ t in c..d, F' y t
  have cJ : ContinuousOn J (Icc a b) := continuousOn_integral_section hF
  have cK : ContinuousOn K (Icc a b) := continuousOn_integral_section hF'
  have hsec (y : ℝ) (hy : y ∈ Icc a b) : ContinuousOn (F y) (uIcc c d) :=
    hF.comp (continuousOn_const.prodMk continuousOn_id) (fun _ ht => ⟨hy, ht⟩)
  have hsec' (y : ℝ) (hy : y ∈ Icc a b) : ContinuousOn (F' y) (uIcc c d) :=
    hF'.comp (continuousOn_const.prodMk continuousOn_id) (fun _ ht => ⟨hy, ht⟩)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_uIcc).exists_bound_of_continuousOn hF'
  have hInt : ∀ y ∈ Ioo a b, HasDerivAt J (K y) y := by
    intro y hy
    apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (s := Ioo a b) (bound := fun _ => C) (Ioo_mem_nhds hy.1 hy.2)
      ?_ ((hsec y ⟨hy.1.le, hy.2.le⟩).intervalIntegrable)
      (((hsec' y ⟨hy.1.le, hy.2.le⟩).aestronglyMeasurable measurableSet_uIcc).mono_set
        uIoc_subset_uIcc)
      ?_ intervalIntegrable_const ?_).2
    · filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
      exact ((hsec z ⟨hz.1.le, hz.2.le⟩).aestronglyMeasurable measurableSet_uIcc).mono_set
        uIoc_subset_uIcc
    · exact Filter.Eventually.of_forall (fun t ht z hz =>
        hC (z, t) ⟨⟨hz.1.le, hz.2.le⟩, uIoc_subset_uIcc ht⟩)
    · exact Filter.Eventually.of_forall (fun t ht z hz =>
        (hd z ⟨hz.1.le, hz.2.le⟩ t (uIoc_subset_uIcc ht)).hasDerivAt
          (Icc_mem_nhds hz.1 hz.2))
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt, ← closure_Ioo hab.ne]
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun y hy => (hInt y hy).differentiableAt.differentiableWithinAt)
    (convex_Ioo a b) isOpen_Ioo
  · intro y hy
    rw [closure_Ioo hab.ne] at hy
    exact (cJ y hy).mono Ioo_subset_Icc_self
  · have hL : ContinuousOn (fun y => toSpanSingleton ℝ (K y)) (Icc a b) :=
      (toSpanSingletonCLE : E ≃L[ℝ] (ℝ →L[ℝ] E)).continuous.comp_continuousOn cK
    apply Filter.Tendsto.congr' _ ((hL x hx).mono Ioo_subset_Icc_self)
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hInt y hy).hasFDerivAt.fderiv.symm

/-- A closed-domain integral representation can be differentiated within its
parameter interval, with the trace term differentiated separately. -/
theorem hasDerivWithinAt_of_integral_representation_rectangle
    {F F' : ℝ → ℝ → E} {G B : ℝ → E} {B' : E} {a b c d x : ℝ}
    (hab : a < b)
    (hF : ContinuousOn (Function.uncurry F) (Icc a b ×ˢ uIcc c d))
    (hF' : ContinuousOn (Function.uncurry F') (Icc a b ×ˢ uIcc c d))
    (hd : ∀ y ∈ Icc a b, ∀ t ∈ uIcc c d,
      HasDerivWithinAt (fun z => F z t) (F' y t) (Icc a b) y)
    (hx : x ∈ Icc a b) (hB : HasDerivWithinAt B B' (Icc a b) x)
    (hrep : EqOn G (fun y => B y + ∫ t in c..d, F y t) (Icc a b)) :
    HasDerivWithinAt G (B' + ∫ t in c..d, F' x t) (Icc a b) x :=
  (hB.add (hasDerivWithinAt_integral_rectangle hab hF hF' hd hx)).congr hrep (hrep hx)

end EmcsfAcExtension
