module

public import EmcsfAcExtension.Global.Exterior.VariationTransportRepresentation

/-! # Classical incoming regularity of the prescribed density

For each fixed label the rough initial density is just one complex constant.
Continuous local transport coefficients and source therefore give a
classical incoming equation. At the original incoming boundary this is a
relative derivative; interior incoming points have a two-sided derivative.
This supplies approved internal project record (R3), `charged_SF_new_version.tex:L1410–L1416`.
-/

public section

open Set MeasureTheory Filter Topology Complex

namespace EmcsfAcExtension.Global.Exterior

/-- [internal] Continuous coefficients and forcing give the pointwise
incoming derivative of the explicit transport density at every time. The
initial label function is arbitrary and is never differentiated. -/
theorem hasDerivAt_transportDensity_of_continuous
    {C F : ℝ → ℝ → ℂ} (hC : Continuous C.uncurry) (hF : Continuous F.uncurry)
    (w : ℝ → ℂ) (a u v : ℝ) :
    HasDerivAt (fun x => Density.transportDensity C F w a x v)
      (C u v * Density.transportDensity C F w a u v + F u v) u := by
  let H : ℝ → ℂ := fun x => ∫ s in a..x, C s v
  have hCv : Continuous (fun x => C x v) :=
    hC.comp (continuous_id.prodMk continuous_const)
  have hFv : Continuous (fun x => F x v) :=
    hF.comp (continuous_id.prodMk continuous_const)
  have hH : Continuous H := (Density.continuous_incoming_primitive hC a).comp
    (continuous_id.prodMk continuous_const)
  have hdH : HasDerivAt H (C u v) u := intervalIntegral.integral_hasDerivAt_right
    (hCv.intervalIntegrable a u) (hCv.stronglyMeasurableAtFilter volume (𝓝 u))
    hCv.continuousAt
  have hq : Continuous (fun x => Complex.exp (-H x) * F x v) :=
    (Complex.continuous_exp.comp hH.neg).mul hFv
  have hdq := (intervalIntegral.integral_hasDerivAt_right (hq.intervalIntegrable a u)
    (hq.stronglyMeasurableAtFilter volume (𝓝 u)) hq.continuousAt).const_add (w v)
  have hd := hdH.cexp.mul hdq
  have he : Complex.exp (H u) * Complex.exp (-H u) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  apply hd.congr_deriv
  change Complex.exp (H u) * C u v *
      (w v + ∫ s in a..u, Complex.exp (-H s) * F s v) +
      Complex.exp (H u) * (Complex.exp (-H u) * F u v) = _
  rw [← mul_assoc (Complex.exp (H u)) (Complex.exp (-H u)), he, one_mul]
  dsimp only [Density.transportDensity, H]
  ring

/-- [node c:exterior#derivative-ac-representation]
For every label, the prescribed density has a continuous incoming right
side and the pointwise relative derivative on its entire proper history.
The initial row and stopped endpoint are included with their one-sided
derivative, without assumptions about fields outside the original domain. -/
theorem densityRepresentative_incoming_history_regularity
    {ui e a t v : ℝ} {S : Fields} (hS : IsSolution e S (origDomain ui))
    (hua : ui ≤ a) (hat : a ≤ t) (htv : t < v) (hv0 : v ≤ 0) :
    ContinuousOn (fun u => densityTransportCoefficient e S u v *
      densityRepresentative e S a u v + rawDensitySource e S u v) (Icc a t) ∧
    ∀ u ∈ Icc a t,
      HasDerivWithinAt (fun x => densityRepresentative e S a x v)
        (densityTransportCoefficient e S u v * densityRepresentative e S a u v +
          rawDensitySource e S u v) (Icc a t) u := by
  obtain ⟨x, y, hax, hy0, hrect, hpm, _⟩ := exists_proper_density_chart hua
    (show (t, v) ∈ densityVisibleDomain a from ⟨hat, htv, hv0⟩)
  obtain ⟨C, hC, hCe⟩ := Calculus.exists_continuous_rectangle_extension
    (f := densityTransportCoefficient e S)
    hax.le hy0.le (Calculus.continuousOn_density_coefficient hS hrect)
  obtain ⟨F, hF, hFe⟩ := Calculus.exists_continuous_rectangle_extension
    hax.le hy0.le (Calculus.continuousOn_rawDensitySource hS hrect)
  have hcan := Calculus.densityRepresentative_eq_transportDensity_of_coefficients
    hS hax hy0 hrect hC (fun p hp => hCe hp) hFe
  have hmem (u : ℝ) (hu : u ∈ Icc a t) : (u, v) ∈ Icc a x ×ˢ Icc y 0 :=
    ⟨⟨hu.1, hu.2.trans hpm.1.2⟩, hpm.2⟩
  have heq (u : ℝ) (hu : u ∈ Icc a t) : densityRepresentative e S a u v =
      Density.transportDensity C F (deriv (S.a a)) a u v :=
    hcan u (hmem u hu).1 v (hmem u hu).2
  have hc (u : ℝ) (hu : u ∈ Icc a t) : C u v = densityTransportCoefficient e S u v :=
    hCe (hmem u hu)
  have hf (u : ℝ) (hu : u ∈ Icc a t) : F u v = rawDensitySource e S u v :=
    hFe (hmem u hu)
  have hW : Continuous (fun u => Density.transportDensity C F (deriv (S.a a)) a u v) :=
    continuous_iff_continuousAt.2 fun u =>
      (hasDerivAt_transportDensity_of_continuous hC hF (deriv (S.a a)) a u v).continuousAt
  refine ⟨?_, ?_⟩
  · have hR : Continuous (fun u =>
        C u v * Density.transportDensity C F (deriv (S.a a)) a u v + F u v) :=
      ((hC.comp (continuous_id.prodMk continuous_const)).mul hW).add
        (hF.comp (continuous_id.prodMk continuous_const))
    apply hR.continuousOn.congr
    intro u hu
    dsimp only
    rw [← hc u hu, ← hf u hu, heq u hu]
  · intro u hu
    have hd' : HasDerivWithinAt (fun z => densityRepresentative e S a z v)
        (C u v * Density.transportDensity C F (deriv (S.a a)) a u v + F u v)
        (Icc a t) u :=
      (hasDerivAt_transportDensity_of_continuous hC hF
        (deriv (S.a a)) a u v).hasDerivWithinAt.congr_of_mem (fun z hz => heq z hz) hu
    rw [hc u hu, hf u hu, ← heq u hu] at hd'
    exact hd'

/-- [node c:exterior#derivative-ac-representation]
Every fixed label satisfies the classical incoming equation at each proper
incoming point strictly after its anchoring row. The common outgoing null
set is therefore more than sufficient for the blueprint's classical claim. -/
theorem densityRepresentative_hasDerivAt_incoming
    {ui e a u v : ℝ} {S : Fields} (hS : IsSolution e S (origDomain ui))
    (hua : ui ≤ a) (hau : a < u) (huv : u < v) (hv0 : v ≤ 0) :
    HasDerivAt (fun x => densityRepresentative e S a x v)
      (densityTransportCoefficient e S u v * densityRepresentative e S a u v +
        rawDensitySource e S u v) u := by
  let t : ℝ := (u + v) / 2
  have hut : u < t := by dsimp [t]; linarith
  have htv : t < v := by dsimp [t]; linarith
  exact ((densityRepresentative_incoming_history_regularity hS hua
    (hau.le.trans hut.le) htv hv0).2 u ⟨hau.le, hut.le⟩).hasDerivAt
      (Icc_mem_nhds hau hut)

end EmcsfAcExtension.Global.Exterior
