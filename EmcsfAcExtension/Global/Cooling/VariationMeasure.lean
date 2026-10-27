/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Global.Defs.Curves
public import EmcsfAcExtension.Global.Defs.Original
import EmcsfAcExtension.Global.Calculus.Gauge
import EmcsfAcExtension.Global.Api.Integrals
import EmcsfAcExtension.Infra.AC.Variation

/-! # The finite covariant variation measure

The density is the speed in a fixed parallel frame on the proper clock
interval (`charged_SF_new_version.tex:L2918–L2922`). Reanchoring that frame multiplies
it by a single unit complex number. Thus restriction to a subinterval has
exactly that subinterval's covariant variation, with no duration constant.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.Cooling

/-- [def-node prop:charged-cool#covariant-variation-measure]
The positive measure with density equal to the speed of the parallel
representative, restricted to its clock interval. -/
noncomputable def covariantVariationMeasure (e : ℝ) (S : Fields)
    (f : ℝ → ℝ → ℂ) (U V : ℝ → ℝ) (s t : ℝ) : Measure ℝ :=
  (volume.restrict (Icc s t)).withDensity
    (fun x => ‖deriv (curveParallel e S f U V s) x‖ₑ)

/-- [internal] The pulled-back connection is integrable on every proper
clock cylinder. Its bound is local; no uniform bound is assumed. -/
theorem connection_intervalIntegrable {ui e b s t : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hst : s ≤ t)
    (γ : ClockCylinder S (origDomain ui) b s t) :
    IntervalIntegrable (fun x => S.A (γ.U x) (γ.V x) * deriv γ.U x) volume s t := by
  have hU : ContDiffOn ℝ 1 γ.U (uIcc s t) := by
    simpa only [uIcc_of_le hst] using γ.c1_U
  have hA : ContinuousOn (fun x => S.A (γ.U x) (γ.V x)) (uIcc s t) := by
    rw [uIcc_of_le hst]
    exact h.solution.cont_A.comp (γ.c1_U.continuousOn.prodMk γ.c1_V.continuousOn) γ.mem
  exact hU.absolutelyContinuousOnInterval.intervalIntegrable_deriv.continuousOn_mul hA

/-- [internal] Restrict an existing clock cylinder to a closed subinterval.
The same coordinate maps and clock derivatives are retained. -/
@[expose] def restrictCylinder {S : Fields} {D : Set (ℝ × ℝ)} {b s t u v : ℝ}
    (γ : ClockCylinder S D b s t) (hsub : Icc u v ⊆ Icc s t) :
    ClockCylinder S D b u v where
  U := γ.U
  V := γ.V
  c1_U := γ.c1_U.mono hsub
  c1_V := γ.c1_V.mono hsub
  mem := fun x hx => γ.mem x (hsub hx)
  radius := fun x hx => γ.radius x (hsub hx)
  rate_U := fun x hx => (γ.rate_U x (hsub hx)).mono hsub
  rate_V := fun x hx => (γ.rate_V x (hsub hx)).mono hsub

/-- [internal] Changing the anchor of a parallel representative changes it
by one constant unit multiplier on the containing proper interval. -/
theorem curveParallel_reanchor {e : ℝ} {S : Fields} {f : ℝ → ℝ → ℂ}
    {U V : ℝ → ℝ} {s t u x : ℝ} (hst : s ≤ t)
    (hA : IntervalIntegrable (fun y => S.A (U y) (V y) * deriv U y) volume s t)
    (hu : u ∈ Icc s t) (hx : x ∈ Icc s t) :
    curveParallel e S f U V s x =
      Complex.exp (I * e * ∫ y in s..u, S.A (U y) (V y) * deriv U y) *
        curveParallel e S f U V u x := by
  have hu' : u ∈ uIcc s t := by rwa [uIcc_of_le hst]
  have hx' : x ∈ uIcc s t := by rwa [uIcc_of_le hst]
  have hsu := hA.mono_set (uIcc_subset_uIcc left_mem_uIcc hu')
  have hux := hA.mono_set (uIcc_subset_uIcc hu' hx')
  rw [curveParallel_def, curveParallel_def, ← mul_assoc, ← Complex.exp_add]
  congr 2
  rw [← intervalIntegral.integral_add_adjacent_intervals hsu hux]
  push_cast
  ring

/-- [internal] Covariant variation on a subinterval equals the variation
of the original parallel representative restricted to that subinterval. -/
theorem curveCovVar_eq_restricted_variation {e : ℝ} {S : Fields}
    {f : ℝ → ℝ → ℂ} {U V : ℝ → ℝ} {s t u v : ℝ} (hst : s ≤ t)
    (hA : IntervalIntegrable (fun y => S.A (U y) (V y) * deriv U y) volume s t)
    (hsub : Icc u v ⊆ Icc s t) (huv : u ≤ v) :
    curveCovVar e S f U V u v =
      eVariationOn (curveParallel e S f U V s) (Icc u v) := by
  have hu := hsub (left_mem_Icc.mpr huv)
  rw [curveCovVar_def]
  symm
  calc
    _ = eVariationOn (fun x =>
        Complex.exp (I * e * ∫ y in s..u, S.A (U y) (V y) * deriv U y) *
          curveParallel e S f U V u x) (Icc u v) := by
      apply eVariationOn.congr
      intro x hx
      exact curveParallel_reanchor hst hA hu (hsub hx)
    _ = _ := Calculus.eVariationOn_unit_mul _ (by
      simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]) _ _

/-- [internal] Covariant AC is inherited by a subinterval in its own
parallel frame. The connection is only assumed integrable locally. -/
theorem curveParallel_ac_subinterval {e : ℝ} {S : Fields}
    {f : ℝ → ℝ → ℂ} {U V : ℝ → ℝ} {s t u v : ℝ} (hst : s ≤ t)
    (hA : IntervalIntegrable (fun y => S.A (U y) (V y) * deriv U y) volume s t)
    (hac : AbsolutelyContinuousOnInterval (curveParallel e S f U V s) s t)
    (huv : u ≤ v) (hsub : Icc u v ⊆ Icc s t) :
    AbsolutelyContinuousOnInterval (curveParallel e S f U V u) u v := by
  have hsub' : uIcc u v ⊆ uIcc s t := by
    simpa only [uIcc_of_le huv, uIcc_of_le hst] using hsub
  let z := Complex.exp (I * e * ∫ y in s..u, S.A (U y) (V y) * deriv U y)
  have hz : z ≠ 0 := Complex.exp_ne_zero _
  apply ((hac.mono hsub').const_smul z⁻¹).congr
  intro x hx
  have hx' : x ∈ Icc u v := by rwa [uIcc_of_le huv] at hx
  simp only [smul_eq_mul]
  rw [curveParallel_reanchor hst hA (hsub (left_mem_Icc.mpr huv)) (hsub hx')]
  exact inv_mul_cancel_left₀ hz _

/-- [node prop:charged-cool#covariant-variation-measure]
On any subinterval, the variation measure has mass equal to its own
covariant variation. This is an exact identity with no constants. -/
theorem covariant_variation_measure_apply {e : ℝ} {S : Fields}
    {f : ℝ → ℝ → ℂ} {U V : ℝ → ℝ} {s t u v : ℝ} (hst : s ≤ t)
    (hA : IntervalIntegrable (fun y => S.A (U y) (V y) * deriv U y) volume s t)
    (hac : AbsolutelyContinuousOnInterval (curveParallel e S f U V s) s t)
    (huv : u ≤ v) (hsub : Icc u v ⊆ Icc s t) :
    covariantVariationMeasure e S f U V s t (Icc u v) = curveCovVar e S f U V u v := by
  have hsub' : uIcc u v ⊆ uIcc s t := by
    simpa only [uIcc_of_le huv, uIcc_of_le hst] using hsub
  have hi := hac.intervalIntegrable_deriv_finiteDimensional.norm.mono_set hsub'
  rw [covariantVariationMeasure, withDensity_apply _ measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr hsub]
  simp only [← ofReal_norm]
  rw [← lintegral_Ico_eq_Icc, ← ofReal_intervalIntegral_eq_lintegral huv hi
    (ae_of_all _ (fun _ => norm_nonneg _))]
  rw [curveCovVar_eq_restricted_variation hst hA hsub huv,
    (hac.mono hsub').eVariationOn_eq_integral_norm_deriv huv]

/-- [internal] The total mass is the covariant variation on the entire
clock interval; the measure vanishes outside that interval. -/
theorem covariant_variation_measure_univ {e : ℝ} {S : Fields}
    {f : ℝ → ℝ → ℂ} {U V : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hac : AbsolutelyContinuousOnInterval (curveParallel e S f U V s) s t) :
    covariantVariationMeasure e S f U V s t univ = curveCovVar e S f U V s t := by
  rw [covariantVariationMeasure, withDensity_apply _ MeasurableSet.univ,
    setLIntegral_univ]
  simp only [← ofReal_norm]
  rw [← lintegral_Ico_eq_Icc, ← ofReal_intervalIntegral_eq_lintegral hst
    hac.intervalIntegrable_deriv_finiteDimensional.norm
    (ae_of_all _ (fun _ => norm_nonneg _))]
  exact (hac.eVariationOn_eq_integral_norm_deriv hst).symm

/-- [internal] The covariant variation measure is finite by the AC speed
formula, established before any conversion of its mass to a real number. -/
theorem covariant_variation_measure_finite {e : ℝ} {S : Fields}
    {f : ℝ → ℝ → ℂ} {U V : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hac : AbsolutelyContinuousOnInterval (curveParallel e S f U V s) s t) :
    IsFiniteMeasure (covariantVariationMeasure e S f U V s t) := by
  constructor
  rw [covariantVariationMeasure, withDensity_apply _ MeasurableSet.univ,
    setLIntegral_univ]
  simp only [← ofReal_norm]
  rw [← lintegral_Ico_eq_Icc, ← ofReal_intervalIntegral_eq_lintegral hst
    hac.intervalIntegrable_deriv_finiteDimensional.norm
    (ae_of_all _ (fun _ => norm_nonneg _))]
  exact ENNReal.ofReal_lt_top

/-- [internal] A positive clock density restricted to its actual interval.
This is used for dissipation counting, separately from the variation density. -/
noncomputable def clockDensityMeasure (D : ℝ → ℝ) (s t : ℝ) : Measure ℝ :=
  (volume.restrict (Icc s t)).withDensity (fun x => ENNReal.ofReal (D x))

/-- [internal] The total mass of an integrable nonnegative clock density. -/
theorem clock_density_measure_univ {D : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hD : IntervalIntegrable D volume s t) (hn : ∀ x ∈ Icc s t, 0 ≤ D x) :
    clockDensityMeasure D s t univ = ENNReal.ofReal (∫ x in s..t, D x) := by
  rw [clockDensityMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← lintegral_Ico_eq_Icc, ← ofReal_intervalIntegral_eq_lintegral hst hD
      ((ae_restrict_mem measurableSet_Icc).mono (fun x hx => hn x hx))]

/-- [internal] Finiteness of a positive integrable clock-density measure. -/
theorem clock_density_measure_finite {D : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hD : IntervalIntegrable D volume s t) (hn : ∀ x ∈ Icc s t, 0 ≤ D x) :
    IsFiniteMeasure (clockDensityMeasure D s t) := by
  constructor
  rw [clock_density_measure_univ hst hD hn]
  exact ENNReal.ofReal_lt_top

/-- [internal] Clock-density mass on any ordered subinterval is its own
integral. The containing interval contributes no other mass. -/
theorem clock_density_measure_apply {D : ℝ → ℝ} {s t u v : ℝ} (hst : s ≤ t)
    (hD : IntervalIntegrable D volume s t) (hn : ∀ x ∈ Icc s t, 0 ≤ D x)
    (huv : u ≤ v) (hsub : Icc u v ⊆ Icc s t) :
    clockDensityMeasure D s t (Icc u v) = ENNReal.ofReal (∫ x in u..v, D x) := by
  have hsub' : uIcc u v ⊆ uIcc s t := by
    simpa only [uIcc_of_le huv, uIcc_of_le hst] using hsub
  rw [clockDensityMeasure, withDensity_apply _ measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr hsub,
    ← lintegral_Ico_eq_Icc, ← ofReal_intervalIntegral_eq_lintegral huv (hD.mono_set hsub')
      ((ae_restrict_mem measurableSet_Icc).mono (fun x hx => hn x (hsub hx)))]

end EmcsfAcExtension.Global.Cooling
