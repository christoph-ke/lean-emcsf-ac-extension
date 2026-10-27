/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Global.Cooling.VariationMeasure
import EmcsfAcExtension.Infra.Measure.WindowSquare

/-! # Counting full cooling windows

The landed two-point counting theorem is applied to the actual finite
covariant variation measure. The statements allow any proper containing
clock interval, so they also apply to unfinished stages and subintervals
(`charged_SF_new_version.tex:L2923–L2935`).
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global

/-- [internal] Linear window counting for the dissipation measure. Its
exact overlap factor is `2*h`, uniformly in the measure and center set. -/
theorem lintegral_window_measure_le (μ : Measure ℝ) [SFinite μ] (h : ℝ) (s : Set ℝ) :
    (∫⁻ t in s, μ (Icc (t - h) (t + h))) ≤ ENNReal.ofReal (2 * h) * μ univ := by
  let K : ℝ → ℝ → ℝ≥0∞ := fun t => (Icc (t - h) (t + h)).indicator (fun _ => 1)
  have hm : Measurable (Function.uncurry K) := by
    apply measurable_const.indicator
    exact (measurableSet_le (measurable_fst.sub_const h) measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_fst.add_const h))
  have hi (t : ℝ) : ∫⁻ x, K t x ∂μ = μ (Icc (t - h) (t + h)) := by
    rw [lintegral_indicator measurableSet_Icc, setLIntegral_const, one_mul]
  calc
    _ = ∫⁻ t in s, ∫⁻ x, K t x ∂μ := by simp_rw [hi]
    _ = ∫⁻ x, (∫⁻ t in s, K t x) ∂μ := lintegral_lintegral_swap hm.aemeasurable
    _ ≤ ∫⁻ _x : ℝ, ENNReal.ofReal (2 * h) ∂μ := by
      apply lintegral_mono
      intro x
      have heq : (fun t => K t x) = (Icc (x - h) (x + h)).indicator (fun _ => 1) := by
        funext t
        have he : x ∈ Icc (t - h) (t + h) ↔ t ∈ Icc (x - h) (x + h) := by
          constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
        simp only [K, Set.indicator_apply, he]
      change (∫⁻ t in s, K t x) ≤ ENNReal.ofReal (2 * h)
      rw [heq, lintegral_indicator measurableSet_Icc, setLIntegral_const, one_mul,
        Measure.restrict_apply measurableSet_Icc]
      calc
        _ ≤ volume (Icc (x - h) (x + h)) := measure_mono inter_subset_left
        _ = ENNReal.ofReal (2 * h) := by rw [Real.volume_Icc]; congr 1; ring
    _ = _ := lintegral_const _

/-- [internal] Linear window mass of a finite positive measure is
integrable over every set of centers. -/
theorem integrableOn_window_measure (μ : Measure ℝ) [IsFiniteMeasure μ]
    (h : ℝ) (s : Set ℝ) :
    IntegrableOn (fun t : ℝ => (μ (Icc (t - h) (t + h))).toReal) s := by
  apply integrable_toReal_of_lintegral_ne_top (measurable_window_measure μ h).aemeasurable
  exact ne_top_of_le_ne_top (by finiteness) (lintegral_window_measure_le μ h s)

/-- [internal] Real linear-window counting for a finite positive measure.
The coefficient `2*h` is independent of the duration and total mass. -/
theorem integral_window_measure_le (μ : Measure ℝ) [IsFiniteMeasure μ]
    {h : ℝ} (hh : 0 ≤ h) (s : Set ℝ) :
    (∫ t in s, (μ (Icc (t - h) (t + h))).toReal) ≤ 2 * h * (μ univ).toReal := by
  have hm := measurable_window_measure μ h
  have hfin : ENNReal.ofReal (2 * h) * μ univ ≠ ∞ := by finiteness
  have hb := ENNReal.toReal_mono hfin (lintegral_window_measure_le μ h s)
  have hi := integral_toReal (μ := volume.restrict s) hm.aemeasurable
    (Filter.Eventually.of_forall fun t => by finiteness :
      ∀ᵐ t ∂volume.restrict s, μ (Icc (t - h) (t + h)) < ∞)
  simpa only [← hi, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * h)] using hb

/-- [internal] Squared covariant window variation has the sharp overlap coefficient `2*h`.
There are no constants depending on the duration or scalar background.
The whole assertion remains valid when the center interval is empty. -/
theorem charged_cool_window_counting_of_connection {e : ℝ} {S : Fields}
    {f : ℝ → ℝ → ℂ} {U V : ℝ → ℝ} {s t h : ℝ} (hst : s ≤ t) (hh : 0 ≤ h)
    (hA : IntervalIntegrable (fun y => S.A (U y) (V y) * deriv U y) volume s t)
    (hac : AbsolutelyContinuousOnInterval (curveParallel e S f U V s) s t) :
    (∫⁻ x in Icc (s + h) (t - h), (curveCovVar e S f U V (x - h) (x + h)) ^ 2) ≤
      ENNReal.ofReal (2 * h) * (curveCovVar e S f U V s t) ^ 2 := by
  let ω := Cooling.covariantVariationMeasure e S f U V s t
  have : IsFiniteMeasure ω := Cooling.covariant_variation_measure_finite hst hac
  have heq : (fun x => (ω (Icc (x - h) (x + h))) ^ 2) =ᵐ[
      volume.restrict (Icc (s + h) (t - h))]
      (fun x => (curveCovVar e S f U V (x - h) (x + h)) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Cooling.covariant_variation_measure_apply hst hA hac (by linarith) (by
      intro y hy
      constructor <;> linarith only [hx.1, hx.2, hy.1, hy.2])]
  have hb := lintegral_window_sq_le ω h (Icc (s + h) (t - h))
  rw [lintegral_congr_ae heq, Cooling.covariant_variation_measure_univ hst hac] at hb
  exact hb

/-- [node eq:charged-cool-window-counting]
Squared covariant variation on actual cylinder windows has overlap factor
exactly `2*Tstar*b`, independently of duration, energy, coupling, and scalar
background. The pulled-back connection hypothesis of the general counting
helper is discharged from the existing cylinder geometry. -/
theorem charged_cool_window_counting (ui e b s t Tstar : ℝ) (S : Fields)
    (h : OriginalData ui e S) (hb : 0 < b) (hst : s ≤ t) (hTs : 0 ≤ Tstar)
    (γ : ClockCylinder S (origDomain ui) b s t)
    (hac : AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V s) s t) :
    (∫⁻ x in Icc (s + Tstar * b) (t - Tstar * b),
      (curveCovVar e S S.a γ.U γ.V (x - Tstar * b) (x + Tstar * b)) ^ 2) ≤
      ENNReal.ofReal (2 * (Tstar * b)) * (curveCovVar e S S.a γ.U γ.V s t) ^ 2 :=
  charged_cool_window_counting_of_connection hst (mul_nonneg hTs hb.le)
    (Cooling.connection_intervalIntegrable h hst γ) hac

end EmcsfAcExtension.Global
