/- Copyright (c) 2026. All rights reserved. -/

module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Two-point counting for moving windows

Generic support for `eq:charged-cool-window-counting`
(`charged_SF_new_version.tex:L2923`–L2935), consumed by `Global/Cooling/Windows` after
the actual covariant variation measure is constructed. No source node is
closed here. The measures may have atoms. The exact two-point overlap is
`ofReal (2 * h - |x - y|)`, and its uniform bound is exactly `ofReal (2 * h)`.
There are no hidden constants, radius, duration, or field assumptions.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global

/-- [internal] The centers whose closed windows contain two prescribed points.
No constants are chosen. Consumed by `eq:charged-cool-window-counting`. -/
theorem two_point_window_centers (h x y : ℝ) :
    {t : ℝ | x ∈ Icc (t - h) (t + h) ∧ y ∈ Icc (t - h) (t + h)} =
      Icc (max x y - h) (min x y + h) := by
  ext t
  change ((t - h ≤ x ∧ x ≤ t + h) ∧ (t - h ≤ y ∧ y ≤ t + h)) ↔
    (max x y - h ≤ t ∧ t ≤ min x y + h)
  constructor
  · rintro ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
    have hm := max_le hx2 hy2
    have hn := le_min hx1 hy1
    constructor <;> linarith only [hm, hn]
  · rintro ⟨hm, hn⟩
    have hxm := le_max_left x y
    have hym := le_max_right x y
    have hxn := min_le_left x y
    have hyn := min_le_right x y
    constructor <;> constructor <;> linarith only [hm, hn, hxm, hym, hxn, hyn]

/-- [internal] Exact Lebesgue length of the two-point center overlap, including
the empty-overlap case. Its only parameter is the half-width `h`.
Consumed by `eq:charged-cool-window-counting`. -/
theorem volume_two_point_window_centers (h x y : ℝ) :
    volume {t : ℝ | x ∈ Icc (t - h) (t + h) ∧ y ∈ Icc (t - h) (t + h)} =
      ENNReal.ofReal (2 * h - |x - y|) := by
  rw [two_point_window_centers, Real.volume_Icc]
  congr 1
  rcases le_total x y with hxy | hyx
  · rw [max_eq_right hxy, min_eq_left hxy, abs_of_nonpos (sub_nonpos.mpr hxy)]
    ring
  · rw [max_eq_left hyx, min_eq_right hyx, abs_of_nonneg (sub_nonneg.mpr hyx)]
    ring

/-- [internal] Uniform overlap bound with the exact factor `2 * h`.
Uniform in both points and in every set of allowed centers. Consumed by
`eq:charged-cool-window-counting`. -/
theorem volume_two_point_window_centers_le (h x y : ℝ) (s : Set ℝ) :
    volume (s ∩ {t : ℝ | x ∈ Icc (t - h) (t + h) ∧
      y ∈ Icc (t - h) (t + h)}) ≤ ENNReal.ofReal (2 * h) := by
  calc
    _ ≤ volume {t : ℝ | x ∈ Icc (t - h) (t + h) ∧
        y ∈ Icc (t - h) (t + h)} := measure_mono inter_subset_right
    _ = _ := volume_two_point_window_centers h x y
    _ ≤ _ := ENNReal.ofReal_le_ofReal (sub_le_self _ (abs_nonneg _))

/-- [internal] Window mass is measurable for any s-finite positive measure;
in particular no absence of atoms is required. Consumed by
`eq:charged-cool-window-counting`. -/
theorem measurable_window_measure (μ : Measure ℝ) [SFinite μ] (h : ℝ) :
    Measurable (fun t : ℝ => μ (Icc (t - h) (t + h))) := by
  have hm : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Icc (p.1 - h) (p.1 + h)} := by
    exact (measurableSet_le (measurable_fst.sub_const h) measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_fst.add_const h))
  exact measurable_measure_prodMk_left hm

/-- [internal] Exact Tonelli formula for the product of two moving window
masses. The overlap is measured only in the chosen center set `s`.
All measures and the half-width are arbitrary; there are no implicit constants.
Consumed by `eq:charged-cool-window-counting`. -/
theorem lintegral_window_mul_eq (μ ν : Measure ℝ) [SFinite μ] [SFinite ν]
    (h : ℝ) (s : Set ℝ) :
    (∫⁻ t in s, μ (Icc (t - h) (t + h)) * ν (Icc (t - h) (t + h))) =
      ∫⁻ p, volume (s ∩ Icc (max p.1 p.2 - h) (min p.1 p.2 + h)) ∂μ.prod ν := by
  let K : ℝ → ℝ × ℝ → ℝ≥0∞ := fun t =>
    (Icc (t - h) (t + h) ×ˢ Icc (t - h) (t + h)).indicator (fun _ => 1)
  have hKm : Measurable (Function.uncurry K) := by
    apply measurable_const.indicator
    exact ((measurableSet_le (measurable_fst.sub_const h)
      (measurable_fst.comp measurable_snd)).inter
      (measurableSet_le (measurable_fst.comp measurable_snd) (measurable_fst.add_const h))).inter
      ((measurableSet_le (measurable_fst.sub_const h)
        (measurable_snd.comp measurable_snd)).inter
        (measurableSet_le (measurable_snd.comp measurable_snd) (measurable_fst.add_const h)))
  have hKint (t : ℝ) : ∫⁻ p, K t p ∂μ.prod ν =
      μ (Icc (t - h) (t + h)) * ν (Icc (t - h) (t + h)) := by
    rw [lintegral_indicator (measurableSet_Icc.prod measurableSet_Icc), setLIntegral_const]
    simp only [one_mul, Measure.prod_prod]
  calc
    _ = ∫⁻ t in s, ∫⁻ p, K t p ∂μ.prod ν := by simp_rw [hKint]
    _ = ∫⁻ p, (∫⁻ t in s, K t p) ∂μ.prod ν := lintegral_lintegral_swap hKm.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro p
      have hfun : (fun t => K t p) =
          (Icc (max p.1 p.2 - h) (min p.1 p.2 + h)).indicator (fun _ => 1) := by
        ext t
        simp only [K, Set.indicator_apply, mem_prod, ← two_point_window_centers,
          mem_ofPred_eq]
      rw [hfun, lintegral_indicator measurableSet_Icc, setLIntegral_const, one_mul,
        Measure.restrict_apply measurableSet_Icc, inter_comm]

/-- [internal] Positive-measure window counting for two possibly different
s-finite measures, with the exact factor `2 * h`. Uniform in the center set,
duration, measures, and total masses. Consumed by
`eq:charged-cool-window-counting`. -/
theorem lintegral_window_mul_le (μ ν : Measure ℝ) [SFinite μ] [SFinite ν]
    (h : ℝ) (s : Set ℝ) :
    (∫⁻ t in s, μ (Icc (t - h) (t + h)) * ν (Icc (t - h) (t + h))) ≤
      ENNReal.ofReal (2 * h) * (μ univ * ν univ) := by
  rw [lintegral_window_mul_eq μ ν h s]
  calc
    _ ≤ ∫⁻ _ : ℝ × ℝ, ENNReal.ofReal (2 * h) ∂μ.prod ν := by
      apply lintegral_mono
      intro p
      dsimp only
      rw [← two_point_window_centers]
      exact volume_two_point_window_centers_le h p.1 p.2 s
    _ = _ := by rw [lintegral_const, ← Set.univ_prod_univ, Measure.prod_prod]

/-- [internal] Squared window counting for a positive s-finite measure, with
the exact overlap constant `2 * h`. No constant depends on the measure or
center set. Consumed by `eq:charged-cool-window-counting`. -/
theorem lintegral_window_sq_le (μ : Measure ℝ) [SFinite μ]
    (h : ℝ) (s : Set ℝ) :
    (∫⁻ t in s, μ (Icc (t - h) (t + h)) ^ 2) ≤
      ENNReal.ofReal (2 * h) * (μ univ) ^ 2 := by
  simpa only [pow_two] using lintegral_window_mul_le μ μ h s

/-- [internal] Squared window mass for a finite positive measure is integrable
on every center set, including the whole real line. No bound on the
duration and no atomlessness is needed. Consumed by
`eq:charged-cool-window-counting` when passing to real integrals. -/
theorem integrableOn_window_sq (μ : Measure ℝ) [IsFiniteMeasure μ]
    (h : ℝ) (s : Set ℝ) :
    IntegrableOn (fun t : ℝ => (μ (Icc (t - h) (t + h))).toReal ^ 2) s := by
  have hm := (measurable_window_measure μ h).pow_const 2
  have hfin : ENNReal.ofReal (2 * h) * (μ univ) ^ 2 < ∞ := by finiteness
  have hi := integrable_toReal_of_lintegral_ne_top hm.aemeasurable
    (ne_of_lt ((lintegral_window_sq_le μ h s).trans_lt hfin))
  simpa only [IntegrableOn, ENNReal.toReal_pow] using hi

/-- [internal] Real integral version of squared window counting, with precisely
the coefficient `2 * h`, uniformly in the finite measure and center set.
Consumed by `eq:charged-cool-window-counting`. -/
theorem integral_window_sq_le (μ : Measure ℝ) [IsFiniteMeasure μ]
    {h : ℝ} (hh : 0 ≤ h) (s : Set ℝ) :
    (∫ t in s, (μ (Icc (t - h) (t + h))).toReal ^ 2) ≤
      2 * h * (μ univ).toReal ^ 2 := by
  have hm := (measurable_window_measure μ h).pow_const 2
  have hfin : ENNReal.ofReal (2 * h) * (μ univ) ^ 2 ≠ ∞ := by finiteness
  have hle := ENNReal.toReal_mono hfin (lintegral_window_sq_le μ h s)
  have hi := integral_toReal (μ := volume.restrict s) hm.aemeasurable
    (Filter.Eventually.of_forall fun t => by finiteness :
      ∀ᵐ t ∂volume.restrict s, μ (Icc (t - h) (t + h)) ^ 2 < ∞)
  have hh2 : 0 ≤ 2 * h := mul_nonneg (by norm_num) hh
  simpa only [← hi, ENNReal.toReal_pow, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hh2] using hle

end EmcsfAcExtension.Global
