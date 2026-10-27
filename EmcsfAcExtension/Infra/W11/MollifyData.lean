module

public import EmcsfAcExtension.Frozen.DatumVar
import EmcsfAcExtension.Infra.W11.MollifyConvolution
import EmcsfAcExtension.Infra.W11.Distance

/-!
# Variation-nonincreasing smooth approximation of AC data

Extend the AC derivative by zero, convolve with normalized smooth bumps, and
integrate from the prescribed vertex. The AC–TV identity turns the global L¹
contraction into exact variation preservation on the interval. Strong L¹
convergence of the densities gives convergence in the representative W¹¹
distance. All estimates have coefficient one, uniformly in the datum and length.
This is the construction in internal project record at `charged_SF_new_version.tex:L6350–L6371`.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace EmcsfAcExtension.W11

/-- Global C∞ approximants preserve the vertex and never increase interval
variation, while their variation error tends to zero. Every estimate is uniform
in `T` and `h`, with coefficient one. -/
theorem exists_smooth_variation_nonincreasing_approximation {T : ℝ} {h : ℝ → ℂ}
    (hT : 0 < T) (hac : AbsolutelyContinuousOnInterval h 0 T) :
    ∃ hn : ℕ → ℝ → ℂ, (∀ n, ContDiff ℝ ∞ (hn n)) ∧
      (∀ n, hn n 0 = h 0) ∧ (∀ n, datumVar (hn n) T ≤ datumVar h T) ∧
      Tendsto (fun n => datumVar (hn n - h) T) atTop (𝓝 0) := by
  have hd := hac.intervalIntegrable_deriv_complex
  let f : ℝ → ℂ := (Ioc 0 T).indicator (deriv h)
  have hfi : Integrable f :=
    (integrable_indicator_iff measurableSet_Ioc).2
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).1 hd)
  have hfnorm : (∫ x, ‖f x‖) = datumVar h T := by
    have heq : (fun x => ‖f x‖) = (Ioc 0 T).indicator (fun x => ‖deriv h x‖) := by
      ext x
      by_cases hx : x ∈ Ioc 0 T <;> simp [f, hx]
    rw [heq, integral_indicator measurableSet_Ioc]
    exact (intervalIntegral.integral_of_le hT.le).symm.trans
      (hac.toReal_eVariationOn_eq_integral_norm_deriv hT.le).symm
  obtain ⟨F, hFs, hFi, hFb, hFt⟩ := exists_smooth_convolution_approximation hfi
  let hn : ℕ → ℝ → ℂ := fun n x => h 0 + ∫ t in 0..x, F n t
  have hv n : hn n 0 = h 0 := by simp [hn]
  have hD n x : HasDerivAt (hn n) (F n x) x :=
    (intervalIntegral.integral_hasDerivAt_right ((hFs n).continuous.intervalIntegrable 0 x)
      ((hFs n).continuous.stronglyMeasurableAtFilter volume (𝓝 x))
      (hFs n).continuous.continuousAt).const_add (h 0)
  have hs n : ContDiff ℝ ∞ (hn n) := by
    apply contDiff_infty_iff_deriv.2
    refine ⟨fun x => (hD n x).differentiableAt, ?_⟩
    convert hFs n using 1
    ext x
    exact (hD n x).deriv
  have hvar n : datumVar (hn n) T = ∫ x in 0..T, ‖F n x‖ := by
    unfold datumVar
    rw [((hFs n).continuous.intervalIntegrable 0 T
      ).eVariationOn_const_add_intervalIntegral hT.le (h 0),
      ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg hT.le
        (fun _ _ => norm_nonneg _))]
  have herror n : datumVar (hn n - h) T = ∫ x in 0..T, ‖F n x - deriv h x‖ := by
    have heq : eVariationOn (hn n - h) (Icc 0 T) =
        ENNReal.ofReal (∫ x in 0..T, ‖F n x - deriv h x‖) := by
      apply (((hFs n).continuous.intervalIntegrable 0 T).sub hd
        ).eVariationOn_eq_integral_norm_of_eq_integral hT.le
      intro x hx
      have hsub : uIcc 0 x ⊆ uIcc 0 T := by
        rw [uIcc_of_le hx.1, uIcc_of_le hT.le]
        exact Icc_subset_Icc le_rfl hx.2
      rw [Pi.sub_apply, Pi.sub_apply, hv, sub_self, zero_add,
        intervalIntegral.integral_sub ((hFs n).continuous.intervalIntegrable 0 x)
          (hd.mono_set hsub), (hac.mono hsub).integral_deriv_eq_sub_complex]
      dsimp only [hn]
      abel
    unfold datumVar
    rw [heq, ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg hT.le
      (fun _ _ => norm_nonneg _))]
  have herr n : datumVar (hn n - h) T ≤ ∫ x, ‖F n x - f x‖ := by
    rw [herror, intervalIntegral.integral_of_le hT.le]
    calc
      _ = ∫ x in Ioc 0 T, ‖F n x - f x‖ := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x hx
        simp [f, hx]
      _ ≤ _ := setIntegral_le_integral ((hFi n).sub hfi).norm
        (ae_of_all _ (fun x => norm_nonneg _))
  refine ⟨hn, hs, hv, ?_, squeeze_zero (fun _ => ENNReal.toReal_nonneg) herr hFt⟩
  intro n
  rw [hvar]
  calc
    _ ≤ ∫ x, ‖F n x‖ := by
      rw [intervalIntegral.integral_of_le hT.le]
      exact setIntegral_le_integral (hFi n).norm
        (ae_of_all _ (fun x => norm_nonneg _))
    _ ≤ _ := (hFb n).trans_eq hfnorm

end EmcsfAcExtension.W11
