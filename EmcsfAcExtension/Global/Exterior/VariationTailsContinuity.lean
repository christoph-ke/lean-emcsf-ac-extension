module

public import EmcsfAcExtension.Infra.Density.Representative
import EmcsfAcExtension.Infra.AC.Variation

/-! # Continuity of moving outgoing density integrals

This is the dominated-convergence step in approved internal project record, support-moving-interval,
`charged_SF_new_version.tex:L1413–L1416`. The initial label density is only integrable.
The majorant constant depends on the two continuous factors and the proper
rectangle, uniformly in the incoming row and the initial density.
-/

public section

open Set MeasureTheory Filter Topology

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
The norm integral of a prescribed density is continuous when its lower
label moves continuously. No continuity of the initial density is required.
The two factors may be any continuous extensions from the swept region;
the conclusion only uses their values above the moving boundary. -/
theorem continuousOn_moving_fixedDensity_norm
    {P R : ℝ → ℝ → ℂ} {w₀ : ℝ → ℂ} {t : ℝ → ℝ} {a b c : ℝ}
    (hc : c ≤ 0) (ht : ContinuousOn t (Icc a b))
    (htmem : ∀ u ∈ Icc a b, t u ∈ Icc c 0)
    (hP : ContinuousOn P.uncurry (Icc a b ×ˢ Icc c 0))
    (hR : ContinuousOn R.uncurry (Icc a b ×ˢ Icc c 0))
    (hw₀ : IntervalIntegrable w₀ volume c 0) :
    ContinuousOn (fun u => ∫ v in t u..0, ‖Density.fixedDensity P R w₀ u v‖)
      (Icc a b) := by
  classical
  obtain ⟨C, hC, hbound⟩ := Density.exists_fixedDensity_bound hP hR
  let F : ℝ → ℝ → ℝ := fun u => (Icc (t u) 0).indicator
    (fun v => ‖Density.fixedDensity P R w₀ u v‖)
  have hFn (u : ℝ) (hu : u ∈ Icc a b) :
      IntegrableOn (F u) (Icc c 0) :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hc).1
      (Density.intervalIntegrable_fixedDensity hc hu hP hR hw₀).norm).indicator
        measurableSet_Icc
  have hFeq (u : ℝ) (hu : u ∈ Icc a b) :
      (∫ v in Icc c 0, F u v) = ∫ v in t u..0, ‖Density.fixedDensity P R w₀ u v‖ := by
    rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
      inter_eq_left.mpr (Icc_subset_Icc (htmem u hu).1 le_rfl)]
    rw [intervalIntegral.integral_of_le (htmem u hu).2, integral_Icc_eq_integral_Ioc]
  have hcont : ContinuousOn (fun u => ∫ v in Icc c 0, F u v) (Icc a b) := by
    intro u hu
    apply MeasureTheory.continuousWithinAt_of_dominated
      (bound := fun v => C * (‖w₀ v‖ + 1))
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact (hFn x hx).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with x hx
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
      dsimp only [F]
      by_cases hvt : v ∈ Icc (t x) 0
      · rw [indicator_of_mem hvt, Real.norm_of_nonneg (norm_nonneg _)]
        exact hbound w₀ x hx v hv
      · rw [indicator_of_notMem hvt, norm_zero]
        positivity
    · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hc).1
        ((hw₀.norm.add intervalIntegrable_const).const_mul C)
    · have hne : ∀ᵐ v ∂volume.restrict (Icc c 0), v ≠ t u :=
        ae_restrict_of_ae (by simp [ae_iff])
      filter_upwards [ae_restrict_mem measurableSet_Icc, hne] with v hv hnv
      have hPv := hP.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun x hx => ⟨hx, hv⟩)
      have hRv := hR.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun x hx => ⟨hx, hv⟩)
      have hnorm : ContinuousWithinAt
          (fun x => ‖Density.fixedDensity P R w₀ x v‖) (Icc a b) u :=
        (((hPv u hu).mul_const (w₀ v)).add (hRv u hu)).norm
      rcases lt_or_gt_of_ne hnv with hlt | hgt
      · have hev : ∀ᶠ x in 𝓝[Icc a b] u, v < t x :=
          (ht u hu).eventually (Ioi_mem_nhds hlt)
        apply (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq_of_mem (hx := hu)
        filter_upwards [hev] with x hx
        exact (indicator_of_notMem (show v ∉ Icc (t x) 0 from
          fun h => (not_le_of_gt hx) h.1) _)
      · have hev : ∀ᶠ x in 𝓝[Icc a b] u, t x < v :=
          (ht u hu).eventually (Iio_mem_nhds hgt)
        apply hnorm.congr_of_eventuallyEq_of_mem (hx := hu)
        filter_upwards [hev] with x hx
        exact indicator_of_mem (show v ∈ Icc (t x) 0 from ⟨hx.le, hv.2⟩) _
  exact hcont.congr (fun u hu => (hFeq u hu).symm)

end EmcsfAcExtension.Global.Exterior
