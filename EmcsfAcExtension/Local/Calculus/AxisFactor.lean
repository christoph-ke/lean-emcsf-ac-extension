module

public import EmcsfAcExtension.Local.Defs.Partial
public import EmcsfAcExtension.Frozen.Triangle
import EmcsfAcExtension.Infra.Calculus.PartialsC1

/-! # Continuous first-order factors at the regular axis

The section integral of the continuous domain partial factors a C¹ field's
increment by `v-u`. This supplies a local quotient extension for axis limits,
without relying on the separately owned internal project record files.
-/

public section

open Set MeasureTheory Filter
open scoped Topology

namespace EmcsfAcExtension.Local

private theorem continuousOn_integral_compact_aux {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set (ℝ × ℝ)} {F : (ℝ × ℝ) → ℝ → E}
    (hK : IsCompact K)
    (hF : ContinuousOn (Function.uncurry F) (K ×ˢ Icc (0 : ℝ) 1)) :
    ContinuousOn (fun p => ∫ t in (0 : ℝ)..1, F p t) K := by
  obtain ⟨C, hC⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn hF
  have hsec (p : ℝ × ℝ) (hp : p ∈ K) : ContinuousOn (F p) (Icc (0 : ℝ) 1) :=
    hF.comp (continuousOn_const.prodMk continuousOn_id) (fun _ ht => ⟨hp, ht⟩)
  intro p hp
  apply intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun _ => C)
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact ((hsec q hq).aestronglyMeasurable measurableSet_Icc).mono_set
      (by simp only [uIoc_of_le zero_le_one]; exact Ioc_subset_Icc_self)
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact Filter.Eventually.of_forall (fun t ht => hC (q, t)
      ⟨hq, by simpa only [uIcc_of_le zero_le_one] using uIoc_subset_uIcc ht⟩)
  · exact intervalIntegrable_const
  · apply Filter.Eventually.of_forall
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le zero_le_one] using (uIoc_subset_uIcc ht)
    exact (hF.comp (continuousOn_id.prodMk continuousOn_const)
      (fun _ hq => ⟨hq, ht'⟩)) p hp

/-- A C¹ field has a continuous outgoing divided increment on a nondegenerate
triangle. Its diagonal value is the canonical outgoing partial. This local helper
provides the axis quotient needed independently of internal project record's axis-limit API. -/
theorem exists_continuous_axis_factor_aux {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {T : ℝ} {f : ℝ → ℝ → E} (hT : 0 < T)
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle 0 T)) :
    ∃ g : (ℝ × ℝ) → E, ContinuousOn g (triangle 0 T) ∧
      (∀ u v, (u, v) ∈ triangle 0 T → f u v - f u u = (v - u) • g (u, v)) ∧
      (∀ t ∈ Icc 0 T, g (t, t) = pdV (triangle 0 T) f t t) := by
  let F (p : ℝ × ℝ) (t : ℝ) :=
    pdV (triangle 0 T) f p.1 (p.1 + (p.2 - p.1) * t)
  have hmap : ∀ q ∈ triangle 0 T ×ˢ Icc (0 : ℝ) 1,
      (q.1.1, q.1.1 + (q.1.2 - q.1.1) * q.2) ∈ triangle 0 T := by
    intro q hq
    refine ⟨hq.1.1, ?_, ?_⟩
    · exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hq.1.2.1) hq.2.1)
    · calc
        q.1.1 + (q.1.2 - q.1.1) * q.2 ≤ q.1.1 + (q.1.2 - q.1.1) * 1 :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hq.2.2
            (sub_nonneg.mpr hq.1.2.1))
        _ = q.1.2 := by ring
        _ ≤ T := hq.1.2.2
  have hF : ContinuousOn (Function.uncurry F) (triangle 0 T ×ˢ Icc (0 : ℝ) 1) :=
    (continuousOn_partial_v hf (uniqueDiffOn_triangle hT)).comp
      (show ContinuousOn
        (fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.1.1 + (q.1.2 - q.1.1) * q.2))
        (triangle 0 T ×ˢ Icc (0 : ℝ) 1) from (by fun_prop : Continuous _).continuousOn)
      hmap
  refine ⟨fun p => ∫ t in (0 : ℝ)..1, F p t,
    continuousOn_integral_compact_aux (isCompact_triangle 0 T) hF, ?_, ?_⟩
  · intro u v hp
    have hc := (continuousOn_partial_v hf (uniqueDiffOn_triangle hT)).comp
      (continuousOn_const.prodMk continuousOn_id)
      (s := Icc u v) (fun _ hs => ⟨hp.1, hs.1, hs.2.trans hp.2.2⟩)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hp.2.1
      (hf.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
        (fun _ hs => ⟨hp.1, hs.1, hs.2.trans hp.2.2⟩))
      (f' := fun s => pdV (triangle 0 T) f u s)
      (fun s hs => (hasDerivWithinAt_uncurry_triangle_v (u := u) (v := s) hf
        ⟨hp.1, hs.1.le, hs.2.le.trans hp.2.2⟩).hasDerivAt
          (Icc_mem_nhds hs.1 (hs.2.trans_le hp.2.2)))
      (hc.intervalIntegrable_of_Icc hp.2.1)
    change (∫ s in u..v, pdV (triangle 0 T) f u s) = f u v - f u u at hftc
    rw [← hftc]
    simp [F]
  · intro t ht
    simp [F]

end EmcsfAcExtension.Local
