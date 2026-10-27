module

public import EmcsfAcExtension.Local.Defs.Partial
public import EmcsfAcExtension.Infra.Triangle
import EmcsfAcExtension.Infra.Calculus.PartialsC1
import EmcsfAcExtension.Local.Calculus.Normalized

/-! # Real classical sections as exact partial-density primitives

The within-triangle partials are continuous and integrable through the
axis, and FTC identifies their ordinary one-dimensional primitives.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

/-- Each outgoing real C¹ section is the primitive of its outgoing
partial, including both endpoints. No estimate constant is introduced.
-/
theorem stab_out_real_partial_primitive_c1 {T : ℝ} (hT : 0 < T)
    {f : ℝ → ℝ → ℝ} (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle 0 T))
    {u : ℝ} (hu : u ∈ Icc 0 T) :
    Integrable (fun s => pdV (triangle 0 T) f u s) (volume.restrict (Icc u T)) ∧
      ∀ v ∈ Icc u T, f u v = f u u + ∫ s in u..v, pdV (triangle 0 T) f u s := by
  have hmap : MapsTo (fun s : ℝ => (u, s)) (Icc u T) (triangle 0 T) :=
    fun s hs => ⟨hu.1, hs.1, hs.2⟩
  have cf := hf.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn hmap
  have cp := (continuousOn_partial_v hf (uniqueDiffOn_triangle hT)).comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have hi := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hu.2 cp
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le hu.2).1 hi, ?_⟩
  intro v hv
  have hsub : Icc u v ⊆ Icc u T := Icc_subset_Icc_right hv.2
  have hp := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hv.1 (cf.mono hsub)
    (fun s hs => (hasDerivWithinAt_v_aux hf hu.1 hs.1.le (hs.2.le.trans hv.2)).hasDerivAt
      (Icc_mem_nhds hs.1 (hs.2.trans_le hv.2)))
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hv.1 (cp.mono hsub))
  change (∫ s in u..v, pdV (triangle 0 T) f u s) = f u v - f u u at hp
  rw [hp]
  ring

/-- Each incoming real C¹ section is the primitive of its incoming
partial from the initial cone. The assertion holds on all closed
sections, with no null set of labels and no estimate constant.
-/
theorem stab_in_real_partial_primitive_c1 {T : ℝ} (hT : 0 < T)
    {f : ℝ → ℝ → ℝ} (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle 0 T))
    {v : ℝ} (hv : v ∈ Icc 0 T) :
    Integrable (fun s => pdU (triangle 0 T) f s v) (volume.restrict (Icc 0 v)) ∧
      ∀ u ∈ Icc 0 v, f u v = f 0 v + ∫ s in 0..u, pdU (triangle 0 T) f s v := by
  have hmap : MapsTo (fun s : ℝ => (s, v)) (Icc 0 v) (triangle 0 T) :=
    fun s hs => ⟨hs.1, hs.2, hv.2⟩
  have cf := hf.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn hmap
  have cp := (continuousOn_partial_u hf (uniqueDiffOn_triangle hT)).comp
    (continuous_id.prodMk continuous_const).continuousOn hmap
  have hi := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hv.1 cp
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le hv.1).1 hi, ?_⟩
  intro u hu
  have hsub : Icc 0 u ⊆ Icc 0 v := Icc_subset_Icc_right hu.2
  have hp := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu.1 (cf.mono hsub)
    (fun s hs => (hasDerivWithinAt_u_aux hf hs.1.le (hs.2.le.trans hu.2) hv.2).hasDerivAt
      (Icc_mem_nhds hs.1 (hs.2.trans_le hu.2)))
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hu.1 (cp.mono hsub))
  change (∫ s in 0..u, pdU (triangle 0 T) f s v) = f u v - f 0 v at hp
  rw [hp]
  ring

end EmcsfAcExtension.Local
