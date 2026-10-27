/- Copyright (c) 2026. All rights reserved. -/

module

public import EmcsfAcExtension.Infra.PowerKernel
public import EmcsfAcExtension.Infra.Triangle
import Mathlib.Tactic

/-!
# The ordered power-kernel operator

Nonnegative Tonelli estimates for the ordered region at
`charged_SF_new_version.tex:L5060–L5060` and `L5050–L5068`. The cutoff is a measurable set
of pairs `(a,w)`. Extended-real statements allow infinite masses and therefore
establish integrability rather than assume it. The interval is truncated in
both input variables. Constants are exactly `1/p` and `1/d`.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension

/-- The ordered-kernel density with a cutoff in the pair `(a,w)`.
Both inputs are restricted to `[0,T]`; the ordering is the internal project record triangle. -/
@[expose] noncomputable def orderedKernelDensity (p T : ℝ) (K J : ℝ → ℝ≥0∞)
    (s : Set (ℝ × ℝ)) (v : ℝ) : ℝ≥0∞ :=
  ∫⁻ a in Icc 0 T, ∫⁻ w in Icc 0 T,
    (triangle 0 v ∩ s).indicator
      (fun q => K q.1 * J q.2 * ENNReal.ofReal (orderedPowerKernel p q.1 q.2 v)) (a, w)

private theorem aemeasurable_kernel_triple {p T : ℝ} {K J : ℝ → ℝ≥0∞}
    {ν : Measure ℝ} [SFinite ν]
    (hK : AEMeasurable K (volume.restrict (Icc 0 T)))
    (hJ : AEMeasurable J (volume.restrict (Icc 0 T)))
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) :
    AEMeasurable (fun q : (ℝ × ℝ) × ℝ =>
      (triangle 0 q.1.1 ∩ s).indicator
        (fun z => K z.1 * J z.2 * ENNReal.ofReal
          (orderedPowerKernel p z.1 z.2 q.1.1)) (q.1.2, q.2))
      ((ν.prod (volume.restrict (Icc 0 T))).prod (volume.restrict (Icc 0 T))) := by
  classical
  let μ := volume.restrict (Icc 0 T)
  have hm : MeasurableSet {q : (ℝ × ℝ) × ℝ |
      (q.1.2, q.2) ∈ triangle 0 q.1.1 ∩ s} := by
    exact ((measurableSet_le measurable_const measurable_fst.snd).inter
      ((measurableSet_le measurable_fst.snd measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst.fst))).inter
      (hs.preimage (measurable_fst.snd.prodMk measurable_snd))
  have hF : AEMeasurable (fun q : (ℝ × ℝ) × ℝ =>
      (triangle 0 q.1.1 ∩ s).indicator
        (fun z => K z.1 * J z.2 * ENNReal.ofReal
          (orderedPowerKernel p z.1 z.2 q.1.1)) (q.1.2, q.2))
      ((ν.prod μ).prod μ) := by
    change AEMeasurable ({q : (ℝ × ℝ) × ℝ |
      (q.1.2, q.2) ∈ triangle 0 q.1.1 ∩ s}.indicator
      (fun q => K q.1.2 * J q.2 * ENNReal.ofReal
        (orderedPowerKernel p q.1.2 q.2 q.1.1))) _
    exact (((hK.comp_snd).comp_fst.mul hJ.comp_snd).mul
      (by unfold orderedPowerKernel; fun_prop)).indicator hm
  exact hF

private theorem lintegral_orderedKernelDensity_swap {p T : ℝ} {K J : ℝ → ℝ≥0∞}
    (hK : AEMeasurable K (volume.restrict (Icc 0 T)))
    (hJ : AEMeasurable J (volume.restrict (Icc 0 T)))
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) :
    (∫⁻ v in Icc 0 T, orderedKernelDensity p T K J s v) =
      ∫⁻ a in Icc 0 T, ∫⁻ w in Icc 0 T, ∫⁻ v in Icc 0 T,
        (triangle 0 v ∩ s).indicator
          (fun q => K q.1 * J q.2 * ENNReal.ofReal
            (orderedPowerKernel p q.1 q.2 v)) (a, w) := by
  classical
  let μ := volume.restrict (Icc 0 T)
  have hF := aemeasurable_kernel_triple (p := p) (ν := μ) hK hJ hs
  unfold orderedKernelDensity
  rw [lintegral_lintegral_swap hF.lintegral_prod_right']
  apply lintegral_congr
  intro a
  apply lintegral_lintegral_swap
  have hm' : MeasurableSet {q : ℝ × ℝ | (a, q.2) ∈ triangle 0 q.1 ∩ s} := by
    exact ((measurableSet_le (f := fun _ : ℝ × ℝ => (0 : ℝ))
      (g := fun _ => a) measurable_const measurable_const).inter
      ((measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst))).inter
      (hs.preimage (measurable_const.prodMk measurable_snd))
  change AEMeasurable ({q : ℝ × ℝ | (a, q.2) ∈ triangle 0 q.1 ∩ s}.indicator
    (fun q => K a * J q.2 * ENNReal.ofReal (orderedPowerKernel p a q.2 q.1))) _
  exact ((aemeasurable_const.mul hJ.comp_snd).mul
    (by unfold orderedPowerKernel; fun_prop)).indicator hm'

private theorem lintegral_kernel_fiber_le {p T a w : ℝ} (hp : 0 < p)
    (ha : a ∈ Icc 0 T) (hw : w ∈ Icc 0 T)
    (K J : ℝ → ℝ≥0∞) (s : Set (ℝ × ℝ)) :
    (∫⁻ v in Icc 0 T, (triangle 0 v ∩ s).indicator
      (fun q => K q.1 * J q.2 * ENNReal.ofReal
        (orderedPowerKernel p q.1 q.2 v)) (a, w)) ≤
      ENNReal.ofReal (1 / p) * K a *
        ((Ici a ∩ (Prod.mk a ⁻¹' s)).indicator J w) := by
  classical
  by_cases h : a ≤ w ∧ (a, w) ∈ s
  · have heq : (fun v => (triangle 0 v ∩ s).indicator
        (fun q => K q.1 * J q.2 * ENNReal.ofReal
          (orderedPowerKernel p q.1 q.2 v)) (a, w)) =
        (Ici w).indicator (fun v => K a * J w * ENNReal.ofReal
          (orderedPowerKernel p a w v)) := by
      funext v
      simp only [indicator_apply, mem_inter_iff, triangle, mem_ofPred_eq, mem_Ici]
      simp only [ha.1, h.1, h.2, true_and, and_true]
    have hset : Ici w ∩ Icc 0 T = Icc w T := by
      ext v
      simp only [mem_inter_iff, mem_Ici, mem_Icc]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hw.1.trans h.1, h.2⟩⟩
    rw [heq, lintegral_indicator measurableSet_Ici,
      Measure.restrict_restrict measurableSet_Ici, hset,
      lintegral_const_mul (K a * J w) (by unfold orderedPowerKernel; fun_prop),
      indicator_of_mem (show w ∈ Ici a ∩ (Prod.mk a ⁻¹' s) from h)]
    calc
      K a * J w * (∫⁻ v in Icc w T, ENNReal.ofReal (orderedPowerKernel p a w v)) ≤
          K a * J w * ENNReal.ofReal (1 / p) := by
        gcongr
        exact lintegral_orderedPowerKernel_le hp h.1 hw.2
      _ = ENNReal.ofReal (1 / p) * K a * J w := by ring
  · have hzero : (∫⁻ v in Icc 0 T, (triangle 0 v ∩ s).indicator
        (fun q => K q.1 * J q.2 * ENNReal.ofReal
          (orderedPowerKernel p q.1 q.2 v)) (a, w)) = 0 := by
      calc
        _ = ∫⁻ _ in Icc 0 T, (0 : ℝ≥0∞) := by
          apply lintegral_congr
          intro v
          apply indicator_of_notMem
          simp only [mem_inter_iff, triangle, mem_ofPred_eq]
          tauto
        _ = 0 := lintegral_zero
    rw [hzero]
    exact zero_le

/-- Tonelli and the outgoing mass bound reduce the operator to a pair integral.
No finiteness assumptions are needed. -/
theorem lintegral_orderedKernelDensity_le {p T : ℝ} (hp : 0 < p)
    {K J : ℝ → ℝ≥0∞}
    (hK : AEMeasurable K (volume.restrict (Icc 0 T)))
    (hJ : AEMeasurable J (volume.restrict (Icc 0 T)))
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) :
    (∫⁻ v in Icc 0 T, orderedKernelDensity p T K J s v) ≤
      ENNReal.ofReal (1 / p) * ∫⁻ a in Icc 0 T,
        K a * ∫⁻ w in Icc 0 T, (Ici a ∩ (Prod.mk a ⁻¹' s)).indicator J w := by
  classical
  rw [lintegral_orderedKernelDensity_swap hK hJ hs]
  have heq : (∫⁻ a in Icc 0 T, ∫⁻ w in Icc 0 T,
      ENNReal.ofReal (1 / p) * K a * ((Ici a ∩ (Prod.mk a ⁻¹' s)).indicator J w)) =
      ENNReal.ofReal (1 / p) * ∫⁻ a in Icc 0 T,
        K a * ∫⁻ w in Icc 0 T, (Ici a ∩ (Prod.mk a ⁻¹' s)).indicator J w := by
    have hin (a : ℝ) : AEMeasurable
        (fun w => (Ici a ∩ (Prod.mk a ⁻¹' s)).indicator J w) (volume.restrict (Icc 0 T)) :=
      hJ.indicator (measurableSet_Ici.inter (hs.preimage (measurable_const.prodMk measurable_id)))
    simp_rw [lintegral_const_mul'' _ (hin _), mul_assoc]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [← heq]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with w hw
  exact lintegral_kernel_fiber_le hp ha hw K J s

/-- The full ordered operator has `L¹` bound `1/p` times the product of input masses. -/
theorem lintegral_orderedKernelDensity_univ_le {p T : ℝ} (hp : 0 < p)
    {K J : ℝ → ℝ≥0∞}
    (hK : AEMeasurable K (volume.restrict (Icc 0 T)))
    (hJ : AEMeasurable J (volume.restrict (Icc 0 T))) :
    (∫⁻ v in Icc 0 T, orderedKernelDensity p T K J univ v) ≤
      ENNReal.ofReal (1 / p) * (∫⁻ a in Icc 0 T, K a) * (∫⁻ w in Icc 0 T, J w) := by
  apply (lintegral_orderedKernelDensity_le hp hK hJ MeasurableSet.univ).trans
  calc
    ENNReal.ofReal (1 / p) * (∫⁻ a in Icc 0 T,
        K a * ∫⁻ w in Icc 0 T, (Ici a ∩ (Prod.mk a ⁻¹' univ)).indicator J w) ≤
        ENNReal.ofReal (1 / p) * (∫⁻ a in Icc 0 T,
          K a * ∫⁻ w in Icc 0 T, J w) := by
      gcongr with a w
      exact indicator_le_self' (fun _ _ => zero_le) _
    _ = ENNReal.ofReal (1 / p) * (∫⁻ a in Icc 0 T, K a) *
        (∫⁻ w in Icc 0 T, J w) := by
      rw [lintegral_mul_const'' _ hK, mul_assoc]

end EmcsfAcExtension
