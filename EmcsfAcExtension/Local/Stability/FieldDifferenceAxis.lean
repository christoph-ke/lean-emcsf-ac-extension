module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Api.Finite
import EmcsfAcExtension.Local.Calculus.AxisMatch
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Scalar comparison along the regular axis

The common axis gauge identifies the diagonal derivative with `j`.
Integrating its difference retains the vertex difference exactly.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The scalar difference on the regular axis is bounded by the vertex
difference plus the outgoing derivative distance, both with coefficient
`1`, uniformly in all parameters and the pair. The gauge is supplied
by the restart data, as required by internal project record. -/
theorem stab_axis_scalar_difference_le
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ENNReal.ofReal ‖S₁.phi t t - S₂.phi t t‖ ≤
      ENNReal.ofReal ‖h₁ 0 - h₂ 0‖ + jDist T S₁ S₂ := by
  let f : ℝ → ℂ := fun s => S₁.phi s s - S₂.phi s s
  let j : ℝ → ℂ := fun s => jC1 (triangle 0 T) S₁ s s - jC1 (triangle 0 T) S₂ s s
  have hmap : MapsTo (fun s : ℝ => (s, s)) (Icc 0 t) (triangle 0 T) :=
    fun s hs => ⟨hs.1, le_rfl, hs.2.trans ht.2⟩
  have cfFull : ContinuousOn
      (fun p : ℝ × ℝ => S₁.phi p.1 p.2 - S₂.phi p.1 p.2) (triangle 0 T) := by
    simpa only using! h₁s.c1.c1_phi.continuousOn.sub h₂s.c1.c1_phi.continuousOn
  have cjFull : ContinuousOn (fun p : ℝ × ℝ =>
      jC1 (triangle 0 T) S₁ p.1 p.2 - jC1 (triangle 0 T) S₂ p.1 p.2) (triangle 0 T) := by
    simpa only using! (continuousOn_jC1_aux h₁s.pos h₁s.c1).sub
      (continuousOn_jC1_aux h₂s.pos h₂s.c1)
  have cf : ContinuousOn f (Icc 0 t) := by
    simpa only [f, Function.comp_def] using!
      cfFull.comp (continuous_id.prodMk continuous_id).continuousOn hmap
  have cj : ContinuousOn j (Icc 0 t) := by
    simpa only [j, Function.comp_def] using!
      cjFull.comp (continuous_id.prodMk continuous_id).continuousOn hmap
  have hd : ∀ s ∈ Ioo 0 t, HasDerivAt f (j s) s := by
    intro s hs
    have hsT : s < T := hs.2.trans_le ht.2
    exact (((stab_axis h₁s.pos h₁s.c1 h₁s.data.2 ⟨hs.1.le, hsT.le⟩).2).sub
      ((stab_axis h₂s.pos h₂s.c1 h₂s.data.2 ⟨hs.1.le, hsT.le⟩).2)).hasDerivAt
        (Icc_mem_nhds hs.1 hsT)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 cf hd
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) ht.1 cj)
  have hzero : (0, 0) ∈ triangle (0 : ℝ) T := ⟨le_rfl, le_rfl, h₁s.pos.le⟩
  have hv₁ : S₁.phi 0 0 = h₁ 0 :=
    ((h₁s.c1.axis 0 hzero).2.2.2.2.1).symm.trans
      (h₁s.data.1 0 ⟨le_rfl, h₁s.pos.le⟩).2
  have hv₂ : S₂.phi 0 0 = h₂ 0 :=
    ((h₂s.c1.axis 0 hzero).2.2.2.2.1).symm.trans
      (h₂s.data.1 0 ⟨le_rfl, h₂s.pos.le⟩).2
  have heq : S₁.phi t t - S₂.phi t t = h₁ 0 - h₂ 0 + ∫ s in 0..t, j s := by
    rw [hi]
    dsimp only [f]
    rw [hv₁, hv₂]
    abel
  have hI : ENNReal.ofReal ‖∫ s in 0..t, j s‖ ≤ jDist T S₁ S₂ := by
    rw [ofReal_norm, intervalIntegral.integral_of_le ht.1]
    apply (enorm_integral_le_lintegral_enorm j).trans
    apply le_trans ?_ (lintegral_mono_set (show Ioc 0 t ⊆ Icc 0 T from
      fun s hs => ⟨hs.1.le, hs.2.trans ht.2⟩))
    apply setLIntegral_mono' measurableSet_Ioc
    intro s hs
    exact enorm_le_normEnvelope
      (fun u v => jC1 (triangle 0 T) S₁ u v - jC1 (triangle 0 T) S₂ u v) ⟨hs.1.le, le_rfl⟩
  rw [heq]
  calc
    _ ≤ ENNReal.ofReal ‖h₁ 0 - h₂ 0‖ + ENNReal.ofReal ‖∫ s in 0..t, j s‖ := by
      rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (norm_add_le _ _)
    _ ≤ _ := add_le_add le_rfl hI

end EmcsfAcExtension.Local
