module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Calculus.Normalized
import EmcsfAcExtension.Infra.Calculus.PartialsC1

/-! # Integrating potential partial differences from the axis gauge

The exact primitive integrates continuous classical partials. Bounds
are imposed only off the axis; the endpoint is a null set.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- A uniform outgoing potential-partial comparison gives the potential
distance with the exact interval-length factor `T`, independently of
all parameters and the pair. This conditional helper discharges its
axis value using the restart gauge. -/
theorem stab_potential_sup_le_of_partial
    {e T ε M A B : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hB : 0 ≤ B)
    (hpartial : ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ T →
      |pdV (triangle 0 T) S₁.A u v - pdV (triangle 0 T) S₂.A u v| ≤ B) :
    supDist T S₁.A S₂.A ≤ ENNReal.ofReal (T * B) := by
  apply iSup₂_le
  rintro ⟨u, v⟩ hp
  let f : ℝ → ℝ := fun s => S₁.A u s - S₂.A u s
  let g : ℝ → ℝ := fun s => pdV (triangle 0 T) S₁.A u s - pdV (triangle 0 T) S₂.A u s
  have hmap : MapsTo (fun s : ℝ => (u, s)) (Icc u v) (triangle 0 T) :=
    fun s hs => ⟨hp.1, hs.1, hs.2.trans hp.2.2⟩
  have cf : ContinuousOn f (Icc u v) := by
    simpa only [f, Function.comp_def] using!
      (h₁s.c1.c1_A.continuousOn.sub h₂s.c1.c1_A.continuousOn).comp
        (continuous_const.prodMk continuous_id).continuousOn hmap
  have cg : ContinuousOn g (Icc u v) := by
    simpa only [g, Function.comp_def] using!
      ((continuousOn_partial_v h₁s.c1.c1_A (uniqueDiffOn_triangle h₁s.pos)).sub
        (continuousOn_partial_v h₂s.c1.c1_A (uniqueDiffOn_triangle h₂s.pos))).comp
          (continuous_const.prodMk continuous_id).continuousOn hmap
  have hd : ∀ s ∈ Ioo u v, HasDerivAt f (g s) s := by
    intro s hs
    exact ((hasDerivWithinAt_v_aux h₁s.c1.c1_A hp.1 hs.1.le (hs.2.le.trans hp.2.2)).sub
      (hasDerivWithinAt_v_aux h₂s.c1.c1_A hp.1 hs.1.le (hs.2.le.trans hp.2.2))).hasDerivAt
        (Icc_mem_nhds hs.1 (hs.2.trans_le hp.2.2))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hp.2.1 cf hd
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hp.2.1 cg)
  have haxis : f u = 0 := by
    dsimp only [f]
    rw [h₁s.data.2 u ⟨hp.1, hp.2.1.trans hp.2.2⟩,
      h₂s.data.2 u ⟨hp.1, hp.2.1.trans hp.2.2⟩, sub_self]
  have heq : f v = ∫ s in u..v, g s := by simpa only [haxis, sub_zero] using hi.symm
  have hAE : ∀ᵐ s ∂volume.restrict (Icc u v), ‖g s‖ ≤ B := by
    have hne : ∀ᵐ s : ℝ, s ≠ u := by simp [ae_iff, measure_singleton]
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with s hs hsu
    rw [Real.norm_eq_abs]
    exact hpartial u s hp.1 (lt_of_le_of_ne hs.1 hsu.symm) (hs.2.trans hp.2.2)
  have hb := intervalIntegral.integral_mono_ae_restrict hp.2.1
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hp.2.1 cg.norm)
    (intervalIntegrable_const (c := B)) hAE
  have hn := (intervalIntegral.norm_integral_le_integral_norm (f := g) hp.2.1).trans hb
  rw [intervalIntegral.integral_const, smul_eq_mul] at hn
  rw [← ofReal_norm]
  change ENNReal.ofReal ‖f v‖ ≤ _
  apply ENNReal.ofReal_le_ofReal
  rw [heq]
  apply hn.trans
  exact mul_le_mul_of_nonneg_right (by linarith only [hp.1, hp.2.2] : v - u ≤ T) hB

end EmcsfAcExtension.Local
