module

public import EmcsfAcExtension.Local.Defs.Renormalized
public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.MomentsSections
import EmcsfAcExtension.Local.Calculus.Partials

/-! # Exact initial-j subtraction

The derivative and cubic differences are separated before any data-only
Hardy or mass-constraint estimate is applied, as in internal project record's initial-j proof.
-/

public section

open Set Complex MeasureTheory Filter Topology

namespace EmcsfAcExtension.Local.Stab

/-- The normalized initial datum of a standing classical solution is AC.
Its equality with the outgoing trace is used on the closed data interval. -/
theorem initial_datum_ac {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) : AbsolutelyContinuousOnInterval h 0 T := by
  have hc : ContDiffOn ℝ 1 (S.a 0) (Icc 0 T) :=
    (stab_normalized_out_c1 hset.c1).comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun v hv => ⟨le_rfl, hv.1, hv.2⟩)
  have hac : AbsolutelyContinuousOnInterval (S.a 0) 0 T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hset.pos.le] using hc
  apply hac.congr
  intro v hv
  rw [uIcc_of_le hset.pos.le] at hv
  exact (hset.data.1 v hv).2

/-- The initial ordinary datum derivative is the within-triangle partial
almost everywhere on its full interval. Endpoint junk values are not used. -/
theorem initial_pdV_eq_deriv_ae {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) :
    ∀ᵐ v ∂volume.restrict (Icc 0 T), pdV (triangle 0 T) S.a 0 v = deriv h v := by
  have hne₀ : ∀ᵐ v : ℝ, v ≠ 0 := by simp [ae_iff, measure_singleton]
  have hneT : ∀ᵐ v : ℝ, v ≠ T := by simp [ae_iff, measure_singleton]
  filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne₀,
    ae_restrict_of_ae hneT] with v hv hv₀ hvT
  have hv₀' : 0 < v := lt_of_le_of_ne hv.1 hv₀.symm
  have hvT' : v < T := lt_of_le_of_ne hv.2 hvT
  have hm : MapsTo (fun w : ℝ => ((0 : ℝ), w)) (Icc 0 T) (triangle 0 T) :=
    fun w hw => ⟨le_rfl, hw.1, hw.2⟩
  have hd := (hasDerivWithinAt_pdV (stab_normalized_out_c1 hset.c1)
    ⟨le_rfl, hv.1, hv.2⟩ hm).hasDerivAt (Icc_mem_nhds hv₀' hvT')
  have heq : h =ᶠ[𝓝 v] S.a 0 := by
    filter_upwards [Icc_mem_nhds hv₀' hvT'] with w hw
    exact (hset.data.1 w hw).2.symm
  exact (hd.congr_of_eventuallyEq heq).deriv.symm

end EmcsfAcExtension.Local.Stab
