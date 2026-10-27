module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.MomentsSections

/-! # The common initial outgoing geometry

Differentiate the exact radius primitive within the full initial
interval. This includes the vertex and outer endpoint and avoids
extending an off-axis field equation to the vertex by assumption.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

/-- The common initial radius gauge forces `λ(0,v)=1/2`, including
both endpoints. This exact identity has no constant or smallness
hypothesis beyond the classical stability setting. -/
theorem stab_initial_lam
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {v : ℝ} (hv : v ∈ Icc 0 T) :
    S.lam 0 v = 1 / 2 := by
  let : Fact (v ∈ Icc 0 T) := ⟨hv⟩
  have cL : ContinuousOn (S.lam 0) (Icc 0 T) := hset.c1.c1_lam.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn
    (fun s hs => ⟨le_rfl, hs.1, hs.2⟩)
  have hsub : uIcc 0 v ⊆ Icc 0 T := by
    rw [uIcc_of_le hv.1]
    exact Icc_subset_Icc_right hv.2
  have hi : HasDerivWithinAt (fun x => ∫ s in 0..x, S.lam 0 s)
      (S.lam 0 v) (Icc 0 T) v :=
    intervalIntegral.integral_hasDerivWithinAt_right (cL.mono hsub).intervalIntegrable
      (cL.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc v) (cL v hv)
  have heq : ∀ x ∈ Icc 0 T, x / 2 = ∫ s in 0..x, S.lam 0 s := by
    intro x hx
    exact (hset.data.1 x hx).1.symm.trans
      (stab_radius_out_integral hset le_rfl hx.1 hx.2).symm
  have hd : HasDerivWithinAt (fun x : ℝ => x / 2) (S.lam 0 v) (Icc 0 T) v :=
    hi.congr heq (heq v hv)
  have hc : HasDerivWithinAt (fun x : ℝ => x / 2) (1 / 2) (Icc 0 T) v :=
    (hasDerivWithinAt_id v (Icc 0 T)).div_const 2
  exact (hd.derivWithin (uniqueDiffOn_Icc hset.pos v hv)).symm.trans
    (hc.derivWithin (uniqueDiffOn_Icc hset.pos v hv))

end EmcsfAcExtension.Local
