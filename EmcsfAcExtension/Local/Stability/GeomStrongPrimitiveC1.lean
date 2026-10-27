module

public import EmcsfAcExtension.Local.Stability.GeomStrongPrimitive
public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.MomentsSections

/-! # Inserting a classical radial moment into a geometric primitive

This bridge supplies the radius power inequalities from the fixed box;
it applies to the individual and difference incoming moments alike.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The classical fixed-box instance of the ordered primitive estimate.
The coefficient is exactly `C * B * D`, with the three input scopes
explicit and no minimum-radius or derivative-supremum dependence.
-/
theorem stab_geometric_primitive_ordered_of_c1_moment
    {e T ε M A u v p B C D : ℝ} {S : Fields} {h : ℝ → ℂ}
    {r : ℝ → ℝ} {y j : ℝ → ℂ} {K J : ℝ → ℝ≥0∞} {c : ℂ}
    (hset : StabSetting e T ε M A S h)
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hK : Measurable K)
    (hr : ∀ w ∈ Ioc u v, |r w| ≤ D * S.r u w)
    (hmoment : ∀ w ∈ Ioc u v, ENNReal.ofReal ‖y w‖ ≤ ENNReal.ofReal B *
      ∫⁻ s in Icc u w, ENNReal.ofReal ((S.r s w / S.r u w) ^ p) * K s)
    (hj : ∀ w ∈ Ioc u v, ‖j w‖ₑ ≤ J w)
    (hc : ‖c‖ₑ ≤ ENNReal.ofReal (C / (v - u) ^ 3)) :
    ‖c * ∫ w in u..v, (r w : ℂ) * starRingEnd ℂ (y w) * j w‖ₑ ≤
      ENNReal.ofReal (C * B * D) * stabOrderedKernel p K J u v := by
  have hR w (hw : w ∈ Ioc u v) : 0 < S.r u w ∧ S.r u w ≤ v - u :=
    ⟨hset.c1.r_pos (u, w) ⟨hu, hw.1.le, hw.2.trans hvT⟩ hw.1,
      ((stab_radius_bounds hset hu hw.1.le (hw.2.trans hvT)).2).trans
        (sub_le_sub_right hw.2 u)⟩
  have hρ w (hw : w ∈ Ioc u v) s (hs : s ∈ Icc u w) :
      0 ≤ S.r s w ∧ S.r s w ≤ w - s := by
    have hb := stab_radius_bounds hset (hu.trans hs.1) hs.2 (hw.2.trans hvT)
    exact ⟨(div_nonneg (sub_nonneg.mpr hs.2) (by norm_num : (0 : ℝ) ≤ 4)).trans hb.1, hb.2⟩
  have hk w (hw : w ∈ Ioc u v) : AEMeasurable
      (fun s => ENNReal.ofReal ((S.r s w / S.r u w) ^ p) * K s)
      (volume.restrict (Icc u w)) := by
    have hrr : ContinuousOn (fun s => S.r s w / S.r u w) (Icc u w) :=
      (hset.c1.c1_r.continuousOn.comp
        (continuous_id.prodMk continuous_const).continuousOn
          (fun s hs => ⟨hu.trans hs.1, hs.2, hw.2.trans hvT⟩)).div_const _
    exact ((ENNReal.continuous_ofReal.comp_continuousOn
      ((Real.continuous_rpow_const hp0).comp_continuousOn hrr)).aemeasurable
        measurableSet_Icc).mul hK.aemeasurable.restrict
  exact stab_geometric_primitive_ordered_of_moment
    (R := S.r u) (r := r) (ρ := fun w s => S.r s w) (y := y) (j := j)
    (K := K) (J := J) (c := c) huv hp0 hp1 hB hC hD
    hR hr hρ hk hmoment hj hc

end EmcsfAcExtension.Local
