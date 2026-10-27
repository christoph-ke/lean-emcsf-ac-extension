module

public import EmcsfAcExtension.Global.Calculus.CurveTrace
public import EmcsfAcExtension.Infra.Level.OrderIso
import EmcsfAcExtension.Infra.Density.Exit
import EmcsfAcExtension.Infra.Density.CurveChain
import EmcsfAcExtension.Infra.AC.Relabel

/-! # The improved outgoing label for the boundary chain rule

This is the label-change route selected by architecture internal project record (internal project
record).
The label is `v + ∫ |ρ|`, with the fixed initial L¹ density `ρ`; it is AC,
strictly increasing, and its inverse is 1-Lipschitz. No pointwise bound on
the initial derivative or uniform terminal Lipschitz constant is assumed.
Source: `charged_SF_new_version.tex:L1415–L1415`, approved internal project record (C5)–(C7).
-/

public section

open Set MeasureTheory Filter Topology Complex
open scoped NNReal

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
The difference of the improved label is its ordinary label difference plus
the integral of the fixed density norm. The identity holds on every pair of
labels of the proper interval and has no constants. -/
theorem improved_label_sub {ρ : ℝ → ℂ} {c d : ℝ}
    (hρ : IntervalIntegrable ρ volume c d) {v w : ℝ}
    (hv : v ∈ uIcc c d) (hw : w ∈ uIcc c d) :
    (w + ∫ s in c..w, ‖ρ s‖) - (v + ∫ s in c..v, ‖ρ s‖) =
      w - v + ∫ s in v..w, ‖ρ s‖ := by
  rw [← intervalIntegral.integral_interval_sub_left
    (hρ.norm.mono_set (uIcc_subset_uIcc left_mem_uIcc hw))
    (hρ.norm.mono_set (uIcc_subset_uIcc left_mem_uIcc hv))]
  ring

/-- [internal]
The fixed L¹ density defines an increasing AC homeomorphism of the compact
label interval onto its image. Its canonical inverse has Lipschitz constant
`1`, uniformly in the density and interval. This is the geometric label
part of the selected bridge; the field and trace consequences below use it.
No Lipschitz bound on the forward improved label is asserted. -/
theorem improved_label_properties {ρ : ℝ → ℂ} {c d : ℝ} (hcd : c ≤ d)
    (hρ : IntervalIntegrable ρ volume c d) :
    let y : ℝ → ℝ := fun v => v + ∫ s in c..v, ‖ρ s‖
    AbsolutelyContinuousOnInterval y c d ∧ StrictMonoOn y (Icc c d) ∧
      ∃ Y : Icc c d ≃o Icc (y c) (y d),
        (∀ v : Icc c d, (Y v : ℝ) = y v) ∧
        LipschitzWith 1 Y.symm := by
  let y : ℝ → ℝ := fun v => v + ∫ s in c..v, ‖ρ s‖
  have hy : AbsolutelyContinuousOnInterval y c d :=
    (LipschitzWith.id.lipschitzOnWith.absolutelyContinuousOnInterval).add
      (hρ.norm.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)
  have hinc {v w : ℝ} (hv : v ∈ Icc c d) (hw : w ∈ Icc c d) (hvw : v ≤ w) :
      w - v ≤ y w - y v := by
    dsimp only [y]
    rw [improved_label_sub hρ (by rwa [uIcc_of_le hcd]) (by rwa [uIcc_of_le hcd])]
    exact le_add_of_nonneg_right (intervalIntegral.integral_nonneg hvw (fun _ _ => norm_nonneg _))
  have hm : StrictMonoOn y (Icc c d) := by
    intro v hv w hw hvw
    have hh := hinc hv hw hvw.le
    linarith only [hh, hvw]
  have hc : ContinuousOn y (Icc c d) := by simpa only [uIcc_of_le hcd] using hy.continuousOn
  let Y := Level.intervalOrderIso hcd hc hm
  have hY (v : Icc c d) : (Y v : ℝ) = y v := Level.intervalOrderIso_apply hcd hc hm v
  refine ⟨hy, hm, Y, hY, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simp only [NNReal.coe_one, one_mul, Subtype.dist_eq]
  have hdist (v w : Icc c d) : dist (v : ℝ) w ≤ dist (y v) (y w) := by
    rcases le_total (v : ℝ) w with hvw | hwv
    · rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hvw),
        abs_of_nonpos (sub_nonpos.mpr (hm.monotoneOn v.property w.property hvw))]
      simpa only [neg_sub] using hinc v.property w.property hvw
    · rw [dist_comm, dist_comm (y v)]
      rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hwv),
        abs_of_nonpos (sub_nonpos.mpr (hm.monotoneOn w.property v.property hwv))]
      simpa only [neg_sub] using hinc w.property v.property hwv
  convert hdist (Y.symm p) (Y.symm q) using 1
  rw [← hY, ← hY, Y.apply_symm_apply, Y.apply_symm_apply]

/-- [internal]
A fixed-density outgoing primitive is Lipschitz in the improved label,
uniformly over incoming rows. The displayed constant `C` bounds its two
continuous factors; it is fixed before all rows and label pairs. This is
the outgoing part of the joint changed-label estimate C6 in internal project record. -/
theorem outgoing_dist_le_improved_label_of_primitive
    {f W : ℝ → ℝ → ℂ} {ρ : ℝ → ℂ} {a b c d C : ℝ}
    (hcd : c ≤ d) (_hC : 0 ≤ C) (hρ : IntervalIntegrable ρ volume c d)
    (hW : ∀ u ∈ Icc a b, IntervalIntegrable (W u) volume c d)
    (hbound : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d, ‖W u v‖ ≤ C * (1 + ‖ρ v‖))
    (hrep : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d, f u v = f u c + ∫ s in c..v, W u s) :
    ∀ u ∈ Icc a b, ∀ v ∈ Icc c d, ∀ w ∈ Icc c d,
      dist (f u v) (f u w) ≤ C *
        dist (v + ∫ s in c..v, ‖ρ s‖) (w + ∫ s in c..w, ‖ρ s‖) := by
  have hordered : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d, ∀ w ∈ Icc c d, v ≤ w →
      dist (f u v) (f u w) ≤ C *
        dist (v + ∫ s in c..v, ‖ρ s‖) (w + ∫ s in c..w, ‖ρ s‖) := by
    intro u hu v hv w hw hvw
    have hv' : v ∈ uIcc c d := by rwa [uIcc_of_le hcd]
    have hw' : w ∈ uIcc c d := by rwa [uIcc_of_le hcd]
    have hi : IntervalIntegrable (fun s => C * (1 + ‖ρ s‖)) volume v w :=
      ((intervalIntegrable_const.add hρ.norm).const_mul C).mono_set (uIcc_subset_uIcc hv' hw')
    have hb := intervalIntegral.norm_integral_le_of_norm_le hvw
      (ae_of_all _ fun s hs => hbound u hu s ⟨hv.1.trans hs.1.le, hs.2.trans hw.2⟩) hi
    have hdiff : f u w - f u v = ∫ s in v..w, W u s := by
      rw [hrep u hu w hw, hrep u hu v hv, add_sub_add_left_eq_sub,
        intervalIntegral.integral_interval_sub_left
          ((hW u hu).mono_set (uIcc_subset_uIcc left_mem_uIcc hw'))
          ((hW u hu).mono_set (uIcc_subset_uIcc left_mem_uIcc hv'))]
    have hinc : 0 ≤ (w + ∫ s in c..w, ‖ρ s‖) - (v + ∫ s in c..v, ‖ρ s‖) := by
      rw [improved_label_sub hρ hv' hw']
      exact add_nonneg (sub_nonneg.mpr hvw)
        (intervalIntegral.integral_nonneg hvw (fun _ _ => norm_nonneg _))
    rw [dist_comm, dist_eq_norm, hdiff]
    apply hb.trans_eq
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
      intervalIntegrable_const (hρ.norm.mono_set (uIcc_subset_uIcc hv' hw')),
      intervalIntegral.integral_const, smul_eq_mul, mul_one,
      Real.dist_eq, abs_of_nonpos (by linarith only [hinc])]
    rw [neg_sub, improved_label_sub hρ hv' hw']
  intro u hu v hv w hw
  rcases le_total v w with hvw | hwv
  · exact hordered u hu v hv w hw hvw
  · simpa only [dist_comm] using hordered u hu w hw v hv hwv

/-- [internal]
The joint changed-label modulus gives an AC trace. The incoming coordinate
has the displayed Lipschitz constant `M`; the outgoing coordinate uses the
fixed improved label with coefficient `C`. Both constants are local and
fixed before the boundary parameter is varied. This is the AC part of the
internal project record bridge, without a generic two-dimensional exceptional-set argument. -/
theorem trace_ac_of_improved_label_modulus
    {f : ℝ → ℝ → ℂ} {ρ : ℝ → ℂ} {V : ℝ → ℝ} {a b M C : ℝ} {K : ℝ≥0}
    (hab : a ≤ b) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hV : LipschitzOnWith K V (uIcc a b)) (hm : MonotoneOn V (uIcc a b))
    (hρ : IntervalIntegrable ρ volume (V a) (V b))
    (hbound : ∀ u ∈ Icc a b, ∀ w ∈ Icc a b,
      dist (f u (V u)) (f w (V w)) ≤ M * dist u w + C *
        dist (V u + ∫ s in V a..V u, ‖ρ s‖) (V w + ∫ s in V a..V w, ‖ρ s‖)) :
    AbsolutelyContinuousOnInterval (fun u => f u (V u)) a b := by
  let y : ℝ → ℝ := fun v => v + ∫ s in V a..v, ‖ρ s‖
  have hVaVb : V a ≤ V b := hm left_mem_uIcc right_mem_uIcc hab
  have hy : AbsolutelyContinuousOnInterval y (V a) (V b) :=
    (improved_label_properties hVaVb hρ).1
  have hym : MonotoneOn y (uIcc (V a) (V b)) := by
    simpa only [uIcc_of_le hVaVb] using (improved_label_properties hVaVb hρ).2.1.monotoneOn
  have hY : AbsolutelyContinuousOnInterval (y ∘ V) a b :=
    hy.comp_monotoneOn hV.absolutelyContinuousOnInterval hm
  let q : ℝ → ℝ := fun u => M * u + C * y (V u)
  have hq : AbsolutelyContinuousOnInterval q a b :=
    (LipschitzWith.id.lipschitzOnWith.absolutelyContinuousOnInterval.const_mul M).add
      (hY.const_mul C)
  apply Density.absolutelyContinuousOnInterval_of_dist_le_control hq
  have hordered : ∀ u ∈ uIcc a b, ∀ w ∈ uIcc a b, u ≤ w →
      dist (f u (V u)) (f w (V w)) ≤ dist (q u) (q w) := by
    intro u hu w hw huw
    have hvw := hm hu hw huw
    have hyvw := hym (hm.image_uIcc_subset ⟨u, hu, rfl⟩)
      (hm.image_uIcc_subset ⟨w, hw, rfl⟩) hvw
    have hb := hbound u (by simpa [uIcc_of_le hab] using hu)
      w (by simpa [uIcc_of_le hab] using hw)
    change dist (f u (V u)) (f w (V w)) ≤ M * dist u w + C * dist (y (V u)) (y (V w)) at hb
    have hqw : q u ≤ q w := add_le_add
      (mul_le_mul_of_nonneg_left huw hM) (mul_le_mul_of_nonneg_left hyvw hC)
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr huw),
      Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hyvw)] at hb
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hqw)]
    convert hb using 1
    dsimp [q]
    ring
  intro u hu w hw
  rcases le_total u w with huw | hwu
  · exact hordered u hu w hw huw
  · simpa only [dist_comm] using hordered w hw u hu hwu

end EmcsfAcExtension.Global.Exterior
