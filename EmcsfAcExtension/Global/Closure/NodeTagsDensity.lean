module

public import EmcsfAcExtension.Global.Defs.Original
import EmcsfAcExtension.Global.Calculus.DensityRepresentative
import EmcsfAcExtension.Global.Calculus.Normalized
import EmcsfAcExtension.Global.Api.Domains
import EmcsfAcExtension.Infra.W11.EndpointAC
import EmcsfAcExtension.Infra.Null.Segments

/-! # Closed-cone AC through the fixed initial-density representation

The proper-rectangle primitive gives local AC away from the vertex. One
finite BV bound on the proper cone and its continuous trace then give AC
at the remaining endpoint. This is the approved density route, independently
of applying the frozen closed-cone `ac_out` directly.
Source: `charged_SF_new_version.tex:L4132–L4133`; internal project record, density route.
-/

public section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace EmcsfAcExtension.Global.Closure

private theorem ac_reflect {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => f (-x)) (-b) (-a) := by
  apply (AbsolutelyContinuousOnInterval.iff_exists_integral_complex (neg_le_neg hab)).mpr
  refine ⟨fun x => -deriv f (-x),
    ((IntervalIntegrable.iff_comp_neg (by finiteness)).mp
      hf.intervalIntegrable_deriv_complex).symm.neg, ?_⟩
  intro x hx
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_neg]
  simp only [neg_neg]
  have hxb : -x ≤ b := by linarith only [hx.1]
  have hax : a ≤ -x := by linarith only [hx.2]
  have hsub : uIcc (-x) b ⊆ uIcc a b := by
    rw [uIcc_of_le hxb, uIcc_of_le hab]
    exact Icc_subset_Icc hax le_rfl
  rw [(hf.mono hsub).integral_deriv_eq_sub_complex]
  abel

/-- [node sec:charged-closure#ac-route-density-representation]
The fixed initial-density primitive and the single proper local BV bound
give AC on the full selected cone, including its axis endpoint. Only the
initial row's AC is used to establish the positive-radius primitive; the
closed-cone AC conjunct is not invoked. No estimate constant is selected.
Source: charged_SF_new_version.tex:L4132–L4133; approved internal project record density route. -/
theorem ac_route_density_representation (ui e : ℝ) (S : Fields)
    (h : OriginalData ui e S) {us : ℝ} (hus : us ∈ Ioo ui 0) :
    AbsolutelyContinuousOnInterval (S.a us) us 0 := by
  have hseg : outSeg us us 0 ⊆ origDomain ui := by
    rintro ⟨u, v⟩ ⟨rfl, hv⟩
    exact ⟨hus.1.le, hus.2, hv⟩
  have hcont : ContinuousOn (S.a us) (Icc us 0) :=
    (Calculus.continuousOn_a h.solution).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => hseg ⟨rfl, hv⟩)
  obtain ⟨B, hB, hout, _hin⟩ := h.solution.bv_loc _ hseg (isCompact_outSeg us us 0)
  have hvar : eVariationOn (S.a us) (Icc us 0) ≤ B :=
    (hout us us 0 (Subset.refl _)).2.2.1
  let f := fun t => S.a us (-t)
  have hfcont : ContinuousOn f (Icc 0 (-us)) :=
    hcont.comp continuous_neg.continuousOn (fun t ht => by
      constructor <;> linarith only [ht.1, ht.2])
  have hlocal : ∀ c ∈ Ico 0 (-us), AbsolutelyContinuousOnInterval f 0 c := by
    intro c hc
    rcases hc.1.eq_or_lt with rfl | hcpos
    · exact AbsolutelyContinuousOnInterval.refl f 0
    have husc : us < -c := by linarith only [hc.2]
    have hrect : Icc ui us ×ˢ Icc (-c) 0 ⊆ origDomain ui ∩ {p | p.1 < p.2} := by
      rintro ⟨u, v⟩ ⟨hu, hv⟩
      have huv : u < v := hu.2.trans_lt (husc.trans_le hv.1)
      exact ⟨⟨hu.1, hu.2.trans_lt hus.2, huv.le, hv.2⟩, huv⟩
    obtain ⟨P, R, hP, hR, _hrep, hprim⟩ :=
      Calculus.exists_density_factors h.solution hus.1 (neg_neg_of_pos hcpos) hrect
    have hinit : AbsolutelyContinuousOnInterval (S.a ui) (-c) 0 := by
      apply h.datumAC.mono
      rw [uIcc_of_le h.ui_neg.le, uIcc_of_le (neg_nonpos.mpr hc.1)]
      exact Icc_subset_Icc (hus.1.trans husc).le le_rfl
    have hi := Density.intervalIntegrable_fixedDensity (neg_nonpos.mpr hc.1)
      (right_mem_Icc.mpr hus.1.le) hP hR hinit.intervalIntegrable_deriv_complex
    have hac : AbsolutelyContinuousOnInterval (S.a us) (-c) 0 :=
      (AbsolutelyContinuousOnInterval.iff_exists_integral_complex (neg_nonpos.mpr hc.1)).mpr
        ⟨_, hi, hprim us (right_mem_Icc.mpr hus.1.le)⟩
    simpa only [neg_zero, neg_neg] using ac_reflect (neg_nonpos.mpr hc.1) hac
  have hrefvar : eVariationOn f (Icc 0 (-us)) ≤ B := by
    have hh := eVariationOn.comp_le_of_antitoneOn (S.a us) (fun t : ℝ => -t)
      (fun x _ y _ hxy => neg_le_neg hxy)
      (show MapsTo (fun t : ℝ => -t) (Icc 0 (-us)) (Icc us 0) from fun t ht => by
        constructor <;> linarith only [ht.1, ht.2])
    exact hh.trans hvar
  have hac := W11.ac_of_local_ac_of_initial_variation_bounds
    (neg_nonneg.mpr hus.2.le) hfcont hlocal hB.ne
    (fun c hc => (eVariationOn.mono f (Icc_subset_Icc le_rfl hc.2.le)).trans hrefvar)
  simpa only [f, neg_neg, neg_zero] using ac_reflect (neg_nonneg.mpr hus.2.le) hac

end EmcsfAcExtension.Global.Closure
