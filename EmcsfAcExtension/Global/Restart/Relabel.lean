module

public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Relabel
import EmcsfAcExtension.Infra.Level.OrderIso
import EmcsfAcExtension.Global.Api.Definitions
import EmcsfAcExtension.Global.Calculus.Sections
import EmcsfAcExtension.Infra.BV.Basic
import EmcsfAcExtension.Global.Restart.ClassInvariance
import EmcsfAcExtension.Local.Api.Mono

/-! # The common restart coordinate and its affine continuation

Integrating the constant endpoint extension of `2λ` gives a global increasing
order isomorphism. This construction uses only proper closed sections of the
original domain, and supplies a canonical inverse.
-/

public section

open Set MeasureTheory Filter Topology

namespace EmcsfAcExtension.Global.Restart

/-- [node sec:charged-closure#coordinate-regularity]
The selected proper cone has a global C¹ increasing label with positive
locally BV derivative, chosen affinely above zero (`charged_SF_new_version.tex:L4137`–L4161,
L4189–L4189). No uniform quantitative constant is claimed. -/
theorem common_relabel (ui e us : ℝ) (S : Fields) (h : OriginalData ui e S)
    (hus : us ∈ Ioo ui 0) :
    ∃ F : ℝ ≃o ℝ, IsNullRelabel F ∧
      (∀ t ∈ Icc us 0, F t = selectedRelabel S us t) ∧
      (∀ t ∈ Ici 0, F t = selectedRelabel S us 0 + 2 * S.lam us 0 * t) := by
  have hrow : outSeg us us 0 ⊆ origDomain ui := by
    rintro p ⟨rfl, hp, hp0⟩
    exact ⟨hus.1.le, hus.2, hp, hp0⟩
  have hc := Calculus.continuousOn_out_section h.solution.cont_lam hrow
  have hv := (Calculus.bv_out_section h.solution hrow).1
  have hp (t : ℝ) (ht : t ∈ Icc us 0) : 0 < 2 * S.lam us t :=
    mul_pos (by norm_num) (h.solution.lam_pos (us, t) (hrow ⟨rfl, ht.1, ht.2⟩))
  let c (t : ℝ) := max us (min t 0)
  have cmem (t : ℝ) : c t ∈ Icc us 0 :=
    ⟨le_max_left _ _, max_le hus.2.le (min_le_right _ _)⟩
  have cc : Continuous c := continuous_const.max (continuous_id.min continuous_const)
  have cm : Monotone c := fun _ _ hst => max_le_max_left us (min_le_min_right 0 hst)
  have ceq (t : ℝ) (ht : t ∈ Icc us 0) : c t = t := by
    simp only [c, min_eq_left ht.2, max_eq_right ht.1]
  let g (t : ℝ) := 2 * S.lam us (c t)
  have cg : Continuous g := (continuousOn_const.mul hc).comp_continuous cc cmem
  have pg (t : ℝ) : 0 < g t := hp _ (cmem t)
  have vg (a b : ℝ) : eVariationOn g (Icc a b) < ⊤ := by
    have vg' : BoundedVariationOn (fun t => 2 * S.lam us t) (Icc us 0) := by
      simpa only [smul_eq_mul] using hv.const_smul (2 : ℝ)
    change eVariationOn ((fun t => 2 * S.lam us t) ∘ c) (Icc a b) < ⊤
    rw [eVariationOn.comp_eq_of_monotoneOn _ _ (cm.monotoneOn _)]
    exact lt_of_le_of_lt (eVariationOn.mono _ (by rintro _ ⟨t, _, rfl⟩; exact cmem t))
      vg'.lt_top
  let P (t : ℝ) := ∫ x in us..t, g x
  have dP (t : ℝ) : HasDerivAt P (g t) t :=
    intervalIntegral.integral_hasDerivAt_right (cg.intervalIntegrable us t)
      cg.stronglyMeasurable.stronglyMeasurableAtFilter cg.continuousAt
  have cP : Continuous P := continuous_iff_continuousAt.mpr (fun t => (dP t).continuousAt)
  have derP : deriv P = g := funext (fun t => (dP t).deriv)
  have c1P : ContDiff ℝ 1 P :=
    contDiff_one_iff_deriv.mpr ⟨fun t => (dP t).differentiableAt, derP ▸ cg⟩
  have mP : StrictMono P := strictMono_of_deriv_pos (fun t => by rw [derP]; exact pg t)
  have hleft (t : ℝ) (ht : t ≤ us) : P t = g us * (t - us) := by
    change (∫ x in us..t, g x) = _
    have heq : ∀ x ∈ uIcc us t, g x = g us := by
      intro x hx
      rw [uIcc_of_ge ht] at hx
      have hx0 : x ≤ 0 := hx.2.trans hus.2.le
      simp only [g, c, min_eq_left hx0, max_eq_left hx.2,
        min_eq_left hus.2.le, max_self]
    rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_const]
    simp only [smul_eq_mul, mul_comm]
  have hright (t : ℝ) (ht : 0 ≤ t) : P t = P 0 + g 0 * t := by
    have heq : ∀ x ∈ uIcc 0 t, g x = g 0 := by
      intro x hx
      rw [uIcc_of_le ht] at hx
      simp only [g, c, min_eq_right hx.1, min_self]
    have hi := intervalIntegral.integral_add_adjacent_intervals
      (cg.intervalIntegrable (μ := volume) us 0) (cg.intervalIntegrable (μ := volume) 0 t)
    change (∫ x in us..t, g x) = _
    rw [← hi, intervalIntegral.integral_congr heq, intervalIntegral.integral_const]
    simp only [P, sub_zero, smul_eq_mul, mul_comm]
  have htop : Tendsto P atTop atTop := by
    apply tendsto_atTop.2
    intro y
    filter_upwards [eventually_ge_atTop (max 0 ((y - P 0) / g 0))] with t ht
    have ht0 : 0 ≤ t := (le_max_left _ _).trans ht
    have hty : (y - P 0) / g 0 ≤ t := (le_max_right _ _).trans ht
    have hmul := (div_le_iff₀ (pg 0)).1 hty
    rw [hright t ht0]
    linarith only [hmul]
  have hbot : Tendsto P atBot atBot := by
    apply tendsto_atBot.2
    intro y
    filter_upwards [eventually_le_atBot (min us (us + y / g us))] with t ht
    have htu : t ≤ us := ht.trans (min_le_left _ _)
    have hty : t ≤ us + y / g us := ht.trans (min_le_right _ _)
    have hsub : t - us ≤ y / g us := by linarith only [hty]
    have hmul := (le_div_iff₀ (pg us)).1 hsub
    rw [hleft t htu, mul_comm]
    exact hmul
  have himage : P '' (univ : Set ℝ) = univ := by
    rw [image_univ, (cP.surjective htop hbot).range_eq]
  let E : (univ : Set ℝ) ≃o (univ : Set ℝ) :=
    Level.orderIsoOn_of_image_eq (mP.strictMonoOn _) himage
  let F : ℝ ≃o ℝ := (OrderIso.Set.univ : (univ : Set ℝ) ≃o ℝ).symm.trans
    (E.trans (OrderIso.Set.univ : (univ : Set ℝ) ≃o ℝ))
  have hF : (F : ℝ → ℝ) = P := by
    funext t
    change (E ⟨t, mem_univ t⟩ : ℝ) = P t
    exact Level.orderIsoOn_of_image_eq_apply (mP.strictMonoOn _) himage ⟨t, mem_univ t⟩
  have hvalid : IsNullRelabel F := by
    rw [IsNullRelabel, hF]
    exact ⟨c1P, fun t => by rw [derP]; exact pg t, by simpa only [derP] using vg⟩
  have hrform (t : ℝ) (ht : t ∈ Icc us 0) :
      IntegralForm (S.r us) (S.lam us) us t := by
    have hs : outSeg us us t ⊆ origDomain ui :=
      fun p hp => hrow ⟨hp.1, hp.2.1, hp.2.2.trans ht.2⟩
    have hbvr : BoundedVariationOn (S.r us) (Icc us t) := by
      simpa only [uIcc_of_le ht.1] using (h.solution.ac_out us us t ht.1 hs).1.boundedVariationOn
    apply Calculus.integralForm_of_continuousOn_of_bv_of_local_integralForm ht.1
      (Calculus.continuousOn_out_section h.solution.cont_r hs) hbvr
    intro a ha b hb hab
    exact (h.solution.eq_out us a b ha.1 hab (fun p hp =>
      hs ⟨hp.1, ha.1.le.trans hp.2.1, hp.2.2.trans hb.2.le⟩)).1
  have hmatch (t : ℝ) (ht : t ∈ Icc us 0) : P t = selectedRelabel S us t := by
    have heq : ∀ x ∈ uIcc us t, g x = 2 * S.lam us x := by
      intro x hx
      rw [uIcc_of_le ht.1] at hx
      simp only [g, ceq x ⟨hx.1, hx.2.trans ht.2⟩]
    change (∫ x in us..t, g x) = 2 * S.r us t
    rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_const_mul,
      ← (hrform t ht).2, (h.solution.axis us (hrow ⟨rfl, le_rfl, hus.2.le⟩)).1, sub_zero]
  refine ⟨F, hvalid, ?_, ?_⟩
  · simpa only [hF] using hmatch
  · intro t ht
    rw [hF, hright t ht, hmatch 0 ⟨hus.2.le, le_rfl⟩]
    simp only [g, ceq 0 ⟨hus.2.le, le_rfl⟩]

end EmcsfAcExtension.Global.Restart

open Set MeasureTheory

namespace EmcsfAcExtension.Global.Restart

/-- [internal] A common null pullback preserves the zero potential on the true axis. -/
theorem nullPullback_axis_gauge (S : Fields) (F : ℝ ≃o ℝ) (t : ℝ)
    (ht : S.A (F t) (F t) = 0) : (nullPullback S F F).A t t = 0 := by
  change deriv (F : ℝ → ℝ) t * S.A (F t) (F t) = 0
  rw [ht, mul_zero]

/-- [node sec:charged-closure#null-normalization]
The selected common label preserves the true axis and its gauge, normalizes
the row radius, and preserves the normalized datum, its AC and its exact TV
(`charged_SF_new_version.tex:L3954`–L4158). Every proper transformed triangle belongs to
the entire frozen solution class. No local restart theorem is used. -/
theorem null_normalization (ui e us : ℝ) (S : Fields) (h : OriginalData ui e S)
    (hus : us ∈ Ioo ui 0) :
    ∃ F : ℝ ≃o ℝ, IsNullRelabel F ∧ F us = 0 ∧ 0 < F 0 ∧
      (∀ t ∈ Icc us 0, F t = selectedRelabel S us t) ∧
      (∀ t ∈ Ici 0, F t = selectedRelabel S us 0 + 2 * S.lam us 0 * t) ∧
      AbsolutelyContinuousOnInterval ((nullPullback S F.symm F.symm).a 0) 0 (F 0) ∧
      eVariationOn ((nullPullback S F.symm F.symm).a 0) (Icc 0 (F 0)) =
        eVariationOn (S.a us) (Icc us 0) ∧
      (∀ v ∈ Icc 0 (F 0), (nullPullback S F.symm F.symm).r 0 v = v / 2 ∧
        (nullPullback S F.symm F.symm).a 0 v = S.a us (F.symm v)) ∧
      (∀ t ∈ Ico 0 (F 0), (nullPullback S F.symm F.symm).A t t = 0) ∧
      (∀ T' ∈ Ioo 0 (F 0),
        IsSolution e (nullPullback S F.symm F.symm) (triangle 0 T')) := by
  obtain ⟨F, hF, hm, hr⟩ := common_relabel ui e us S h hus
  have hrow : outSeg us us 0 ⊆ origDomain ui := by
    rintro p ⟨rfl, hp, hp0⟩
    exact ⟨hus.1.le, hus.2, hp, hp0⟩
  have hz : F us = 0 := by
    rw [hm us ⟨le_rfl, hus.2.le⟩, selectedRelabel,
      (h.solution.axis us (hrow ⟨rfl, le_rfl, hus.2.le⟩)).1, mul_zero]
  have hzi : F.symm 0 = us := by rw [← hz, F.symm_apply_apply]
  have hpos : 0 < F 0 := by
    calc
      0 = F us := hz.symm
      _ < F 0 := F.strictMono hus.2
  have hfi := hF.symm
  have ha : (nullPullback S F.symm F.symm).a 0 = fun v => S.a us (F.symm v) := by
    funext v
    rw [nullPullback_a S hfi, hzi]
  have hac : AbsolutelyContinuousOnInterval ((nullPullback S F.symm F.symm).a 0) 0 (F 0) := by
    rw [ha]
    apply ac_comp_nullLabel (f := S.a us) (a := 0) (b := F 0) hfi
    rw [hzi, F.symm_apply_apply]
    exact (h.solution.ac_out us us 0 hus.2.le hrow).2.2.2.2
  have hvar : eVariationOn ((nullPullback S F.symm F.symm).a 0) (Icc 0 (F 0)) =
      eVariationOn (S.a us) (Icc us 0) := by
    rw [ha, variation_comp_nullLabel, hzi, F.symm_apply_apply]
  refine ⟨F, hF, hz, hpos, hm, hr, hac, hvar, ?_, ?_, ?_⟩
  · intro v hv
    have ht : F.symm v ∈ Icc us 0 := by
      constructor
      · rw [← hzi]
        exact F.symm.monotone hv.1
      · simpa only [F.symm_apply_apply] using F.symm.monotone hv.2
    have he := hm (F.symm v) ht
    rw [F.apply_symm_apply] at he
    refine ⟨?_, ?_⟩
    · change S.r (F.symm 0) (F.symm v) = v / 2
      rw [hzi]
      dsimp only [selectedRelabel] at he
      linarith only [he]
    · rw [ha]
  · intro t ht
    apply nullPullback_axis_gauge
    apply h.gauge
    · exact hus.1.le.trans (by rw [← hzi]; exact F.symm.monotone ht.1)
    · have hlt := F.symm.strictMono ht.2
      simpa only [F.symm_apply_apply] using hlt
  · intro T' hT'
    apply relabel_class e 0 T' S F.symm hfi hT'.1
    apply Local.isSolution_mono h.solution
    apply triangle_subset_origDomain
    · rw [hzi]
      exact hus.1.le
    · have hlt := F.symm.strictMono hT'.2
      simpa only [F.symm_apply_apply] using hlt

end EmcsfAcExtension.Global.Restart
