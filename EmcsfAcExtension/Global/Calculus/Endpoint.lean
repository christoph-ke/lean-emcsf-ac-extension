/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Global.Calculus.Sections
import EmcsfAcExtension.Local.Calculus.Sections
import EmcsfAcExtension.Infra.BV.Basic
import EmcsfAcExtension.Infra.AC.Variation

/-! # Characteristic FTC at the existing regular axis

The AC fields give their own source integrability. The expansion equations use
local BV. The wave fields are BV products of expansions with normalized fields
minus the scalar. Maxwell's equation and the radius equation bound `Q / r²`,
which makes the potential source integrable as well. Every segment is required
to lie in the given solution domain, so no missing endpoint is adjoined.
-/

public section

open Set MeasureTheory Filter Topology Complex

namespace EmcsfAcExtension.Global.Calculus

variable {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}

private theorem xi_bv_out (hS : IsSolution e S D) {u a b : ℝ}
    (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    BoundedVariationOn (S.xi u) (Icc a b) := by
  have hbv := bv_out_section hS hs
  have hp := (hS.ac_out u a b hab hs).2.2.2.1.boundedVariationOn_Icc hab
  have he : EqOn (fun v => S.nu u v • (S.b u v - S.phi u v)) (S.xi u) (Icc a b) := by
    intro v hv
    have hn := (hS.nu_neg (u, v) (hs ⟨rfl, hv.1, hv.2⟩)).ne
    simp only [Fields.b, add_sub_cancel_left, Complex.real_smul]
    field_simp [Complex.ofReal_ne_zero.mpr hn]
  change eVariationOn (S.xi u) (Icc a b) ≠ ⊤
  rw [← eVariationOn.eq_of_eqOn he]
  exact hbv.2.1.smul (hbv.2.2.2.sub hp)

private theorem theta_bv_in (hS : IsSolution e S D) {a b v : ℝ}
    (hab : a ≤ b) (hs : inSeg a b v ⊆ D) :
    BoundedVariationOn (fun u => S.theta u v) (Icc a b) := by
  have hbv := bv_in_section hS hs
  have hp := (hS.ac_in a b v hab hs).2.2.2.boundedVariationOn_Icc hab
  have he : EqOn (fun u => S.lam u v • (S.a u v - S.phi u v))
      (fun u => S.theta u v) (Icc a b) := by
    intro u hu
    have hl := (hS.lam_pos (u, v) (hs ⟨hu.1, hu.2, rfl⟩)).ne'
    simp only [Fields.a, add_sub_cancel_left, Complex.real_smul]
    field_simp [Complex.ofReal_ne_zero.mpr hl]
  change eVariationOn (fun u => S.theta u v) (Icc a b) ≠ ⊤
  rw [← eVariationOn.eq_of_eqOn he]
  exact hbv.1.smul (hbv.2.2.1.sub hp)

private theorem out_forms (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u ≤ a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    IntegralForm (S.r u) (S.lam u) a b ∧
    IntegralForm (S.nu u) (S.rUV u) a b ∧
    IntegralForm (S.m u) (S.mV u) a b ∧
    IntegralForm (S.Q u) (S.QV e u) a b ∧
    IntegralForm (S.phi u) (S.phiV u) a b ∧
    IntegralForm (S.xi u) (S.xiV e u) a b := by
  have h c (hc : c ∈ Ioo a b) d (hd : d ∈ Ioo a b) (hcd : c ≤ d) :=
    hS.eq_out u c d (hua.trans_lt hc.1) hcd
      (fun p hp => hs (outSeg_subset_outSeg hc.1.le hd.2.le hp))
  have hac := hS.ac_out u a b hab hs
  have hbv := bv_out_section hS hs
  exact ⟨integralForm_of_continuousOn_of_bv_of_local_integralForm hab
      (continuousOn_out_section hS.cont_r hs) (hac.1.boundedVariationOn_Icc hab)
      (fun c hc d hd hcd => (h c hc d hd hcd).1),
    integralForm_of_continuousOn_of_bv_of_local_integralForm hab
      (continuousOn_out_section hS.cont_nu hs) hbv.2.1
      (fun c hc d hd hcd => (h c hc d hd hcd).2.1),
    integralForm_of_continuousOn_of_bv_of_local_integralForm hab
      (continuousOn_out_section hS.cont_m hs) (hac.2.1.boundedVariationOn_Icc hab)
      (fun c hc d hd hcd => (h c hc d hd hcd).2.2.1),
    integralForm_of_continuousOn_of_bv_of_local_integralForm hab
      (continuousOn_out_section hS.cont_Q hs) (hac.2.2.1.boundedVariationOn_Icc hab)
      (fun c hc d hd hcd => (h c hc d hd hcd).2.2.2.1),
    integralForm_of_continuousOn_of_bv_of_local_integralForm hab
      (continuousOn_out_section hS.cont_phi hs) (hac.2.2.2.1.boundedVariationOn_Icc hab)
      (fun c hc d hd hcd => (h c hc d hd hcd).2.2.2.2.2.1),
    integralForm_of_continuousOn_of_bv_of_local_integralForm hab
      (continuousOn_out_section hS.cont_xi hs) (xi_bv_out hS hab hs)
      (fun c hc d hd hcd => (h c hc d hd hcd).2.2.2.2.2.2)⟩

/-- [internal] All six incoming equations extend to any proper closed segment,
including its existing axis endpoint. Integrability is part of each conclusion:
AC supplies `ν,mU,QU,phiU`, BV supplies `rUV`, and the BV product
`θ = λ (a - φ)` supplies `thetaU`. -/
theorem in_integralForm (hS : IsSolution e S D) {a b v : ℝ}
    (hab : a ≤ b) (hbv : b ≤ v) (hs : inSeg a b v ⊆ D) :
    IntegralForm (fun u => S.r u v) (fun u => S.nu u v) a b ∧
    IntegralForm (fun u => S.lam u v) (fun u => S.rUV u v) a b ∧
    IntegralForm (fun u => S.m u v) (fun u => S.mU u v) a b ∧
    IntegralForm (fun u => S.Q u v) (fun u => S.QU e u v) a b ∧
    IntegralForm (fun u => S.phi u v) (fun u => S.phiU e u v) a b ∧
    IntegralForm (fun u => S.theta u v) (fun u => S.thetaU e u v) a b := by
  have h c (hc : c ∈ Ioo a b) d (hd : d ∈ Ioo a b) (hcd : c ≤ d) :=
    hS.eq_in c d v hcd (hd.2.trans_le hbv)
      (fun p hp => hs (inSeg_subset_inSeg hc.1.le hd.2.le hp))
  have hac := hS.ac_in a b v hab hs
  have hvar := bv_in_section hS hs
  exact ⟨integralForm_of_continuousOn_of_bv_of_local_integralForm hab
      (continuousOn_in_section hS.cont_r hs) (hac.1.boundedVariationOn_Icc hab)
      (fun c hc d hd hcd => (h c hc d hd hcd).1),
    integralForm_of_continuousOn_of_bv_of_local_integralForm hab
      (continuousOn_in_section hS.cont_lam hs) hvar.1
      (fun c hc d hd hcd => (h c hc d hd hcd).2.1),
    integralForm_of_continuousOn_of_bv_of_local_integralForm hab
      (continuousOn_in_section hS.cont_m hs) (hac.2.1.boundedVariationOn_Icc hab)
      (fun c hc d hd hcd => (h c hc d hd hcd).2.2.1),
    integralForm_of_continuousOn_of_bv_of_local_integralForm hab
      (continuousOn_in_section hS.cont_Q hs) (hac.2.2.1.boundedVariationOn_Icc hab)
      (fun c hc d hd hcd => (h c hc d hd hcd).2.2.2.1),
    integralForm_of_continuousOn_of_bv_of_local_integralForm hab
      (continuousOn_in_section hS.cont_phi hs) (hac.2.2.2.boundedVariationOn_Icc hab)
      (fun c hc d hd hcd => (h c hc d hd hcd).2.2.2.2.1),
    integralForm_of_continuousOn_of_bv_of_local_integralForm hab
      (continuousOn_in_section hS.cont_theta hs) (theta_bv_in hS hab hs)
      (fun c hc d hd hcd => (h c hc d hd hcd).2.2.2.2.2)⟩

private theorem charge_square_bound {r l Q q : ℝ → ℝ} {a b C : ℝ}
    (hr : ∀ x ∈ Icc a b, IntegralForm r l a x)
    (hQ : ∀ x ∈ Icc a b, IntegralForm Q q a x)
    (hr0 : r a = 0) (hQ0 : Q a = 0)
    (hb : ∀ x ∈ Icc a b, ‖q x‖ ≤ C * (r x * l x)) :
    ∀ x ∈ Icc a b, ‖Q x‖ ≤ C / 2 * r x ^ 2 := by
  intro x hx
  have hr' := ac_ae_of_integralForm_on hx.1
    (fun y hy => hr y ⟨hy.1, hy.2.trans hx.2⟩)
  have hl := (hr x hx).1
  have hrl : IntervalIntegrable (fun y => r y * l y) volume a x := by
    simpa only [mul_comm] using hl.mul_continuousOn hr'.1.continuousOn
  have hd : ∀ᵐ y, y ∈ uIcc a x → HasDerivAt (fun z => r z * r z)
      (r y * l y + r y * l y) y := by
    rw [← ae_restrict_iff' measurableSet_uIcc, uIcc_of_le hx.1]
    exact hr'.2.mono fun y hy => by simpa only [Pi.mul_apply, mul_comm] using! hy.mul hy
  have hi := (hr'.1.mul hr'.1).integral_eq_sub_of_ae_hasDerivAt_normed
    (hrl.add hrl) hd
  rw [intervalIntegral.integral_add hrl hrl] at hi
  simp only [Pi.mul_apply, hr0, mul_zero, sub_zero] at hi
  have hqi := (hQ x hx).1
  have hqeq := (hQ x hx).2
  rw [hQ0, sub_zero] at hqeq
  calc
    ‖Q x‖ = ‖∫ y in a..x, q y‖ := congrArg norm hqeq
    _ ≤ ∫ y in a..x, ‖q y‖ := intervalIntegral.norm_integral_le_integral_norm hx.1
    _ ≤ ∫ y in a..x, C * (r y * l y) :=
      intervalIntegral.integral_mono_on hx.1 hqi.norm (hrl.const_mul C)
        (fun y hy => hb y ⟨hy.1, hy.2.trans hx.2⟩)
    _ = C / 2 * r x ^ 2 := by
      rw [intervalIntegral.integral_const_mul]
      rw [pow_two, ← hi]
      ring

private theorem continuousOn_mu_out_axis (hS : IsSolution e S D) {u b : ℝ}
    (hub : u ≤ b) (hs : outSeg u u b ⊆ D) : ContinuousOn (S.mu u) (Icc u b) := by
  have cr := continuousOn_out_section hS.cont_r hs
  have cm := continuousOn_out_section hS.cont_m hs
  intro x hx
  rcases hx.1.eq_or_lt with rfl | hux
  · apply continuousWithinAt_sdiff_self.mp
    have hp : (u, u) ∈ D := hs ⟨rfl, le_rfl, hub⟩
    have hm : S.mu u u = 0 := by simp [Fields.mu, (hS.axis u hp).1]
    change Tendsto (S.mu u) (𝓝[Icc u b \ {u}] u) (𝓝 (S.mu u u))
    rw [hm]
    change Tendsto (Function.uncurry S.mu ∘ fun y : ℝ => (u, y))
      (𝓝[Icc u b \ {u}] u) (𝓝 0)
    apply (hS.axis_mu u hp).comp
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(continuous_const.prodMk continuous_id).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact ⟨hs ⟨rfl, hy.1.1, hy.1.2⟩,
      lt_of_le_of_ne hy.1.1 (show y ≠ u from hy.2).symm⟩
  · exact ((continuousWithinAt_const.mul (cm x hx)).div (cr x hx)
      (hS.r_pos (u, x) (hs ⟨rfl, hx.1, hx.2⟩) hux).ne')

private theorem integrable_AV_axis (hS : IsSolution e S D) {u b : ℝ}
    (hub : u ≤ b) (hs : outSeg u u b ⊆ D) :
    IntervalIntegrable (S.AV u) volume u b := by
  have cr := continuousOn_out_section hS.cont_r hs
  have cl := continuousOn_out_section hS.cont_lam hs
  have cn := continuousOn_out_section hS.cont_nu hs
  have cp := continuousOn_out_section hS.cont_phi hs
  have ct := continuousOn_out_section hS.cont_theta hs
  have cq := continuousOn_out_section hS.cont_Q hs
  have cmu := continuousOn_mu_out_axis hS hub hs
  have pos (x : ℝ) (hx : x ∈ Icc u b) := hS.lam_pos (u, x) (hs ⟨rfl, hx.1, hx.2⟩)
  have cg : ContinuousOn (fun x => -(e * (starRingEnd ℂ (S.phi u x) * S.theta u x).im) /
      S.lam u x) (Icc u b) :=
    (continuousOn_const.mul (Complex.continuous_im.comp_continuousOn (cp.star.mul ct))).neg.div cl
      (fun x hx => (pos x hx).ne')
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image cg.norm
  have hbound : ∀ x ∈ Icc u b, ‖S.QV e u x‖ ≤ C * (S.r u x * S.lam u x) := by
    intro x hx
    have hp : (u, x) ∈ D := hs ⟨rfl, hx.1, hx.2⟩
    have hr : 0 ≤ S.r u x := by
      rcases hx.1.eq_or_lt with rfl | hux
      · rw [(hS.axis u hp).1]
      · exact (hS.r_pos (u, x) hp hux).le
    have he : S.QV e u x =
        (-(e * (starRingEnd ℂ (S.phi u x) * S.theta u x).im) / S.lam u x) *
          (S.r u x * S.lam u x) := by
      unfold Fields.QV
      field_simp [(pos x hx).ne']
    rw [he, norm_mul, Real.norm_eq_abs (S.r u x * S.lam u x),
      abs_of_nonneg (mul_nonneg hr (pos x hx).le)]
    exact mul_le_mul_of_nonneg_right (hC (mem_image_of_mem _ hx))
      (mul_nonneg hr (pos x hx).le)
  have forms (x : ℝ) (hx : x ∈ Icc u b) :=
    out_forms hS le_rfl hx.1 (fun _ hp => hs (outSeg_subset_outSeg le_rfl hx.2 hp))
  have hp : (u, u) ∈ D := hs ⟨rfl, le_rfl, hub⟩
  have hQ := charge_square_bound (fun x hx => (forms x hx).1)
    (fun x hx => (forms x hx).2.2.2.1) (hS.axis u hp).1
    (hS.axis u hp).2.2.1 hbound
  have hratio : ∀ x ∈ Icc u b, ‖S.Q u x / S.r u x ^ 2‖ ≤ max (C / 2) 0 := by
    intro x hx
    by_cases hr : S.r u x = 0
    · simp only [hr, zero_pow (by decide : 2 ≠ 0), div_zero, norm_zero]
      exact le_max_right _ _
    · rw [norm_div, Real.norm_eq_abs (S.r u x ^ 2), abs_of_nonneg (sq_nonneg _)]
      exact ((div_le_iff₀ (sq_pos_of_ne_zero hr)).2 (hQ x hx)).trans (le_max_left _ _)
  have hi : IntegrableOn (fun x => S.Q u x / S.r u x ^ 2) (Icc u b) := by
    apply Integrable.mono' (integrableOn_const (C := max (C / 2) 0)
      (measure_Icc_lt_top.ne))
    · exact (cq.aemeasurable measurableSet_Icc).div
        ((cr.pow 2).aemeasurable measurableSet_Icc) |>.aestronglyMeasurable
    · exact (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hratio)
  have cf : ContinuousOn (fun x => 2 * S.nu u x * S.lam u x / (1 - S.mu u x))
      (Icc u b) :=
    ((continuousOn_const.mul cn).mul cl).div (continuousOn_const.sub cmu)
      (fun x hx => (hS.one_sub_mu_pos (u, x) (hs ⟨rfl, hx.1, hx.2⟩)).ne')
  have hii := (intervalIntegrable_iff_integrableOn_Icc_of_le hub).2 hi
  convert hii.continuousOn_mul (by simpa only [uIcc_of_le hub] using cf) using 1
  funext x
  dsimp [Fields.AV]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- [internal] All seven outgoing equations extend to any proper closed segment,
including its existing axis endpoint. The potential source is proved integrable
from Maxwell and the radius equation; all other sources follow from AC or BV. -/
theorem out_integralForm (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u ≤ a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    IntegralForm (S.r u) (S.lam u) a b ∧
    IntegralForm (S.nu u) (S.rUV u) a b ∧
    IntegralForm (S.m u) (S.mV u) a b ∧
    IntegralForm (S.Q u) (S.QV e u) a b ∧
    IntegralForm (S.A u) (S.AV u) a b ∧
    IntegralForm (S.phi u) (S.phiV u) a b ∧
    IntegralForm (S.xi u) (S.xiV e u) a b := by
  rcases hua.eq_or_lt with rfl | hua
  · have h := out_forms hS le_rfl hab hs
    refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_, h.2.2.2.2.1, h.2.2.2.2.2⟩
    apply integralForm_of_continuousOn_of_local_integralForm_of_intervalIntegrable hab
      (continuousOn_out_section hS.cont_A hs) (integrable_AV_axis hS hab hs)
    intro c hc d hd hcd
    exact (hS.eq_out u c d hc.1 hcd
      (fun _ hp => hs (outSeg_subset_outSeg hc.1.le hd.2.le hp))).2.2.2.2.1
  · exact hS.eq_out u a b hua hab hs

/-- [internal] All outgoing equation fields are AC through an existing endpoint,
with their literal frozen derivatives a.e. on the closed label interval.
Off-axis segments reuse the frozen-class sectional calculus from `Local`. -/
theorem out_section (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u ≤ a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    (AbsolutelyContinuousOnInterval (S.r u) a b ∧
      ∀ᵐ v ∂volume.restrict (Icc a b), HasDerivAt (S.r u) (S.lam u v) v) ∧
    (AbsolutelyContinuousOnInterval (S.nu u) a b ∧
      ∀ᵐ v ∂volume.restrict (Icc a b), HasDerivAt (S.nu u) (S.rUV u v) v) ∧
    (AbsolutelyContinuousOnInterval (S.m u) a b ∧
      ∀ᵐ v ∂volume.restrict (Icc a b), HasDerivAt (S.m u) (S.mV u v) v) ∧
    (AbsolutelyContinuousOnInterval (S.Q u) a b ∧
      ∀ᵐ v ∂volume.restrict (Icc a b), HasDerivAt (S.Q u) (S.QV e u v) v) ∧
    (AbsolutelyContinuousOnInterval (S.A u) a b ∧
      ∀ᵐ v ∂volume.restrict (Icc a b), HasDerivAt (S.A u) (S.AV u v) v) ∧
    (AbsolutelyContinuousOnInterval (S.phi u) a b ∧
      ∀ᵐ v ∂volume.restrict (Icc a b), HasDerivAt (S.phi u) (S.phiV u v) v) ∧
    (AbsolutelyContinuousOnInterval (S.xi u) a b ∧
      ∀ᵐ v ∂volume.restrict (Icc a b), HasDerivAt (S.xi u) (S.xiV e u v) v) := by
  by_cases hua' : u < a
  · exact Local.IsSolution.out_section hS hua' hab hs
  have h x (hx : x ∈ Icc a b) := out_integralForm hS hua hx.1
    (fun _ hp => hs (outSeg_subset_outSeg le_rfl hx.2 hp))
  exact ⟨ac_ae_of_integralForm_on hab (fun x hx => (h x hx).1),
    ac_ae_of_integralForm_on hab (fun x hx => (h x hx).2.1),
    ac_ae_of_integralForm_on hab (fun x hx => (h x hx).2.2.1),
    ac_ae_of_integralForm_on hab (fun x hx => (h x hx).2.2.2.1),
    ac_ae_of_integralForm_on hab (fun x hx => (h x hx).2.2.2.2.1),
    ac_ae_of_integralForm_on hab (fun x hx => (h x hx).2.2.2.2.2.1),
    ac_ae_of_integralForm_on hab (fun x hx => (h x hx).2.2.2.2.2.2)⟩

/-- [internal] All incoming equation fields are AC through an existing endpoint,
with their literal frozen derivatives a.e. on the closed label interval.
The axis derivative itself is not evaluated pointwise. -/
theorem in_section (hS : IsSolution e S D) {a b v : ℝ}
    (hab : a ≤ b) (hbv : b ≤ v) (hs : inSeg a b v ⊆ D) :
    (AbsolutelyContinuousOnInterval (fun u => S.r u v) a b ∧
      ∀ᵐ u ∂volume.restrict (Icc a b), HasDerivAt (fun x => S.r x v) (S.nu u v) u) ∧
    (AbsolutelyContinuousOnInterval (fun u => S.lam u v) a b ∧
      ∀ᵐ u ∂volume.restrict (Icc a b), HasDerivAt (fun x => S.lam x v) (S.rUV u v) u) ∧
    (AbsolutelyContinuousOnInterval (fun u => S.m u v) a b ∧
      ∀ᵐ u ∂volume.restrict (Icc a b), HasDerivAt (fun x => S.m x v) (S.mU u v) u) ∧
    (AbsolutelyContinuousOnInterval (fun u => S.Q u v) a b ∧
      ∀ᵐ u ∂volume.restrict (Icc a b), HasDerivAt (fun x => S.Q x v) (S.QU e u v) u) ∧
    (AbsolutelyContinuousOnInterval (fun u => S.phi u v) a b ∧
      ∀ᵐ u ∂volume.restrict (Icc a b), HasDerivAt (fun x => S.phi x v) (S.phiU e u v) u) ∧
    (AbsolutelyContinuousOnInterval (fun u => S.theta u v) a b ∧
      ∀ᵐ u ∂volume.restrict (Icc a b), HasDerivAt (fun x => S.theta x v) (S.thetaU e u v) u) := by
  by_cases hbv' : b < v
  · exact Local.IsSolution.in_section hS hab hbv' hs
  have h x (hx : x ∈ Icc a b) := in_integralForm hS hx.1 (hx.2.trans hbv)
    (fun _ hp => hs (inSeg_subset_inSeg le_rfl hx.2 hp))
  exact ⟨ac_ae_of_integralForm_on hab (fun x hx => (h x hx).1),
    ac_ae_of_integralForm_on hab (fun x hx => (h x hx).2.1),
    ac_ae_of_integralForm_on hab (fun x hx => (h x hx).2.2.1),
    ac_ae_of_integralForm_on hab (fun x hx => (h x hx).2.2.2.1),
    ac_ae_of_integralForm_on hab (fun x hx => (h x hx).2.2.2.2.1),
    ac_ae_of_integralForm_on hab (fun x hx => (h x hx).2.2.2.2.2)⟩

/-- [node sec:charged-equations#existing-axis-endpoint-calculus]
The characteristic FTC passes to every existing axis endpoint in the original
development (`charged_SF_new_version.tex:L677–L680`). Each `IntegralForm` includes
integrability of its literal frozen equation source. The missing point `(0,0)`
is excluded by segment inclusion in `origDomain ui`. -/
theorem existing_axis_endpoint_calculus {ui : ℝ} (hS : IsSolution e S (origDomain ui)) :
    (∀ u b, u ≤ b → outSeg u u b ⊆ origDomain ui →
      IntegralForm (S.r u) (S.lam u) u b ∧
      IntegralForm (S.nu u) (S.rUV u) u b ∧
      IntegralForm (S.m u) (S.mV u) u b ∧
      IntegralForm (S.Q u) (S.QV e u) u b ∧
      IntegralForm (S.A u) (S.AV u) u b ∧
      IntegralForm (S.phi u) (S.phiV u) u b ∧
      IntegralForm (S.xi u) (S.xiV e u) u b) ∧
    (∀ a v, a ≤ v → inSeg a v v ⊆ origDomain ui →
      IntegralForm (fun u => S.r u v) (fun u => S.nu u v) a v ∧
      IntegralForm (fun u => S.lam u v) (fun u => S.rUV u v) a v ∧
      IntegralForm (fun u => S.m u v) (fun u => S.mU u v) a v ∧
      IntegralForm (fun u => S.Q u v) (fun u => S.QU e u v) a v ∧
      IntegralForm (fun u => S.phi u v) (fun u => S.phiU e u v) a v ∧
      IntegralForm (fun u => S.theta u v) (fun u => S.thetaU e u v) a v) :=
  ⟨fun _ _ hab hs => out_integralForm hS le_rfl hab hs,
    fun _ _ hab hs => in_integralForm hS hab le_rfl hs⟩

end EmcsfAcExtension.Global.Calculus
