module

public import EmcsfAcExtension.Global.Interaction.BoundaryCharge
import EmcsfAcExtension.Global.Terminal.Scalar
import EmcsfAcExtension.Local.Calculus.RelativeCharge
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Global.Calculus.Sections

/-! # The two core scalar comparison inequalities

The weighted Cauchy–Schwarz factors in `charged_SF_new_version.tex:L3325–L3333`
are retained before replacing them by the mass and gap bounds. The
stopped-profile consumer discharges the boundary scalar premise.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Interaction

/-- [internal] The full core scalar comparison chain. The exact coefficient
is `2 / δ`, uniform in the solution and coupling. The consumer supplies the
boundary scalar bound from the exterior envelope. -/
theorem core_scalar_growth_chain_of_boundary_bound {e δ M₀ : ℝ} {S : Fields}
    {D : Set (ℝ × ℝ)} (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u u b ⊆ D) (hδ : 0 < δ)
    (hgap : ∀ v ∈ Icc u b, δ ≤ 1 - S.mu u v) (hM : ‖S.phi u b‖ ≤ M₀) :
    ‖S.phi u a‖ ≤ ‖S.phi u b‖ +
        Real.sqrt (∫ v in a..b, S.lam u v * (1 - S.mu u v) *
          ‖S.theta u v / S.lam u v‖ ^ 2) *
        Real.sqrt (∫ v in a..b, S.lam u v / ((1 - S.mu u v) * S.r u v ^ 2)) ∧
      ‖S.phi u b‖ +
        Real.sqrt (∫ v in a..b, S.lam u v * (1 - S.mu u v) *
          ‖S.theta u v / S.lam u v‖ ^ 2) *
        Real.sqrt (∫ v in a..b, S.lam u v / ((1 - S.mu u v) * S.r u v ^ 2)) ≤
      M₀ + Real.sqrt (2 * S.m u b / (δ * S.r u a)) := by
  have hub := hua.trans_le hab
  have hsa : outSeg u a b ⊆ D := fun p hp => hs ⟨hp.1, hua.le.trans hp.2.1, hp.2.2⟩
  have hp (v : ℝ) (hv : v ∈ Icc a b) : (u, v) ∈ D := hsa ⟨rfl, hv⟩
  have hr (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.r u v :=
    hS.r_pos (u, v) (hp v hv) (hua.trans_le hv.1)
  have hl (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.lam u v := hS.lam_pos (u, v) (hp v hv)
  have hg (v : ℝ) (hv : v ∈ Icc a b) : 0 < 1 - S.mu u v :=
    hδ.trans_le (hgap v ⟨hua.le.trans hv.1, hv.2⟩)
  have cr := Calculus.continuousOn_out_section hS.cont_r hsa
  have cl := Calculus.continuousOn_out_section hS.cont_lam hsa
  have ct := Calculus.continuousOn_out_section hS.cont_theta hsa
  have cmu := Local.continuousOn_mu_out hS hub hs
  have cg : ContinuousOn (fun v => 1 - S.mu u v) (Icc a b) :=
    continuousOn_const.sub (cmu.mono (Icc_subset_Icc hua.le le_rfl))
  have cy := ct.div (continuous_ofReal.comp_continuousOn cl)
    (fun v hv => Complex.ofReal_ne_zero.mpr (hl v hv).ne')
  let f := fun v => Real.sqrt (S.lam u v) * Real.sqrt (1 - S.mu u v) *
    ‖S.theta u v / S.lam u v‖
  let g := fun v => Real.sqrt (S.lam u v) / Real.sqrt (1 - S.mu u v) / S.r u v
  have cf : ContinuousOn f (Icc a b) := (cl.sqrt.mul cg.sqrt).mul cy.norm
  have cgg : ContinuousOn g (Icc a b) :=
    (cl.sqrt.div cg.sqrt (fun v hv => (Real.sqrt_pos.mpr (hg v hv)).ne')).div cr
      (fun v hv => (hr v hv).ne')
  have fsq (v : ℝ) (hv : v ∈ Icc a b) : f v ^ 2 =
      S.lam u v * (1 - S.mu u v) * ‖S.theta u v / S.lam u v‖ ^ 2 := by
    dsimp [f]
    rw [mul_pow, mul_pow, Real.sq_sqrt (hl v hv).le, Real.sq_sqrt (hg v hv).le]
  have gsq (v : ℝ) (hv : v ∈ Icc a b) : g v ^ 2 =
      S.lam u v / ((1 - S.mu u v) * S.r u v ^ 2) := by
    dsimp [g]
    rw [div_pow, div_pow, Real.sq_sqrt (hl v hv).le, Real.sq_sqrt (hg v hv).le, div_div]
  have fg (v : ℝ) (hv : v ∈ Icc a b) : f v * g v = ‖S.phiV u v‖ := by
    have hgs := (Real.sqrt_pos.mpr (hg v hv)).ne'
    have he : f v * g v = Real.sqrt (S.lam u v) ^ 2 / S.r u v *
        ‖S.theta u v / S.lam u v‖ := by dsimp [f, g]; field_simp [hgs]
    rw [he, Real.sq_sqrt (hl v hv).le]
    simp only [Fields.phiV, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hl v hv), abs_of_pos (hr v hv)]
    field_simp [(hl v hv).ne', (hr v hv).ne']
  have hcs := Terminal.integral_cauchy_schwarz hab cf cgg
  rw [intervalIntegral.integral_congr (fun v hv => fg v ((uIcc_of_le hab) ▸ hv)),
    intervalIntegral.integral_congr (fun v hv => fsq v ((uIcc_of_le hab) ▸ hv)),
    intervalIntegral.integral_congr (fun v hv => gsq v ((uIcc_of_le hab) ▸ hv))] at hcs
  have forms := hS.eq_out u a b hua hab hsa
  have hnorm : ‖S.phi u a - S.phi u b‖ ≤ ∫ v in a..b, ‖S.phiV u v‖ := by
    rw [norm_sub_rev, forms.2.2.2.2.2.1.2]
    exact intervalIntegral.norm_integral_le_integral_norm hab
  have hdiff := (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hcs
  have clcore := Calculus.continuousOn_out_section hS.cont_lam hs
  have ctcore := Calculus.continuousOn_out_section hS.cont_theta hs
  have cycore := ctcore.div (continuous_ofReal.comp_continuousOn clcore)
    (fun v hv => Complex.ofReal_ne_zero.mpr (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).ne')
  have cgcore : ContinuousOn (fun v => 1 - S.mu u v) (Icc u b) := continuousOn_const.sub cmu
  have iE := ((clcore.mul cgcore).mul (cycore.norm.pow 2))
    |>.intervalIntegrable_of_Icc hub.le (μ := volume)
  have iEa := iE.mono_set (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc ⟨hua.le, hab⟩))
  have iEb := iE.mono_set (uIcc_subset_uIcc (Icc_subset_uIcc ⟨hua.le, hab⟩) right_mem_uIcc)
  have hEn := intervalIntegral.integral_nonneg hua.le (μ := volume) (fun v hv =>
    mul_nonneg (mul_nonneg (hS.lam_pos (u, v) (hs ⟨rfl, hv.1, hv.2.trans hab⟩)).le
      (hS.one_sub_mu_pos (u, v) (hs ⟨rfl, hv.1, hv.2.trans hab⟩)).le)
        (sq_nonneg ‖S.theta u v / S.lam u v‖))
  have hsum := intervalIntegral.integral_add_adjacent_intervals iEa iEb
  have hmass := Local.RelCharge.mass_controls_radial_flux hS hub hs
  dsimp only [Pi.mul_apply, Pi.pow_apply, Pi.div_apply, Function.comp_def] at iE hsum
  have hE : (∫ v in a..b, S.lam u v * (1 - S.mu u v) *
      ‖S.theta u v / S.lam u v‖ ^ 2) ≤ 2 * S.m u b := by linarith only [hmass, hsum, hEn]
  have cW : ContinuousOn (fun v => S.lam u v / ((1 - S.mu u v) * S.r u v ^ 2)) (Icc a b) :=
    cl.div (cg.mul (cr.pow 2)) (fun v hv => mul_ne_zero (hg v hv).ne' (pow_ne_zero _ (hr v hv).ne'))
  have iW := cW.intervalIntegrable_of_Icc hab (μ := volume)
  have iW' := ((cl.div (cr.pow 2) (fun v hv => pow_ne_zero _ (hr v hv).ne')).div
    continuousOn_const (fun _ _ => hδ.ne')).intervalIntegrable_of_Icc hab (μ := volume)
  have hW := intervalIntegral.integral_mono_on hab iW iW' (fun v hv => by
    rw [← div_div, div_right_comm]
    exact div_le_div_of_nonneg_left (div_nonneg (hl v hv).le (sq_nonneg _))
      hδ (hgap v ⟨hua.le.trans hv.1, hv.2⟩))
  have ik := (cl.div (cr.pow 2) (fun v hv => pow_ne_zero _ (hr v hv).ne'))
    |>.intervalIntegrable_of_Icc hab (μ := volume)
  have hkernel : (∫ v in a..b, S.lam u v / S.r u v ^ 2) =
      1 / S.r u a - 1 / S.r u b := by
    have hc : ContinuousOn (fun v => -(S.r u v)⁻¹) (Icc a b) :=
      (cr.inv₀ (fun v hv => (hr v hv).ne')).neg
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc
      (f' := fun v => S.lam u v / S.r u v ^ 2) (fun v hv => ?_) ik
    · simpa only [one_div, neg_sub_neg] using hftc
    · have hd := (Local.IsSolution.hasDerivAt_radius_out hS hs ⟨hua.trans hv.1, hv.2⟩).inv
        (hr v ⟨hv.1.le, hv.2.le⟩).ne'
      simpa only [Pi.inv_apply, Pi.neg_apply, neg_div, neg_neg] using! hd.neg
  dsimp only [Pi.div_apply] at hW
  rw [intervalIntegral.integral_div] at hW
  simp only [Pi.pow_apply] at hW
  rw [hkernel] at hW
  have hW' : (∫ v in a..b, S.lam u v / ((1 - S.mu u v) * S.r u v ^ 2)) ≤
      1 / (δ * S.r u a) := by
    calc
      _ ≤ _ := hW
      _ ≤ (1 / S.r u a) / δ := div_le_div_of_nonneg_right
        (sub_le_self _ (one_div_nonneg.mpr (hr b ⟨hab, le_rfl⟩).le)) hδ.le
      _ = _ := by ring
  have hW0 := intervalIntegral.integral_nonneg (μ := volume) hab (fun v hv =>
    div_nonneg (hl v hv).le (mul_nonneg (hg v hv).le (sq_nonneg (S.r u v))))
  have hE0 := intervalIntegral.integral_nonneg (μ := volume) hab (fun v hv =>
    mul_nonneg (mul_nonneg (hl v hv).le (hg v hv).le) (sq_nonneg ‖S.theta u v / S.lam u v‖))
  have hprod :
      (∫ v in a..b, S.lam u v * (1 - S.mu u v) * ‖S.theta u v / S.lam u v‖ ^ 2) *
        (∫ v in a..b, S.lam u v / ((1 - S.mu u v) * S.r u v ^ 2)) ≤
      2 * S.m u b / (δ * S.r u a) := by
    calc
      _ ≤ (2 * S.m u b) * (1 / (δ * S.r u a)) :=
        mul_le_mul hE hW' hW0 (hE0.trans hE)
      _ = _ := by ring
  constructor
  · have hroot := Real.le_sqrt_of_sq_le hdiff
    rw [Real.sqrt_mul hE0] at hroot
    exact (norm_le_norm_add_norm_sub' (S.phi u a) (S.phi u b)).trans
      (add_le_add le_rfl hroot)
  · apply add_le_add hM
    rw [← Real.sqrt_mul hE0]
    exact Real.sqrt_le_sqrt hprod

end EmcsfAcExtension.Global.Interaction
