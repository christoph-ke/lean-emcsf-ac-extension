module

public import EmcsfAcExtension.Global.Renormalized.Incoming
public import EmcsfAcExtension.Global.Renormalized.Radial
import EmcsfAcExtension.Local.Algebra.Curvature
import EmcsfAcExtension.Local.Calculus.Sections
import EmcsfAcExtension.Infra.AC.Quotient

/-! # Outgoing transport of the full complex curvature

The curvature primitive is AC on proper outgoing sections. The cancellation
is the landed curvature algebra, applied to normalized jets: it does not
require separate outgoing derivatives of `θ` and `λ`.
Source: `charged_SF_new_version.tex:L3166–L3169`, L3202–L3210; internal project record.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Renormalized

private theorem normalized_curvature_algebra
    (r lam nu mu Q e : ℝ) (y z phi yV : ℂ)
    (hr : r ≠ 0) (hl : lam ≠ 0) (hn : nu ≠ 0) (hg : 1 - mu ≠ 0) :
    let R : ℂ := r
    let L : ℂ := lam
    let H : ℂ := 1 - mu
    let Mv : ℂ := lam / r * ((1 - mu) * ‖y‖ ^ 2 + Q ^ 2 / r ^ 2 - mu)
    let zV := L * (-y / R - ((mu : ℂ) - Q ^ 2 / R ^ 2) / (H * R) * z +
      I * e * Q * phi / (H * R))
    L * ((mu : ℂ) + H * y * starRingEnd ℂ z) +
      R * (Mv - Mv * y * starRingEnd ℂ z + H * yV * starRingEnd ℂ z +
        H * y * starRingEnd ℂ zV) =
      R * starRingEnd ℂ z * (H * (yV + L / R * y - L / R * (‖y‖ : ℂ) ^ 2 * y)) +
        L * Q ^ 2 / R ^ 2 - I * e * Q * (L * y) * starRingEnd ℂ phi := by
  have hr' := Complex.ofReal_ne_zero.mpr hr
  have hl' := Complex.ofReal_ne_zero.mpr hl
  have hn' := Complex.ofReal_ne_zero.mpr hn
  have hg' : 1 - (mu : ℂ) ≠ 0 := by exact_mod_cast hg
  have h := Local.bv_c_v_algebra (r : ℂ) (lam : ℂ) (nu : ℂ) (mu : ℂ) (Q : ℂ)
    (I * e) ((lam : ℂ) * y) ((lam : ℂ) * starRingEnd ℂ y)
    ((nu : ℂ) * starRingEnd ℂ z) (starRingEnd ℂ phi) ((lam : ℂ) * yV) 0
    hr' hl' hn' hg'
  dsimp only at h ⊢
  simp only [map_mul, map_add, map_sub, map_neg, map_div₀, map_pow,
    Complex.conj_ofReal, Complex.conj_I, map_one] at h ⊢
  simp only [← Complex.conj_mul'] at h ⊢
  convert h using 1 <;> (field_simp [hr', hl', hn', hg']; ring)

variable {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}

/-- [node lem:ct-renormalized#radial-curvature-cancellation]
[node eq:ct-C-trans]
The full complex curvature primitive is AC and satisfies its exact outgoing
transport a.e. on every proper outgoing segment. Dividing the displayed
speed by `λ` gives the radial identity, since `D_r = λ⁻¹ D_v`.
Only the frozen AC class is assumed. -/
theorem curvature_out_section (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    AbsolutelyContinuousOnInterval (fun v => (S.r u v : ℂ) * Local.curv S u v) a b ∧
    ∀ᵐ v ∂volume.restrict (Icc a b), HasDerivAt
      (fun t => (S.r u t : ℂ) * Local.curv S u t)
      (S.r u v * starRingEnd ℂ (S.xi u v / S.nu u v) * jOut S u v +
        (S.lam u v * S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) -
        I * e * S.Q u v * S.theta u v * starRingEnd ℂ (S.phi u v)) v := by
  have h := Local.IsSolution.out_section hS hua hab hs
  have hy := radial_out_section hS hua hab hs
  have hz := radial_in_section hS hua hab hs
  have hm := radial_mu_section hS hua hab hs
  have hc : (fun v => (S.r u v : ℂ) * Local.curv S u v) =
      (fun v => (S.r u v : ℂ) * ((S.mu u v : ℂ) + (1 - S.mu u v) *
        (S.theta u v / S.lam u v) * starRingEnd ℂ (S.xi u v / S.nu u v))) := by
    funext v
    rw [curv_eq]
  rw [hc]
  have hg := ((LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval.sub
    hm.1).ofReal
  refine ⟨?_, ?_⟩
  · simpa only [Pi.sub_apply, Complex.ofReal_sub, Complex.ofReal_one] using!
      h.1.1.ofReal.mul_normed_ring (hm.1.ofReal.fun_add
        ((hg.mul_normed_ring hy.1).mul_normed_ring (ac_conj hz.1)))
  filter_upwards [h.1.2, hy.2, hz.2, hm.2, ae_restrict_mem measurableSet_Icc]
    with v hrv hyv hzv hmv hv
  have hp : (u, v) ∈ D := hs ⟨rfl, hv.1, hv.2⟩
  have hr := (hS.r_pos (u, v) hp (hua.trans_le hv.1)).ne'
  have hl := (hS.lam_pos (u, v) hp).ne'
  have hn := (hS.nu_neg (u, v) hp).ne
  have hgap := (hS.one_sub_mu_pos (u, v) hp).ne'
  have hd := hrv.ofReal_comp.mul (hmv.ofReal_comp.add
    (((hasDerivAt_const v (1 : ℂ)).sub hmv.ofReal_comp).mul hyv |>.mul (hasDerivAt_conj hzv)))
  apply hd.congr_deriv
  simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, zero_sub]
  have halg := normalized_curvature_algebra
    (S.r u v) (S.lam u v) (S.nu u v) (S.mu u v) (S.Q u v) e
    (S.theta u v / S.lam u v) (S.xi u v / S.nu u v) (S.phi u v)
    (S.lam u v * (jOut S u v / ((1 - S.mu u v) * S.lam u v) -
      (1 - ‖S.theta u v / S.lam u v‖ ^ 2 : ℝ) / S.r u v *
        (S.theta u v / S.lam u v))) hr hl hn hgap
  dsimp only at halg
  have hj : (1 - (S.mu u v : ℂ)) *
      (S.lam u v * (jOut S u v / ((1 - S.mu u v) * S.lam u v) -
        (1 - ‖S.theta u v / S.lam u v‖ ^ 2 : ℝ) / S.r u v *
          (S.theta u v / S.lam u v)) +
        (S.lam u v : ℂ) / S.r u v * (S.theta u v / S.lam u v) -
        (S.lam u v : ℂ) / S.r u v * (‖S.theta u v / S.lam u v‖ : ℂ) ^ 2 *
          (S.theta u v / S.lam u v)) = jOut S u v := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hl,
      show 1 - (S.mu u v : ℂ) ≠ 0 from by exact_mod_cast hgap]
    ring
  rw [hj] at halg
  convert halg using 1 <;> (push_cast; field_simp [Complex.ofReal_ne_zero.mpr hl])
  ring

/-- [node lem:ct-renormalized#radial-curvature-cancellation]
The radial curvature cancellation with `D_r = λ⁻¹ D_v`. The primitive is
AC, and its normalized derivative retains the full complex source and the
electric current on every proper outgoing section. -/
theorem radial_curvature_cancellation (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    AbsolutelyContinuousOnInterval (fun v => (S.r u v : ℂ) * Local.curv S u v) a b ∧
    ∀ᵐ v ∂volume.restrict (Icc a b),
      deriv (fun t => (S.r u t : ℂ) * Local.curv S u t) v / S.lam u v =
        S.r u v * starRingEnd ℂ (S.xi u v / S.nu u v) * jOut S u v / S.lam u v +
          (S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) -
          I * e * S.Q u v * (S.theta u v / S.lam u v) * starRingEnd ℂ (S.phi u v) := by
  have h := curvature_out_section hS hua hab hs
  refine ⟨h.1, ?_⟩
  filter_upwards [h.2, ae_restrict_mem measurableSet_Icc] with v hv hvm
  rw [hv.deriv]
  have hl := (hS.lam_pos (u, v) (hs ⟨rfl, hvm.1, hvm.2⟩)).ne'
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hl]

/-- [node eq:ct-C-trans]
The curvature transport holds in integral form to both endpoints of every
proper outgoing segment; source integrability follows from AC. -/
theorem curvature_out_integralForm (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    IntegralForm (fun v => (S.r u v : ℂ) * Local.curv S u v)
      (fun v => S.r u v * starRingEnd ℂ (S.xi u v / S.nu u v) * jOut S u v +
        (S.lam u v * S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) -
        I * e * S.Q u v * S.theta u v * starRingEnd ℂ (S.phi u v)) a b := by
  have h := curvature_out_section hS hua hab hs
  exact integralForm_of_ac_of_ae_deriv_eq h.1 (by
    rw [uIcc_of_le hab]
    exact h.2.mono fun _ hx => hx.deriv)

end EmcsfAcExtension.Global.Renormalized

namespace EmcsfAcExtension.Global

variable {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}

/-- [node eq:ct-C-trans]
Canonical graph export of the outgoing AC transport of the full complex
curvature primitive, with its electromagnetic contribution retained. -/
theorem ct_c_trans (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    AbsolutelyContinuousOnInterval (fun v => (S.r u v : ℂ) * Local.curv S u v) a b ∧
    ∀ᵐ v ∂volume.restrict (Icc a b), HasDerivAt
      (fun t => (S.r u t : ℂ) * Local.curv S u t)
      (S.r u v * starRingEnd ℂ (S.xi u v / S.nu u v) * jOut S u v +
        (S.lam u v * S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) -
        I * e * S.Q u v * S.theta u v * starRingEnd ℂ (S.phi u v)) v :=
  Renormalized.curvature_out_section hS hua hab hs

end EmcsfAcExtension.Global
