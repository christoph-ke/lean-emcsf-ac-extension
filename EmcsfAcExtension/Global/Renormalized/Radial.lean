module

public import EmcsfAcExtension.Global.Defs.Renormalized
public import EmcsfAcExtension.Global.Calculus.Normalized
import EmcsfAcExtension.Local.Calculus.Sections
import EmcsfAcExtension.Local.Algebra.Radial
import EmcsfAcExtension.Infra.AC.Quotient

/-! # The renormalized radial system in the AC class

The four radial identities of `charged_SF_new_version.tex:L3188–L3201`, interpreted as
outgoing AC identities with `D_r = λ⁻¹ D_v`. The rough outgoing ratio is
`a - φ`; no outgoing derivative of `λ` or `θ` is used.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Renormalized

/-- [def-node eq:ct-j]
The frozen outgoing derivative is the source's normalized derivative with
its cubic correction (`charged_SF_new_version.tex:L3134–L3137`). -/
theorem jOut_eq (S : Fields) (u v : ℝ) (hl : S.lam u v ≠ 0) :
    jOut S u v = (1 - S.mu u v) * S.lam u v *
      (alphaPrime S u v - (‖S.theta u v / S.lam u v‖ ^ 2 : ℂ) /
        S.r u v * (S.theta u v / S.lam u v)) := by
  unfold jOut alphaPrime
  field_simp [Complex.ofReal_ne_zero.mpr hl]

/-- [def-node eq:ct-C]
The shared complex curvature is exactly the normalized source object,
including its imaginary part (`charged_SF_new_version.tex:L3138–L3139`). -/
theorem curv_eq (S : Fields) (u v : ℝ) :
    Local.curv S u v = S.mu u v + (1 - S.mu u v) *
      (S.theta u v / S.lam u v) * starRingEnd ℂ (S.xi u v / S.nu u v) := by
  simp only [Local.curv, map_div₀, Complex.conj_ofReal]
  ring

/-- [def-node eq:ct-Ej]
The shared electromagnetic remainder uses the frozen outgoing Maxwell
right side `QV` for `Q_v` (`charged_SF_new_version.tex:L3178–L3183`). -/
theorem emSourceJ_eq (e : ℝ) (S : Fields) (u v : ℝ) :
    Local.emSourceJ e S u v =
      (-S.nu u v) * S.lam u v / S.r u v ^ 2 *
        (5 * (S.Q u v ^ 2 / S.r u v ^ 2) * (S.theta u v / S.lam u v) +
          I * e * S.Q u v * (3 * (S.theta u v / S.lam u v) + S.phi u v)) +
      I * e * (-S.nu u v) * S.QV e u v * S.phi u v / S.r u v := rfl

variable {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}

/-- [node lem:ct-renormalized#radial-system]
Outgoing AC and the radial equation for `θ/λ`. The displayed derivative is
`λ D_r(θ/λ)`; the frozen derivative `jOut` is only used a.e. -/
theorem radial_out_section (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    AbsolutelyContinuousOnInterval (fun v => S.theta u v / S.lam u v) a b ∧
    ∀ᵐ v ∂volume.restrict (Icc a b), HasDerivAt
      (fun t => S.theta u t / S.lam u t)
      (S.lam u v * (jOut S u v / ((1 - S.mu u v) * S.lam u v) -
        (1 - ‖S.theta u v / S.lam u v‖ ^ 2 : ℝ) / S.r u v *
          (S.theta u v / S.lam u v))) v := by
  have h := Local.IsSolution.out_section hS hua hab hs
  have ha := (hS.ac_out u a b hab hs).2.2.2.2
  have hy : (fun v => S.theta u v / S.lam u v) =
      (fun v => S.a u v - S.phi u v) := by
    funext v
    simp [Fields.a]
  refine ⟨by rw [hy]; exact ha.sub h.2.2.2.2.2.1.1, ?_⟩
  have had := (ae_restrict_iff' measurableSet_Icc).2 (by
    simpa only [uIcc_of_le hab] using ha.ae_differentiableAt_of_mem_uIcc)
  filter_upwards [had, h.2.2.2.2.2.1.2, ae_restrict_mem measurableSet_Icc]
    with v hav hpv hv
  have hp : (u, v) ∈ D := hs ⟨rfl, hv.1, hv.2⟩
  have hr := (hS.r_pos (u, v) hp (hua.trans_le hv.1)).ne'
  have hl := (hS.lam_pos (u, v) hp).ne'
  have hg := (hS.one_sub_mu_pos (u, v) hp).ne'
  have halg := Local.radial_theta_div_lam_algebra
    (theta := S.theta u v) (phiV := S.phiV u v)
    (ratioV := deriv (S.a u) v - S.phiV u v) (j := jOut S u v)
    hr hl hg rfl (by unfold jOut; push_cast; ring)
  rw [hy]
  apply (hav.hasDerivAt.sub hpv).congr_deriv
  simpa only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow, mul_comm] using
    (div_eq_iff (Complex.ofReal_ne_zero.mpr hl)).mp halg

/-- [node lem:ct-renormalized#radial-system]
The incoming scalar ratio is AC along each outgoing section. Its derivative
is `λ D_r(ξ/ν)`, with the charged term retained. -/
theorem radial_in_section (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    AbsolutelyContinuousOnInterval (fun v => S.xi u v / S.nu u v) a b ∧
    ∀ᵐ v ∂volume.restrict (Icc a b), HasDerivAt
      (fun t => S.xi u t / S.nu u t)
      (S.lam u v * (-(S.theta u v / S.lam u v) / S.r u v -
        ((S.mu u v : ℂ) - S.Q u v ^ 2 / (S.r u v : ℂ) ^ 2) /
          ((1 - S.mu u v) * S.r u v) * (S.xi u v / S.nu u v) +
        I * e * S.Q u v * S.phi u v / ((1 - S.mu u v) * S.r u v))) v := by
  have h := Local.IsSolution.out_section hS hua hab hs
  have hn (v : ℝ) (hv : v ∈ Icc a b) :=
    (hS.nu_neg (u, v) (hs ⟨rfl, hv.1, hv.2⟩)).ne
  refine ⟨Calculus.ac_div_of_ne_zero h.2.2.2.2.2.2.1 h.2.1.1.ofReal
    (fun v hv => Complex.ofReal_ne_zero.mpr (hn v (by
      simpa [uIcc_of_le hab] using hv))), ?_⟩
  filter_upwards [h.2.1.2, h.2.2.2.2.2.2.2, ae_restrict_mem measurableSet_Icc]
    with v hnv hxv hv
  have hp : (u, v) ∈ D := hs ⟨rfl, hv.1, hv.2⟩
  have hl := (hS.lam_pos (u, v) hp).ne'
  have halg := Local.radial_xi_div_nu_algebra (xi := S.xi u v)
    (hS.r_pos (u, v) hp (hua.trans_le hv.1)).ne' hl (hn v hv)
    (hS.one_sub_mu_pos (u, v) hp).ne'
    (show S.rUV u v = _ from rfl) (show S.xiV e u v = _ from rfl)
  apply (hxv.div hnv.ofReal_comp (Complex.ofReal_ne_zero.mpr (hn v hv))).congr_deriv
  simpa only [mul_comm] using (div_eq_iff (Complex.ofReal_ne_zero.mpr hl)).mp halg

/-- [node lem:ct-renormalized#radial-system]
The radial ordinary-mass equation, as outgoing AC and its derivative.
The derivative is `λ μ_r`; no charge-adjusted mass is used. -/
theorem radial_mu_section (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    AbsolutelyContinuousOnInterval (S.mu u) a b ∧
    ∀ᵐ v ∂volume.restrict (Icc a b), HasDerivAt (S.mu u)
      (S.lam u v / S.r u v * ((1 - S.mu u v) *
        ‖S.theta u v / S.lam u v‖ ^ 2 + S.Q u v ^ 2 / S.r u v ^ 2 - S.mu u v)) v := by
  have h := Local.IsSolution.out_section hS hua hab hs
  have hr (v : ℝ) (hv : v ∈ Icc a b) :=
    (hS.r_pos (u, v) (hs ⟨rfl, hv.1, hv.2⟩) (hua.trans_le hv.1)).ne'
  refine ⟨Calculus.ac_div_of_ne_zero (h.2.2.1.1.const_mul 2) h.1.1
    (fun v hv => hr v (by simpa [uIcc_of_le hab] using hv)), ?_⟩
  filter_upwards [h.1.2, h.2.2.1.2, ae_restrict_mem measurableSet_Icc]
    with v hrv hmv hv
  apply ((hmv.const_mul 2).div hrv (hr v hv)).congr_deriv
  calc
    _ = 2 * S.mV u v / S.r u v - 2 * S.m u v * S.lam u v / S.r u v ^ 2 := by
      field_simp [hr v hv]
    _ = _ := Local.Stab.outgoing_mu_derivative_identity_algebra (hr v hv)
      (hS.lam_pos (u, v) (hs ⟨rfl, hv.1, hv.2⟩)).ne' rfl

/-- [node lem:ct-renormalized#radial-system]
The radial expansion identity, as outgoing AC of `log(-ν)` and its
specified derivative `λ (log(-ν))_r`. -/
theorem radial_log_neg_nu_section (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    AbsolutelyContinuousOnInterval (fun v => Real.log (-S.nu u v)) a b ∧
    ∀ᵐ v ∂volume.restrict (Icc a b), HasDerivAt
      (fun t => Real.log (-S.nu u t))
      (S.lam u v * ((S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) /
        ((1 - S.mu u v) * S.r u v))) v := by
  have h := Local.IsSolution.out_section hS hua hab hs
  have hn (v : ℝ) (hv : v ∈ uIcc a b) : 0 < -S.nu u v :=
    neg_pos.mpr (hS.nu_neg (u, v) (hs ⟨rfl, by
      simpa [uIcc_of_le hab] using hv⟩))
  obtain ⟨x, hx, hm⟩ := isCompact_uIcc.exists_isMinOn nonempty_uIcc h.2.1.1.neg.continuousOn
  refine ⟨h.2.1.1.neg.log_of_pos_le (hn x hx) hm, ?_⟩
  filter_upwards [h.2.1.2, ae_restrict_mem measurableSet_Icc] with v hnv hv
  have hp : (u, v) ∈ D := hs ⟨rfl, hv.1, hv.2⟩
  have hl := (hS.lam_pos (u, v) hp).ne'
  have hn' := (hS.nu_neg (u, v) hp).ne
  have halg := Local.radial_log_neg_nu_algebra
    (hS.r_pos (u, v) hp (hua.trans_le hv.1)).ne' hl hn'
    (hS.one_sub_mu_pos (u, v) hp).ne' (show S.rUV u v = _ from rfl)
  apply (hnv.neg.log (neg_ne_zero.mpr hn')).congr_deriv
  change -S.rUV u v / -S.nu u v = _
  rw [neg_div_neg_eq]
  apply (div_eq_iff hn').2
  simpa only [mul_comm, mul_left_comm, mul_assoc] using
    (div_eq_iff (mul_ne_zero hn' hl)).mp halg

/-- [node lem:ct-renormalized#radial-system]
The complete four-equation radial system on a proper outgoing section.
Every displayed outgoing speed is `λ D_r` of the named quantity. AC and
a.e. identities are proved directly from the frozen characteristic class;
there are no additional regularity or smallness hypotheses. -/
theorem radial_system (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    (AbsolutelyContinuousOnInterval (fun v => S.theta u v / S.lam u v) a b ∧
    ∀ᵐ v ∂volume.restrict (Icc a b), HasDerivAt
      (fun t => S.theta u t / S.lam u t)
      (S.lam u v * (jOut S u v / ((1 - S.mu u v) * S.lam u v) -
        (1 - ‖S.theta u v / S.lam u v‖ ^ 2 : ℝ) / S.r u v *
          (S.theta u v / S.lam u v))) v) ∧
    (AbsolutelyContinuousOnInterval (fun v => S.xi u v / S.nu u v) a b ∧
    ∀ᵐ v ∂volume.restrict (Icc a b), HasDerivAt
      (fun t => S.xi u t / S.nu u t)
      (S.lam u v * (-(S.theta u v / S.lam u v) / S.r u v -
        ((S.mu u v : ℂ) - S.Q u v ^ 2 / (S.r u v : ℂ) ^ 2) /
          ((1 - S.mu u v) * S.r u v) * (S.xi u v / S.nu u v) +
        I * e * S.Q u v * S.phi u v / ((1 - S.mu u v) * S.r u v))) v) ∧
    (AbsolutelyContinuousOnInterval (S.mu u) a b ∧
    ∀ᵐ v ∂volume.restrict (Icc a b), HasDerivAt (S.mu u)
      (S.lam u v / S.r u v * ((1 - S.mu u v) *
        ‖S.theta u v / S.lam u v‖ ^ 2 + S.Q u v ^ 2 / S.r u v ^ 2 - S.mu u v)) v) ∧
    (AbsolutelyContinuousOnInterval (fun v => Real.log (-S.nu u v)) a b ∧
    ∀ᵐ v ∂volume.restrict (Icc a b), HasDerivAt
      (fun t => Real.log (-S.nu u t))
      (S.lam u v * ((S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) /
        ((1 - S.mu u v) * S.r u v))) v) :=
  ⟨radial_out_section hS hua hab hs, radial_in_section hS hua hab hs,
    radial_mu_section hS hua hab hs, radial_log_neg_nu_section hS hua hab hs⟩

end EmcsfAcExtension.Global.Renormalized
