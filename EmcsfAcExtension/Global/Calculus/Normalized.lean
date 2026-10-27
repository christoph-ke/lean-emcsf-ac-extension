module

public import EmcsfAcExtension.Global.Calculus.Sections
import EmcsfAcExtension.Local.Calculus.Sections
import EmcsfAcExtension.Local.Algebra.Normalized
import EmcsfAcExtension.Infra.AC.Quotient

/-! # Normalized characteristic transport in the original AC class

The quotient rules use the characteristic AC equations, without a classical
regularity assumption on the solution. The rational cancellations reuse
`Local.Algebra.Normalized` (`charged_SF_new_version.tex:L662–L677`, L4328–L4335).
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Calculus

/-- [internal] A nonvanishing AC function on a compact interval has an AC
reciprocal. The lower bound is local to this function and interval. -/
theorem ac_inv_of_ne_zero {K : Type*} [NormedDivisionRing K]
    {f : ℝ → K} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hne : ∀ x ∈ uIcc a b, f x ≠ 0) :
    AbsolutelyContinuousOnInterval (fun x => (f x)⁻¹) a b := by
  obtain ⟨x, hx, hmin⟩ := isCompact_uIcc.exists_isMinOn nonempty_uIcc hf.continuousOn.norm
  exact hf.inv_of_le_norm (norm_pos_iff.mpr (hne x hx)) hmin

/-- [internal] Nonvanishing denominators suffice for the AC quotient rule on a
compact characteristic interval; no terminal uniform lower bound is needed. -/
theorem ac_div_of_ne_zero {K : Type*} [NormedDivisionRing K]
    {f g : ℝ → K} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hne : ∀ x ∈ uIcc a b, g x ≠ 0) :
    AbsolutelyContinuousOnInterval (fun x => f x / g x) a b := by
  simpa only [div_eq_mul_inv] using hf.mul_normed_ring (ac_inv_of_ne_zero hg hne)

variable {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}

/-- [internal] The normalized outgoing scalar is jointly continuous in the
frozen class, since its expansion denominator is everywhere positive. -/
theorem continuousOn_a (hS : IsSolution e S D) :
    ContinuousOn (Function.uncurry S.a) D := by
  exact hS.cont_phi.add (hS.cont_theta.div
    (Complex.continuous_ofReal.comp_continuousOn hS.cont_lam)
    (fun p hp => Complex.ofReal_ne_zero.mpr (hS.lam_pos p hp).ne'))

/-- [node restart-eq-normalized]
Incoming normalized transport, with its literal ordinary a.e. derivative.
All regularity is obtained from `IsSolution` on this off-axis segment.
The connection term converts the covariant equation to an ordinary one. -/
theorem normalized_in_section (hS : IsSolution e S D) {a b v : ℝ}
    (hab : a ≤ b) (hbv : b < v) (hs : inSeg a b v ⊆ D) :
    AbsolutelyContinuousOnInterval (fun u => S.a u v) a b ∧
      ∀ᵐ u ∂volume.restrict (Icc a b),
        HasDerivAt (fun x => S.a x v)
          ((-(S.nu u v : ℂ) / S.r u v) *
            (((S.mu u v : ℂ) - S.Q u v ^ 2 / (S.r u v : ℂ) ^ 2) /
              (1 - S.mu u v) * (S.theta u v / S.lam u v) +
              I * e * S.Q u v * S.phi u v / (1 - S.mu u v)) -
            I * e * S.A u v * S.a u v) u := by
  have h := Local.IsSolution.in_section hS hab hbv hs
  have hl (x : ℝ) (hx : x ∈ Icc a b) :=
    (hS.lam_pos (x, v) (hs ⟨hx.1, hx.2, rfl⟩)).ne'
  refine ⟨?_, ?_⟩
  · simpa only [Fields.a] using! h.2.2.2.2.1.1.fun_add
      (ac_div_of_ne_zero h.2.2.2.2.2.1 h.2.1.1.ofReal
        (fun x hx => Complex.ofReal_ne_zero.mpr (hl x (by simpa [uIcc_of_le hab] using hx))))
  · filter_upwards [h.2.1.2, h.2.2.2.2.1.2, h.2.2.2.2.2.2,
      ae_restrict_mem measurableSet_Icc] with u hlu hpu htu hu
    have hp : (u, v) ∈ D := hs ⟨hu.1, hu.2, rfl⟩
    have hd := hpu.add (htu.div hlu.ofReal_comp (Complex.ofReal_ne_zero.mpr (hl u hu)))
    have halg := Local.eq_normalized_in_algebra
      (e := e) (A := S.A u v) (phi := S.phi u v)
      (theta := S.theta u v) (xi := S.xi u v)
      (hS.r_pos (u, v) hp (hu.2.trans_lt hbv)).ne' (hl u hu)
      (hS.one_sub_mu_pos (u, v) hp).ne'
      (show S.rUV u v = _ from rfl) (show S.phiU e u v = _ from rfl)
      (show S.thetaU e u v = _ from rfl)
    exact (show HasDerivAt (fun x => S.a x v) _ u from hd).congr_deriv
      (eq_sub_iff_add_eq.mpr halg)

/-- [node restart-eq-normalized]
Outgoing normalized transport, including outgoing AC of `β/ν` derived from the
equations. This does not assume outgoing differentiability of `λ` or `θ`. -/
theorem normalized_out_section (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    AbsolutelyContinuousOnInterval (S.b u) a b ∧
      ∀ᵐ v ∂volume.restrict (Icc a b),
        HasDerivAt (S.b u)
          ((-(S.lam u v : ℂ) / S.r u v) *
            (((S.mu u v : ℂ) - S.Q u v ^ 2 / (S.r u v : ℂ) ^ 2) /
              (1 - S.mu u v) * (S.xi u v / S.nu u v) -
              I * e * S.Q u v * S.phi u v / (1 - S.mu u v))) v := by
  have h := Local.IsSolution.out_section hS hua hab hs
  have hn (x : ℝ) (hx : x ∈ Icc a b) :=
    (hS.nu_neg (u, x) (hs ⟨rfl, hx.1, hx.2⟩)).ne
  refine ⟨?_, ?_⟩
  · simpa only [Fields.b] using! h.2.2.2.2.2.1.1.fun_add
      (ac_div_of_ne_zero h.2.2.2.2.2.2.1 h.2.1.1.ofReal
        (fun x hx => Complex.ofReal_ne_zero.mpr (hn x (by simpa [uIcc_of_le hab] using hx))))
  · filter_upwards [h.2.1.2, h.2.2.2.2.2.1.2, h.2.2.2.2.2.2.2,
      ae_restrict_mem measurableSet_Icc] with v hnv hpv hxv hv
    have hp : (u, v) ∈ D := hs ⟨rfl, hv.1, hv.2⟩
    have hd := hpv.add (hxv.div hnv.ofReal_comp (Complex.ofReal_ne_zero.mpr (hn v hv)))
    have halg := Local.eq_normalized_out_algebra
      (e := e) (phi := S.phi u v) (theta := S.theta u v) (xi := S.xi u v)
      (hS.r_pos (u, v) hp (hua.trans_le hv.1)).ne' (hn v hv)
      (hS.one_sub_mu_pos (u, v) hp).ne'
      (show S.rUV u v = _ from rfl) (show S.phiV u v = _ from rfl)
      (show S.xiV e u v = _ from rfl)
    exact (show HasDerivAt (S.b u) _ v from hd).congr_deriv halg

/-- [node sec:charged-equations#constant-label-connector-calculus]
On a constant incoming-label connector, the normalized incoming equation
holds in integral form. Its source is integrable by the AC equation itself;
no trace of an arbitrary product-a.e. density is taken. -/
theorem constant_label_connector_calculus (hS : IsSolution e S D) {a b v : ℝ}
    (hab : a ≤ b) (hbv : b < v) (hs : inSeg a b v ⊆ D) :
    IntegralForm (fun u => S.a u v)
      (fun u => (-(S.nu u v : ℂ) / S.r u v) *
        (((S.mu u v : ℂ) - S.Q u v ^ 2 / (S.r u v : ℂ) ^ 2) /
          (1 - S.mu u v) * (S.theta u v / S.lam u v) +
          I * e * S.Q u v * S.phi u v / (1 - S.mu u v)) -
        I * e * S.A u v * S.a u v) a b := by
  have h := normalized_in_section hS hab hbv hs
  exact integralForm_of_ac_of_ae_deriv_eq h.1 (by
    rw [uIcc_of_le hab]
    exact h.2.mono fun _ hx => hx.deriv)

/-- [node restart-eq-normalized]
The outgoing normalized equation in integral form on a proper row. -/
theorem normalized_out_integralForm (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    IntegralForm (S.b u)
      (fun v => (-(S.lam u v : ℂ) / S.r u v) *
        (((S.mu u v : ℂ) - S.Q u v ^ 2 / (S.r u v : ℂ) ^ 2) /
          (1 - S.mu u v) * (S.xi u v / S.nu u v) -
          I * e * S.Q u v * S.phi u v / (1 - S.mu u v))) a b := by
  have h := normalized_out_section hS hua hab hs
  exact integralForm_of_ac_of_ae_deriv_eq h.1 (by
    rw [uIcc_of_le hab]
    exact h.2.mono fun _ hx => hx.deriv)

end EmcsfAcExtension.Global.Calculus
