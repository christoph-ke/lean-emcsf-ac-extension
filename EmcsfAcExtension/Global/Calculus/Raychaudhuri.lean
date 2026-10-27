module

public import EmcsfAcExtension.Global.Calculus.Normalized
import EmcsfAcExtension.Local.Calculus.Sections
import EmcsfAcExtension.Local.Algebra.Raychaudhuri
import EmcsfAcExtension.Infra.AC.Quotient

/-! # Logarithmic Raychaudhuri identities for AC solutions

The source identities at `charged_SF_new_version.tex:L655–L658` follow from the frozen
radius and mass integral equations. Only compact off-axis sections are used;
all denominator bounds are local. The algebra is the landed Root B algebra.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Global.Calculus

private theorem ac_log_of_pos {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hp : ∀ x ∈ uIcc a b, 0 < f x) :
    AbsolutelyContinuousOnInterval (fun x => Real.log (f x)) a b := by
  obtain ⟨x, hx, hm⟩ := isCompact_uIcc.exists_isMinOn nonempty_uIcc hf.continuousOn
  exact hf.log_of_pos_le (hp x hx) hm

private theorem log_div_derivative {f g : ℝ → ℝ} {f' g' x : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x)
    (hfn : f x ≠ 0) (hgn : g x ≠ 0) :
    HasDerivAt (fun y => Real.log (f y / g y)) (f' / f x - g' / g x) x := by
  have hd : HasDerivAt (fun y => Real.log (f y / g y))
      (((f' * g x - f x * g') / g x ^ 2) / (f x / g x)) x := by
    simpa only [Pi.div_apply] using! (hf.div hg hgn).log (div_ne_zero hfn hgn)
  apply hd.congr_deriv
  field_simp

variable {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}

/-- [node restart-eq-ray]
Incoming Raychaudhuri identity as an AC function and its a.e. derivative.
No constant or expansion bound uniform at a missing endpoint is assumed. -/
theorem raychaudhuri_in_section (hS : IsSolution e S D) {a b v : ℝ}
    (hab : a ≤ b) (hbv : b < v) (hs : inSeg a b v ⊆ D) :
    AbsolutelyContinuousOnInterval
      (fun u => Real.log (S.lam u v / (1 - S.mu u v))) a b ∧
      ∀ᵐ u ∂volume.restrict (Icc a b),
        HasDerivAt (fun x => Real.log (S.lam x v / (1 - S.mu x v)))
          (‖S.xi u v‖ ^ 2 / (S.nu u v * S.r u v)) u := by
  have h := Local.IsSolution.in_section hS hab hbv hs
  have mem (x : ℝ) (hx : x ∈ Icc a b) : (x, v) ∈ D := hs ⟨hx.1, hx.2, rfl⟩
  have hr (x : ℝ) (hx : x ∈ Icc a b) :=
    (hS.r_pos (x, v) (mem x hx) (hx.2.trans_lt hbv)).ne'
  have hacmu : AbsolutelyContinuousOnInterval (fun u => S.mu u v) a b :=
    ac_div_of_ne_zero (h.2.2.1.1.const_mul 2) h.1.1
      (fun x hx => hr x (by simpa [uIcc_of_le hab] using hx))
  have hacg : AbsolutelyContinuousOnInterval (fun u => 1 - S.mu u v) a b :=
    (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval.sub hacmu
  refine ⟨?_, ?_⟩
  · apply ac_log_of_pos (ac_div_of_ne_zero h.2.1.1 hacg ?_) ?_
    · intro x hx
      exact (hS.one_sub_mu_pos (x, v) (mem x (by simpa [uIcc_of_le hab] using hx))).ne'
    · intro x hx
      have hm := mem x (by simpa [uIcc_of_le hab] using hx)
      exact div_pos (hS.lam_pos (x, v) hm) (hS.one_sub_mu_pos (x, v) hm)
  · filter_upwards [h.1.2, h.2.1.2, h.2.2.1.2,
      ae_restrict_mem measurableSet_Icc] with u hru hlu hmu hu
    have hp := mem u hu
    have hmuder : HasDerivAt (fun x => S.mu x v)
        ((2 * S.mU u v * S.r u v - 2 * S.m u v * S.nu u v) / S.r u v ^ 2) u :=
      (hmu.const_mul 2).div hru (hr u hu)
    have hd := log_div_derivative hlu ((hasDerivAt_const u (1 : ℝ)).sub hmuder)
      (hS.lam_pos (u, v) hp).ne' (hS.one_sub_mu_pos (u, v) hp).ne'
    apply hd.congr_deriv
    have halg := Local.eq_ray_in_algebra (hr u hu) (hS.lam_pos (u, v) hp).ne'
      (hS.nu_neg (u, v) hp).ne (hS.one_sub_mu_pos (u, v) hp).ne'
      (show S.rUV u v = _ from rfl) (show S.mU u v = _ from rfl)
    change S.rUV u v / S.lam u v -
      (0 - (2 * S.mU u v * S.r u v - 2 * S.m u v * S.nu u v) / S.r u v ^ 2) /
        (1 - S.mu u v) = _
    have heq : (2 * S.mU u v * S.r u v - 2 * S.m u v * S.nu u v) / S.r u v ^ 2 =
        2 * S.mU u v / S.r u v - 2 * S.m u v * S.nu u v / S.r u v ^ 2 := by
      field_simp [hr u hu]
    rw [heq]
    simpa only [zero_sub, neg_div, sub_neg_eq_add, Fields.mu] using! halg

/-- [node restart-eq-ray]
Outgoing Raychaudhuri identity as an AC function and its a.e. derivative,
on every proper positive-radius outgoing segment of the original class. -/
theorem raychaudhuri_out_section (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    AbsolutelyContinuousOnInterval
      (fun v => Real.log (-S.nu u v / (1 - S.mu u v))) a b ∧
      ∀ᵐ v ∂volume.restrict (Icc a b),
        HasDerivAt (fun x => Real.log (-S.nu u x / (1 - S.mu u x)))
          (‖S.theta u v‖ ^ 2 / (S.lam u v * S.r u v)) v := by
  have h := Local.IsSolution.out_section hS hua hab hs
  have mem (x : ℝ) (hx : x ∈ Icc a b) : (u, x) ∈ D := hs ⟨rfl, hx.1, hx.2⟩
  have hr (x : ℝ) (hx : x ∈ Icc a b) :=
    (hS.r_pos (u, x) (mem x hx) (hua.trans_le hx.1)).ne'
  have hacmu : AbsolutelyContinuousOnInterval (S.mu u) a b :=
    ac_div_of_ne_zero (h.2.2.1.1.const_mul 2) h.1.1
      (fun x hx => hr x (by simpa [uIcc_of_le hab] using hx))
  have hacg : AbsolutelyContinuousOnInterval (fun x => 1 - S.mu u x) a b :=
    (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval.sub hacmu
  refine ⟨?_, ?_⟩
  · apply ac_log_of_pos (ac_div_of_ne_zero h.2.1.1.neg hacg ?_) ?_
    · intro x hx
      exact (hS.one_sub_mu_pos (u, x) (mem x (by simpa [uIcc_of_le hab] using hx))).ne'
    · intro x hx
      have hm := mem x (by simpa [uIcc_of_le hab] using hx)
      exact div_pos (neg_pos.mpr (hS.nu_neg (u, x) hm)) (hS.one_sub_mu_pos (u, x) hm)
  · filter_upwards [h.1.2, h.2.1.2, h.2.2.1.2,
      ae_restrict_mem measurableSet_Icc] with v hrv hnv hmv hv
    have hp := mem v hv
    have hmuder : HasDerivAt (S.mu u)
        ((2 * S.mV u v * S.r u v - 2 * S.m u v * S.lam u v) / S.r u v ^ 2) v :=
      (hmv.const_mul 2).div hrv (hr v hv)
    have hd := log_div_derivative hnv.neg ((hasDerivAt_const v (1 : ℝ)).sub hmuder)
      (neg_ne_zero.mpr (hS.nu_neg (u, v) hp).ne) (hS.one_sub_mu_pos (u, v) hp).ne'
    apply hd.congr_deriv
    have halg := Local.eq_ray_out_algebra (hr v hv) (hS.lam_pos (u, v) hp).ne'
      (hS.nu_neg (u, v) hp).ne (hS.one_sub_mu_pos (u, v) hp).ne'
      (show S.rUV u v = _ from rfl) (show S.mV u v = _ from rfl)
    change -S.rUV u v / -S.nu u v -
      (0 - (2 * S.mV u v * S.r u v - 2 * S.m u v * S.lam u v) / S.r u v ^ 2) /
        (1 - S.mu u v) = _
    have heq : (2 * S.mV u v * S.r u v - 2 * S.m u v * S.lam u v) / S.r u v ^ 2 =
        2 * S.mV u v / S.r u v - 2 * S.m u v * S.lam u v / S.r u v ^ 2 := by
      field_simp [hr v hv]
    rw [heq]
    simpa only [zero_sub, neg_div, div_neg, neg_neg, sub_neg_eq_add, Fields.mu] using! halg

/-- [node restart-eq-ray]
Incoming logarithmic Raychaudhuri identity in integral form, with source
integrability derived from AC and the identified a.e. derivative. -/
theorem raychaudhuri_in_integralForm (hS : IsSolution e S D) {a b v : ℝ}
    (hab : a ≤ b) (hbv : b < v) (hs : inSeg a b v ⊆ D) :
    IntegralForm (fun u => Real.log (S.lam u v / (1 - S.mu u v)))
      (fun u => ‖S.xi u v‖ ^ 2 / (S.nu u v * S.r u v)) a b := by
  have h := raychaudhuri_in_section hS hab hbv hs
  exact integralForm_of_ac_of_ae_deriv_eq h.1 (by
    rw [uIcc_of_le hab]
    exact h.2.mono fun _ hx => hx.deriv)

/-- [node restart-eq-ray]
Outgoing logarithmic Raychaudhuri identity in integral form on a proper row.
This is the optical comparison interface for the terminal and gap packets. -/
theorem raychaudhuri_out_integralForm (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    IntegralForm (fun v => Real.log (-S.nu u v / (1 - S.mu u v)))
      (fun v => ‖S.theta u v‖ ^ 2 / (S.lam u v * S.r u v)) a b := by
  have h := raychaudhuri_out_section hS hua hab hs
  exact integralForm_of_ac_of_ae_deriv_eq h.1 (by
    rw [uIcc_of_le hab]
    exact h.2.mono fun _ hx => hx.deriv)

end EmcsfAcExtension.Global.Calculus
