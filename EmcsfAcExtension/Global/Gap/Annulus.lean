/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Global.Gap.Radial
import EmcsfAcExtension.Local.Calculus.RelativeCharge
import EmcsfAcExtension.Local.Calculus.Reconstruction

/-! # Scalar and electric parts of annular mass

All integrals retain the original outgoing null label. Their integrands include
the exact radial Jacobian. Source: charged_SF_new_version.tex:L1554–1598.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Global.Annulus

variable {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}

private theorem annular_derivatives (hS : IsSolution e S D) {u a b x : ℝ}
    (hua : u < a) (hs : outSeg u a b ⊆ D) (hx : x ∈ Ioo a b) :
    HasDerivAt (S.r u) (S.lam u x) x ∧
      HasDerivAt (S.nu u) (S.rUV u x) x ∧
      HasDerivAt (S.m u) (S.mV u x) x := by
  have hp (v : ℝ) (hv : v ∈ Ioo a b) : (u, v) ∈ D :=
    hs ⟨rfl, hv.1.le, hv.2.le⟩
  have sect {f : ℝ → ℝ → ℝ} (hf : ContinuousOn (Function.uncurry f) D) :=
    (Calculus.continuousOn_out_section hf hs).mono Ioo_subset_Icc_self
  have cr := sect hS.cont_r
  have cm := sect hS.cont_m
  have cn := sect hS.cont_nu
  have cl := sect hS.cont_lam
  have cq := sect hS.cont_Q
  have ct := (Calculus.continuousOn_out_section hS.cont_theta hs).mono Ioo_subset_Icc_self
  have nr (v : ℝ) (hv : v ∈ Ioo a b) : S.r u v ≠ 0 :=
    (hS.r_pos (u, v) (hp v hv) (hua.trans hv.1)).ne'
  have ng (v : ℝ) (hv : v ∈ Ioo a b) : 1 - S.mu u v ≠ 0 :=
    (hS.one_sub_mu_pos (u, v) (hp v hv)).ne'
  have cg : ContinuousOn (fun v => 1 - S.mu u v) (Ioo a b) :=
    continuousOn_const.sub ((continuousOn_const.mul cm).div cr nr)
  have cq2 := (cq.pow 2).div (cr.pow 2) (fun v hv => pow_ne_zero _ (nr v hv))
  have cnv : ContinuousOn (S.rUV u) (Ioo a b) :=
    ((cn.mul cl).div cr nr).mul
      ((((continuousOn_const.mul cm).div cr nr).sub cq2).div cg ng)
  have cmv : ContinuousOn (S.mV u) (Ioo a b) :=
    ((cg.mul (ct.norm.pow 2)).div (continuousOn_const.mul cl)
      (fun v hv => mul_ne_zero (by norm_num)
        (hS.lam_pos (u, v) (hp v hv)).ne')).add
    (((cq.pow 2).mul cl).div (continuousOn_const.mul (cr.pow 2))
      (fun v hv => mul_ne_zero (by norm_num) (pow_ne_zero _ (nr v hv))))
  have hform c d (hc : a < c) (hcd : c ≤ d) (hd : d < b) :=
    hS.eq_out u c d (hua.trans hc) hcd (by
      rintro ⟨s, t⟩ ⟨rfl, hmem⟩
      exact hs ⟨rfl, hc.le.trans hmem.1, hmem.2.trans hd.le⟩)
  exact ⟨Local.hasDerivAt_of_integralForm_interior hx cl
      (fun c d hc hcd hd => (hform c d hc hcd hd).1),
    Local.hasDerivAt_of_integralForm_interior hx cnv
      (fun c d hc hcd hd => (hform c d hc hcd hd).2.1),
    Local.hasDerivAt_of_integralForm_interior hx cmv
      (fun c d hc hcd hd => (hform c d hc hcd hd).2.2.1)⟩

/-- [node cg:radial-ratio]
The radial quotient identity in the original outgoing label. Dividing the
displayed derivative by `λ` gives precisely the radial derivative. -/
theorem radial_ratio (hS : IsSolution e S D) {u a b x : ℝ}
    (hua : u < a) (hs : outSeg u a b ⊆ D) (hx : x ∈ Ioo a b) :
    HasDerivAt (fun v => (1 - S.mu u v) / (-S.nu u v))
      (-S.lam u x * (1 - S.mu u x) / ((-S.nu u x) * S.r u x) *
        ‖S.theta u x / S.lam u x‖ ^ 2) x := by
  have hp := hs (show (u, x) ∈ outSeg u a b from ⟨rfl, hx.1.le, hx.2.le⟩)
  have hr := (hS.r_pos (u, x) hp (hua.trans hx.1)).ne'
  have hn := (hS.nu_neg (u, x) hp).ne
  have hl := (hS.lam_pos (u, x) hp).ne'
  have hg := (hS.one_sub_mu_pos (u, x) hp).ne'
  have hmu : 2 * S.m u x = S.mu u x * S.r u x := (div_eq_iff hr).mp rfl
  obtain ⟨dr, dn, dm⟩ := annular_derivatives hS hua hs hx
  have dmu := (dm.const_mul 2).div dr hr
  have hd := ((hasDerivAt_const x (1 : ℝ)).sub dmu).div dn.neg (neg_ne_zero.mpr hn)
  have hm := (div_eq_iff hl).mp (Gap.radial_mass hS hp)
  convert hd using 1
  · rfl
  · dsimp only [Pi.div_apply, Pi.sub_apply, Pi.neg_apply]
    rw [hm, hmu]
    dsimp only [Fields.rUV]
    field_simp [hr, hn, hg]
    ; ring

/-- [node cg:radial-weight]
The logarithmic radial-weight identity on every positive-radius characteristic
interior. The coefficient is exact for arbitrary coupling and data size. -/
theorem radial_weight (hS : IsSolution e S D) {u a b x : ℝ}
    (hua : u < a) (hs : outSeg u a b ⊆ D) (hx : x ∈ Ioo a b) :
    HasDerivAt (fun v => Real.log (S.nu u v ^ 2 / (1 - S.mu u v)))
      (S.lam u x / S.r u x *
        ((S.mu u x - S.Q u x ^ 2 / S.r u x ^ 2) / (1 - S.mu u x) +
          ‖S.theta u x / S.lam u x‖ ^ 2)) x := by
  have hp := hs (show (u, x) ∈ outSeg u a b from ⟨rfl, hx.1.le, hx.2.le⟩)
  have hr := (hS.r_pos (u, x) hp (hua.trans hx.1)).ne'
  have hn := (hS.nu_neg (u, x) hp).ne
  have hl := (hS.lam_pos (u, x) hp).ne'
  have hg := (hS.one_sub_mu_pos (u, x) hp).ne'
  have hmu : 2 * S.m u x = S.mu u x * S.r u x := (div_eq_iff hr).mp rfl
  obtain ⟨dr, dn, dm⟩ := annular_derivatives hS hua hs hx
  have dmu := (dm.const_mul 2).div dr hr
  have hd := ((dn.pow 2).div ((hasDerivAt_const x (1 : ℝ)).sub dmu) hg).log
    (div_ne_zero (pow_ne_zero _ hn) hg)
  have hm := (div_eq_iff hl).mp (Gap.radial_mass hS hp)
  convert hd using 1
  · rfl
  · dsimp only [Pi.div_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]
    rw [hm, hmu]
    dsimp only [Fields.rUV]
    field_simp [hr, hn, hg]
    ; ring

/-- [node cg:radial-ratio]
The endpoint form of the quotient identity, with its exact radial Jacobian. -/
theorem radial_ratio_integral (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    (1 - S.mu u a) / (-S.nu u a) - (1 - S.mu u b) / (-S.nu u b) =
      ∫ v in a..b, S.lam u v * (1 - S.mu u v) /
        ((-S.nu u v) * S.r u v) * ‖S.theta u v / S.lam u v‖ ^ 2 := by
  have hp (v : ℝ) (hv : v ∈ Icc a b) : (u, v) ∈ D := hs ⟨rfl, hv⟩
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cm := Calculus.continuousOn_out_section hS.cont_m hs
  have cn := Calculus.continuousOn_out_section hS.cont_nu hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have ct := Calculus.continuousOn_out_section hS.cont_theta hs
  have nr (v : ℝ) (hv : v ∈ Icc a b) : S.r u v ≠ 0 :=
    (hS.r_pos (u, v) (hp v hv) (hua.trans_le hv.1)).ne'
  have nn (v : ℝ) (hv : v ∈ Icc a b) : -S.nu u v ≠ 0 :=
    neg_ne_zero.mpr (hS.nu_neg (u, v) (hp v hv)).ne
  have nl (v : ℝ) (hv : v ∈ Icc a b) : S.lam u v ≠ 0 :=
    (hS.lam_pos (u, v) (hp v hv)).ne'
  have cg : ContinuousOn (fun v => 1 - S.mu u v) (Icc a b) :=
    continuousOn_const.sub ((continuousOn_const.mul cm).div cr nr)
  have cx := ct.div (Complex.continuous_ofReal.comp_continuousOn cl)
    (fun v hv => Complex.ofReal_ne_zero.mpr (nl v hv))
  have ci := (((cl.mul cg).div (cn.neg.mul cr)
    (fun v hv => mul_ne_zero (nn v hv) (nr v hv))).mul (cx.norm.pow 2))
  have hi : IntervalIntegrable (fun v => -(S.lam u v * (1 - S.mu u v) /
      ((-S.nu u v) * S.r u v) * ‖S.theta u v / S.lam u v‖ ^ 2)) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab ci.neg
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (cg.div cn.neg nn) (fun v hv => by
      convert radial_ratio hS hua hs hv using 1; ring) hi
  rw [intervalIntegral.integral_neg] at hf
  dsimp only [Pi.div_apply, Pi.neg_apply] at hf
  linarith only [hf]

private theorem weight_mono_of_charge_bound (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hs : outSeg u a b ⊆ D)
    (hcharge : ∀ v ∈ Icc a b, S.Q u v ^ 2 / S.r u v ^ 2 ≤ S.mu u v) :
    MonotoneOn (fun v => S.nu u v ^ 2 / (1 - S.mu u v)) (Icc a b) := by
  have hp (v : ℝ) (hv : v ∈ Icc a b) : (u, v) ∈ D := hs ⟨rfl, hv⟩
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cm := Calculus.continuousOn_out_section hS.cont_m hs
  have cn := Calculus.continuousOn_out_section hS.cont_nu hs
  have cg : ContinuousOn (fun v => 1 - S.mu u v) (Icc a b) :=
    continuousOn_const.sub ((continuousOn_const.mul cm).div cr
      (fun v hv => (hS.r_pos (u, v) (hp v hv) (hua.trans_le hv.1)).ne'))
  have hw v (hv : v ∈ Icc a b) : 0 < S.nu u v ^ 2 / (1 - S.mu u v) :=
    div_pos (sq_pos_of_ne_zero (hS.nu_neg (u, v) (hp v hv)).ne)
      (hS.one_sub_mu_pos (u, v) (hp v hv))
  have hd v (hv : v ∈ interior (Icc a b)) :=
    radial_weight hS hua hs (show v ∈ Ioo a b by simpa only [interior_Icc] using hv)
  have hm := monotoneOn_of_deriv_nonneg (convex_Icc a b)
    (((cn.pow 2).div cg (fun v hv => (hS.one_sub_mu_pos (u, v) (hp v hv)).ne')).log
      (fun v hv => (hw v hv).ne'))
    (fun v hv => (hd v hv).differentiableAt.differentiableWithinAt) (fun v hv => by
      change 0 ≤ deriv (fun v => Real.log (S.nu u v ^ 2 / (1 - S.mu u v))) v
      rw [(hd v hv).deriv]
      have hv' := interior_subset hv
      exact mul_nonneg
        (div_nonneg (hS.lam_pos (u, v) (hp v hv')).le
          (hS.r_pos (u, v) (hp v hv') (hua.trans_le hv'.1)).le)
        (add_nonneg (div_nonneg (sub_nonneg.mpr (hcharge v hv'))
          (hS.one_sub_mu_pos (u, v) (hp v hv')).le) (sq_nonneg _)))
  intro v hv w hw' hvw
  exact (Real.log_le_log_iff (hw v hv) (hw w hw')).mp (hm hv hw' hvw)

private theorem ratio_of_charge_bound (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D)
    (hcharge : ∀ v ∈ Icc a b, S.Q u v ^ 2 / S.r u v ^ 2 ≤ S.mu u v) :
    1 + (∫ v in a..b,
        S.lam u v * (1 - S.mu u v) * ‖S.theta u v / S.lam u v‖ ^ 2) /
      ((1 - S.mu u b) * S.r u b) ≤
      (-S.nu u b) * (1 - S.mu u a) / ((-S.nu u a) * (1 - S.mu u b)) := by
  have hp (v : ℝ) (hv : v ∈ Icc a b) : (u, v) ∈ D := hs ⟨rfl, hv⟩
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cm := Calculus.continuousOn_out_section hS.cont_m hs
  have cn := Calculus.continuousOn_out_section hS.cont_nu hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have ct := Calculus.continuousOn_out_section hS.cont_theta hs
  have hr (v : ℝ) (hv : v ∈ Icc a b) := hS.r_pos (u, v) (hp v hv) (hua.trans_le hv.1)
  have hn (v : ℝ) (hv : v ∈ Icc a b) : 0 < -S.nu u v := neg_pos.mpr (hS.nu_neg (u, v) (hp v hv))
  have hg (v : ℝ) (hv : v ∈ Icc a b) := hS.one_sub_mu_pos (u, v) (hp v hv)
  have cg : ContinuousOn (fun v => 1 - S.mu u v) (Icc a b) :=
    continuousOn_const.sub ((continuousOn_const.mul cm).div cr (fun v hv => (hr v hv).ne'))
  have cx := ct.div (Complex.continuous_ofReal.comp_continuousOn cl)
    (fun v hv => Complex.ofReal_ne_zero.mpr (hS.lam_pos (u, v) (hp v hv)).ne')
  have cf := (cl.mul cg).mul (cx.norm.pow 2)
  have cfR := ((cl.mul cg).div (cn.neg.mul cr)
    (fun v hv => mul_ne_zero (hn v hv).ne' (hr v hv).ne')).mul (cx.norm.pow 2)
  have nmono : MonotoneOn (fun v => -S.nu u v) (Icc a b) :=
    fun v hv w hw hvw => neg_le_neg (Gap.nu_out_antitone_of_charge_bound hS
      (hua.trans_le hv.1) hvw
      (fun p hp => hs (outSeg_subset_outSeg hv.1 hw.2 hp))
      (fun t ht => hcharge t ⟨hv.1.trans ht.1, ht.2.trans hw.2⟩))
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hi := intervalIntegral.integral_mono_on hab
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab (cf.div_const ((-S.nu u b) * S.r u
        b)))
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab cfR) (fun v hv => by
      have hrad := Gap.radius_out_le hS (hua.trans_le hv.1).le hv.2
        (fun p hp => hs (outSeg_subset_outSeg hv.1 le_rfl hp))
      have hden := mul_le_mul (nmono hv hb hv.2) hrad (hr v hv).le (hn b hb).le
      have hdiv := div_le_div_of_nonneg_left
        (mul_nonneg (mul_nonneg (hS.lam_pos (u, v) (hp v hv)).le (hg v hv).le)
          (sq_nonneg ‖S.theta u v / S.lam u v‖))
        (mul_pos (hn v hv) (hr v hv)) hden
      convert hdiv using 1 <;>
        dsimp only [Pi.mul_apply, Pi.div_apply, Pi.neg_apply, Pi.pow_apply, Function.comp_apply];
            ring)
  change (∫ v in a..b, (S.lam u v * (1 - S.mu u v) *
      ‖S.theta u v / S.lam u v‖ ^ 2) / ((-S.nu u b) * S.r u b)) ≤
    ∫ v in a..b, S.lam u v * (1 - S.mu u v) /
      ((-S.nu u v) * S.r u v) * ‖S.theta u v / S.lam u v‖ ^ 2 at hi
  rw [intervalIntegral.integral_div, ← radial_ratio_integral hS hua hab hs] at hi
  have hi' := mul_le_mul_of_nonneg_right hi
    (mul_nonneg (mul_nonneg (hn a ha).le (hn b hb).le) (hr b hb).le)
  have hi'' : (∫ v in a..b, S.lam u v * (1 - S.mu u v) *
      ‖S.theta u v / S.lam u v‖ ^ 2) * (-S.nu u a) ≤
      ((-S.nu u b) * (1 - S.mu u a) - (1 - S.mu u b) * (-S.nu u a)) * S.r u b := by
    convert hi' using 1 <;>
      field_simp [neg_ne_zero.mp (hn a ha).ne', neg_ne_zero.mp (hn b hb).ne', (hr b hb).ne']
  apply (le_div_iff₀ (mul_pos (hn a ha) (hg b hb))).mpr
  calc
    _ = (1 - S.mu u b) * (-S.nu u a) +
        ((∫ v in a..b, S.lam u v * (1 - S.mu u v) *
          ‖S.theta u v / S.lam u v‖ ^ 2) * (-S.nu u a)) / S.r u b := by
      field_simp [(hg b hb).ne', (hr b hb).ne']
      ; ring
    _ ≤ _ := by
      have hh : ((∫ v in a..b, S.lam u v * (1 - S.mu u v) *
          ‖S.theta u v / S.lam u v‖ ^ 2) * (-S.nu u a)) / S.r u b ≤
          (-S.nu u b) * (1 - S.mu u a) - (1 - S.mu u b) * (-S.nu u a) := by
        exact (div_le_iff₀ (hr b hb)).mpr hi''
      linarith only [hh]

/-- [node cg:ratio]
The integrated annular ratio in the conditional setting. The scalar mass
integral is twice `Δsc`; the exact coefficient is uniform in all parameters. -/
theorem ratio {δ : ℝ} (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u u b ⊆ D)
    (hδ : 0 < δ ∧ δ ≤ 1) (hmu : ∀ v ∈ Icc u b, 0 ≤ S.mu u v)
    (hgap : ∀ v ∈ Icc u b, δ ≤ 1 - S.mu u v)
    (hsmall : ∀ v ∈ Icc u b, |e| * S.r u v * ‖S.phi u v‖ ≤ δ / 64) :
    1 + (∫ v in a..b,
        S.lam u v * (1 - S.mu u v) * ‖S.theta u v / S.lam u v‖ ^ 2) /
      ((1 - S.mu u b) * S.r u b) ≤
      (-S.nu u b) * (1 - S.mu u a) / ((-S.nu u a) * (1 - S.mu u b)) := by
  apply ratio_of_charge_bound hS hua hab (fun p hp => hs (outSeg_subset_outSeg hua.le le_rfl hp))
  intro v hv
  have huv : u < v := hua.trans_le hv.1
  have hmem : v ∈ Icc u b := ⟨huv.le, hv.2⟩
  have hc := (Gap.relative_charge hS huv
    (fun p hp => hs (outSeg_subset_outSeg le_rfl hv.2 hp)) hδ (hmu v hmem)
    (fun s hs => hgap s ⟨hs.1, hs.2.trans hv.2⟩)
    (fun s hs => hsmall s ⟨hs.1, hs.2.trans hv.2⟩)).1
  exact hc.trans (mul_le_of_le_one_left (hmu v hmem) (by linarith only [hδ.2]))

/-- [node cg:radial-weight]
The radial weight is nondecreasing under the original conditional cone bounds.
The sign follows from Gauss' law, without an additional optical hypothesis. -/
theorem radial_weight_monotone {δ : ℝ} (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hs : outSeg u u b ⊆ D)
    (hδ : 0 < δ ∧ δ ≤ 1) (hmu : ∀ v ∈ Icc u b, 0 ≤ S.mu u v)
    (hgap : ∀ v ∈ Icc u b, δ ≤ 1 - S.mu u v)
    (hsmall : ∀ v ∈ Icc u b, |e| * S.r u v * ‖S.phi u v‖ ≤ δ / 64) :
    MonotoneOn (fun v => S.nu u v ^ 2 / (1 - S.mu u v)) (Icc a b) := by
  apply weight_mono_of_charge_bound hS hua
    (fun p hp => hs (outSeg_subset_outSeg hua.le le_rfl hp))
  intro v hv
  have huv : u < v := hua.trans_le hv.1
  have hmem : v ∈ Icc u b := ⟨huv.le, hv.2⟩
  have hc := (Gap.relative_charge hS huv
    (fun p hp => hs (outSeg_subset_outSeg le_rfl hv.2 hp)) hδ (hmu v hmem)
    (fun s hs => hgap s ⟨hs.1, hs.2.trans hv.2⟩)
    (fun s hs => hsmall s ⟨hs.1, hs.2.trans hv.2⟩)).1
  exact hc.trans (mul_le_of_le_one_left (hmu v hmem) (by linarith only [hδ.2]))

/-- [node lem:charged-conditional-gap#incoming-flux-decomposition]
The negative incoming mass density is exactly the sum of the scalar and electric
fluxes. The identity holds for complex scalars without a phase choice. -/
theorem incoming_flux_decomposition (S : Fields) (u v : ℝ) :
    -S.mU u v = (1 - S.mu u v) / (2 * (-S.nu u v)) * ‖S.xi u v‖ ^ 2 +
      (-S.nu u v) * S.Q u v ^ 2 / (2 * S.r u v ^ 2) := by
  simp only [Fields.mU, neg_add_rev, neg_mul, mul_div_assoc]
  ring

/-- [node lem:charged-conditional-gap#annular-masses]
Across a positive-radius annulus, scalar mass is nonnegative, is at most the
ordinary mass difference, and leaves exactly the electric radial mass. The
coefficient `1/2` is uniform in the solution, coupling, and annulus. -/
theorem annular_masses (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    0 ≤ (1 / 2 : ℝ) * (∫ v in a..b,
      S.lam u v * (1 - S.mu u v) * ‖S.theta u v / S.lam u v‖ ^ 2) ∧
    (1 / 2 : ℝ) * (∫ v in a..b,
      S.lam u v * (1 - S.mu u v) * ‖S.theta u v / S.lam u v‖ ^ 2) ≤
      S.m u b - S.m u a ∧
    2 * ((S.m u b - S.m u a) - (1 / 2 : ℝ) * (∫ v in a..b,
      S.lam u v * (1 - S.mu u v) * ‖S.theta u v / S.lam u v‖ ^ 2)) =
      ∫ v in a..b, S.lam u v * (S.Q u v ^ 2 / S.r u v ^ 2) := by
  have hp (v : ℝ) (hv : v ∈ Icc a b) : (u, v) ∈ D := hs ⟨rfl, hv⟩
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cm := Calculus.continuousOn_out_section hS.cont_m hs
  have cq := Calculus.continuousOn_out_section hS.cont_Q hs
  have ct := Calculus.continuousOn_out_section hS.cont_theta hs
  have nr (v : ℝ) (hv : v ∈ Icc a b) : S.r u v ≠ 0 :=
    (hS.r_pos (u, v) (hp v hv) (hua.trans_le hv.1)).ne'
  have nl (v : ℝ) (hv : v ∈ Icc a b) : S.lam u v ≠ 0 :=
    (hS.lam_pos (u, v) (hp v hv)).ne'
  have cg : ContinuousOn (fun v => 1 - S.mu u v) (Icc a b) :=
    continuousOn_const.sub ((continuousOn_const.mul cm).div cr nr)
  have cx := ct.div (Complex.continuous_ofReal.comp_continuousOn cl)
    (fun v hv => Complex.ofReal_ne_zero.mpr (nl v hv))
  have ifs : IntervalIntegrable (fun v => S.lam u v * (1 - S.mu u v) *
      ‖S.theta u v / S.lam u v‖ ^ 2) volume a b := ContinuousOn.intervalIntegrable_of_Icc hab
    ((cl.mul cg).mul (cx.norm.pow 2))
  have ife : IntervalIntegrable (fun v => S.lam u v * (S.Q u v ^ 2 / S.r u v ^ 2))
      volume a b := ContinuousOn.intervalIntegrable_of_Icc hab
    (cl.mul ((cq.pow 2).div (cr.pow 2) (fun v hv => pow_ne_zero _ (nr v hv))))
  have hfs : 0 ≤ ∫ v in a..b,
      S.lam u v * (1 - S.mu u v) * ‖S.theta u v / S.lam u v‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun v hv =>
      mul_nonneg (mul_nonneg (hS.lam_pos (u, v) (hp v hv)).le
        (hS.one_sub_mu_pos (u, v) (hp v hv)).le) (sq_nonneg _))
  have hfe : 0 ≤ ∫ v in a..b, S.lam u v * (S.Q u v ^ 2 / S.r u v ^ 2) :=
    intervalIntegral.integral_nonneg hab (fun v hv =>
      mul_nonneg (hS.lam_pos (u, v) (hp v hv)).le
        (div_nonneg (sq_nonneg _) (sq_nonneg _)))
  have heq : 2 * (S.m u b - S.m u a) =
      (∫ v in a..b, S.lam u v * (1 - S.mu u v) *
        ‖S.theta u v / S.lam u v‖ ^ 2) +
      (∫ v in a..b, S.lam u v * (S.Q u v ^ 2 / S.r u v ^ 2)) := by
    rw [(Gap.mass hS).1 u a b hua.le hab hs |>.2,
      ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add ifs ife]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hab] at hv
    have h := Local.RelCharge.radial_mass_equation hS (hp v hv)
    apply (div_eq_iff (nl v hv)).mp at h
    linear_combination h
  exact ⟨mul_nonneg (by norm_num) hfs, by linarith only [heq, hfe], by linarith only [heq]⟩

/-- [node cg:xi-decomposition]
The exact complex scalar transport decomposition on a positive-radius annulus.
The null-label scalar integral equals the radial integral because `dr = λ dv`.
There is no phase or gauge normalization of the scalar. -/
theorem xi_decomposition (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    S.xi u b = S.xi u a +
      (∫ v in a..b, ((-S.nu u v / S.r u v : ℝ) : ℂ) * S.theta u v) +
      (-Complex.I) * (∫ v in a..b,
        ((e * S.Q u v * (-S.nu u v) * S.lam u v /
          ((1 - S.mu u v) * S.r u v) : ℝ) : ℂ) * S.phi u v) := by
  have hp (v : ℝ) (hv : v ∈ Icc a b) : (u, v) ∈ D := hs ⟨rfl, hv⟩
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cm := Calculus.continuousOn_out_section hS.cont_m hs
  have cn := Calculus.continuousOn_out_section hS.cont_nu hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have cq := Calculus.continuousOn_out_section hS.cont_Q hs
  have ct := Calculus.continuousOn_out_section hS.cont_theta hs
  have cp := Calculus.continuousOn_out_section hS.cont_phi hs
  have nr (v : ℝ) (hv : v ∈ Icc a b) : S.r u v ≠ 0 :=
    (hS.r_pos (u, v) (hp v hv) (hua.trans_le hv.1)).ne'
  have ng (v : ℝ) (hv : v ∈ Icc a b) : 1 - S.mu u v ≠ 0 :=
    (hS.one_sub_mu_pos (u, v) (hp v hv)).ne'
  have cg : ContinuousOn (fun v => 1 - S.mu u v) (Icc a b) :=
    continuousOn_const.sub ((continuousOn_const.mul cm).div cr nr)
  have cI : ContinuousOn (fun v => ((-S.nu u v / S.r u v : ℝ) : ℂ) * S.theta u v)
      (Icc a b) := (Complex.continuous_ofReal.comp_continuousOn (cn.neg.div cr nr)).mul ct
  have cE : ContinuousOn (fun v =>
      ((e * S.Q u v * (-S.nu u v) * S.lam u v /
        ((1 - S.mu u v) * S.r u v) : ℝ) : ℂ) * S.phi u v) (Icc a b) :=
    (Complex.continuous_ofReal.comp_continuousOn
    ((((continuousOn_const.mul cq).mul cn.neg).mul cl).div (cg.mul cr)
      (fun v hv => mul_ne_zero (ng v hv) (nr v hv)))).mul cp
  have ifI := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab cI
  have ifE := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab cE
  have hf := (Gap.scalar hS hua.le hab hs).2.2
  rw [add_assoc, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ifI (ifE.const_mul (-Complex.I))]
  have hi : (∫ v in a..b, S.xiV e u v) =
      ∫ v in a..b, ((-S.nu u v / S.r u v : ℝ) : ℂ) * S.theta u v +
        (-Complex.I) * (((e * S.Q u v * (-S.nu u v) * S.lam u v /
          ((1 - S.mu u v) * S.r u v) : ℝ) : ℂ) * S.phi u v) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hab] at hv
    have hr := Complex.ofReal_ne_zero.mpr (nr v hv)
    have hg := Complex.ofReal_ne_zero.mpr (ng v hv)
    simp only [Fields.xiV, Fields.waveSource, Complex.ofReal_mul,
      Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_sub,
      Complex.ofReal_one]
    field_simp [hr, hg]
  rw [← hi, ← hf]
  abel

/-- [internal] Cauchy–Schwarz for continuous real functions on a closed interval. -/
theorem scalar_cauchy_schwarz {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b)) :
    (∫ v in a..b, f v * g v) ^ 2 ≤
      (∫ v in a..b, f v ^ 2) * (∫ v in a..b, g v ^ 2) := by
  have iff : IntervalIntegrable (fun v => f v ^ 2) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (hf.pow 2)
  have ifg : IntervalIntegrable (fun v => f v * g v) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (hf.mul hg)
  have igg : IntervalIntegrable (fun v => g v ^ 2) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (hg.pow 2)
  have h (t : ℝ) : 0 ≤ (∫ v in a..b, g v ^ 2) * (t * t) +
      (2 * ∫ v in a..b, f v * g v) * t + ∫ v in a..b, f v ^ 2 := by
    have hp := intervalIntegral.integral_nonneg (μ := volume) hab
      (fun v _ => sq_nonneg (f v + t * g v))
    have he : (∫ v in a..b, (f v + t * g v) ^ 2) =
        (∫ v in a..b, f v ^ 2) + 2 * t * (∫ v in a..b, f v * g v) +
          t ^ 2 * (∫ v in a..b, g v ^ 2) := by
      calc
        _ = ∫ v in a..b, (f v ^ 2 + (2 * t) * (f v * g v)) + t ^ 2 * g v ^ 2 :=
          intervalIntegral.integral_congr (fun v _ => by ring)
        _ = _ := by
          rw [intervalIntegral.integral_add (iff.add (ifg.const_mul (2 * t)))
            (igg.const_mul (t ^ 2)), intervalIntegral.integral_add iff (ifg.const_mul (2 * t))]
          simp only [intervalIntegral.integral_const_mul]
    rw [he] at hp
    nlinarith only [hp]
  have hd := discrim_le_zero h
  dsimp [discrim] at hd
  nlinarith only [hd]

/-- [internal] Weighted complex Cauchy–Schwarz with the exact outgoing Jacobian. -/
theorem weighted_scalar_cauchy_schwarz (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    ‖∫ v in a..b, ((-S.nu u v / S.r u v : ℝ) : ℂ) * S.theta u v‖ ^ 2 ≤
      (∫ v in a..b, S.lam u v * (1 - S.mu u v) * ‖S.theta u v / S.lam u v‖ ^ 2) *
      (∫ v in a..b, S.nu u v ^ 2 / (1 - S.mu u v) * (S.lam u v / S.r u v ^ 2)) := by
  have hp (v : ℝ) (hv : v ∈ Icc a b) : (u, v) ∈ D := hs ⟨rfl, hv⟩
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cn := Calculus.continuousOn_out_section hS.cont_nu hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have ct := Calculus.continuousOn_out_section hS.cont_theta hs
  have cm := Calculus.continuousOn_out_section hS.cont_m hs
  have hr v (hv : v ∈ Icc a b) := hS.r_pos (u, v) (hp v hv) (hua.trans_le hv.1)
  have hl v (hv : v ∈ Icc a b) := hS.lam_pos (u, v) (hp v hv)
  have hg v (hv : v ∈ Icc a b) := hS.one_sub_mu_pos (u, v) (hp v hv)
  have hn v (hv : v ∈ Icc a b) : 0 < -S.nu u v := neg_pos.mpr (hS.nu_neg (u, v) (hp v hv))
  have cg : ContinuousOn (fun v => 1 - S.mu u v) (Icc a b) :=
    continuousOn_const.sub ((continuousOn_const.mul cm).div cr (fun v hv => (hr v hv).ne'))
  have cx := ct.div (Complex.continuous_ofReal.comp_continuousOn cl)
    (fun v hv => Complex.ofReal_ne_zero.mpr (hl v hv).ne')
  let f := fun v => Real.sqrt (S.lam u v) * Real.sqrt (1 - S.mu u v) *
    ‖S.theta u v / S.lam u v‖
  let g := fun v => Real.sqrt (S.lam u v) / Real.sqrt (1 - S.mu u v) * (-S.nu u v) / S.r u v
  have cf : ContinuousOn f (Icc a b) := (cl.sqrt.mul cg.sqrt).mul cx.norm
  have cgg : ContinuousOn g (Icc a b) :=
    ((cl.sqrt.div cg.sqrt (fun v hv => (Real.sqrt_pos.mpr (hg v hv)).ne')).mul cn.neg).div cr
      (fun v hv => (hr v hv).ne')
  have fsq v (hv : v ∈ Icc a b) : f v ^ 2 =
      S.lam u v * (1 - S.mu u v) * ‖S.theta u v / S.lam u v‖ ^ 2 := by
    dsimp [f]
    rw [mul_pow, mul_pow, Real.sq_sqrt (hl v hv).le, Real.sq_sqrt (hg v hv).le]
  have gsq v (hv : v ∈ Icc a b) : g v ^ 2 =
      S.nu u v ^ 2 / (1 - S.mu u v) * (S.lam u v / S.r u v ^ 2) := by
    dsimp [g]
    rw [div_pow, mul_pow, div_pow, Real.sq_sqrt (hl v hv).le,
      Real.sq_sqrt (hg v hv).le, neg_sq]
    ring
  have fg v (hv : v ∈ Icc a b) :
      ‖((-S.nu u v / S.r u v : ℝ) : ℂ) * S.theta u v‖ = f v * g v := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos (hn v hv) (hr v hv))]
    have he : f v * g v = Real.sqrt (S.lam u v) ^ 2 *
        (-S.nu u v / S.r u v) * ‖S.theta u v / S.lam u v‖ := by
      dsimp [f, g]
      field_simp [(Real.sqrt_pos.mpr (hg v hv)).ne']
    rw [he, Real.sq_sqrt (hl v hv).le, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (hl v hv)]
    field_simp [(hl v hv).ne']
  have hnorm := intervalIntegral.norm_integral_le_integral_norm (μ := volume) hab
    (f := fun v => ((-S.nu u v / S.r u v : ℝ) : ℂ) * S.theta u v)
  rw [intervalIntegral.integral_congr (fun v hv => fg v (by
    simpa only [uIcc_of_le hab] using hv))] at hnorm
  have hsq := (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hnorm)).mpr hnorm
  have hcs := hsq.trans (scalar_cauchy_schwarz hab cf cgg)
  rw [intervalIntegral.integral_congr (fun v hv => fsq v (by
    simpa only [uIcc_of_le hab] using hv)), intervalIntegral.integral_congr (fun v hv => gsq v (by
    simpa only [uIcc_of_le hab] using hv))] at hcs
  exact hcs

private theorem scalar_integral_of_charge_bound (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D)
    (hcharge : ∀ v ∈ Icc a b, S.Q u v ^ 2 / S.r u v ^ 2 ≤ S.mu u v) :
    ‖∫ v in a..b, ((-S.nu u v / S.r u v : ℝ) : ℂ) * S.theta u v‖ ^ 2 ≤
      (∫ v in a..b, S.lam u v * (1 - S.mu u v) *
        ‖S.theta u v / S.lam u v‖ ^ 2) * S.nu u b ^ 2 * (S.r u b - S.r u a) /
        ((1 - S.mu u b) * S.r u a * S.r u b) := by
  have hp (v : ℝ) (hv : v ∈ Icc a b) : (u, v) ∈ D := hs ⟨rfl, hv⟩
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cn := Calculus.continuousOn_out_section hS.cont_nu hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have cm := Calculus.continuousOn_out_section hS.cont_m hs
  have hr v (hv : v ∈ Icc a b) := hS.r_pos (u, v) (hp v hv) (hua.trans_le hv.1)
  have hl v (hv : v ∈ Icc a b) := hS.lam_pos (u, v) (hp v hv)
  have hg v (hv : v ∈ Icc a b) := hS.one_sub_mu_pos (u, v) (hp v hv)
  have cg : ContinuousOn (fun v => 1 - S.mu u v) (Icc a b) :=
    continuousOn_const.sub ((continuousOn_const.mul cm).div cr (fun v hv => (hr v hv).ne'))
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have cJ : ContinuousOn (fun v => S.lam u v / S.r u v ^ 2) (Icc a b) :=
    cl.div (cr.pow 2) (fun v hv => pow_ne_zero _ (hr v hv).ne')
  have hJ : (∫ v in a..b, S.lam u v / S.r u v ^ 2) = 1 / S.r u a - 1 / S.r u b := by
    have cP : ContinuousOn (fun v => (-1 : ℝ) / S.r u v) (Icc a b) :=
      continuousOn_const.div cr (fun v hv => (hr v hv).ne')
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
      cP (fun v hv => by
        have hd := (hasDerivAt_const v (-1 : ℝ)).div (annular_derivatives hS hua hs hv).1
          (hr v (Ioo_subset_Icc_self hv)).ne'
        convert hd using 1; simp only [zero_mul, neg_mul, one_mul, zero_sub, neg_neg])
      (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab cJ)
    calc
      _ = -1 / S.r u b - -1 / S.r u a := hh
      _ = _ := by ring
  have wm := weight_mono_of_charge_bound hS hua hs hcharge
  have hgg := intervalIntegral.integral_mono_on hab
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab
      (((cn.pow 2).div cg (fun v hv => (hg v hv).ne')).mul cJ))
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab (cJ.const_mul
      (S.nu u b ^ 2 / (1 - S.mu u b)))) (fun v hv => by
        change (S.nu u v ^ 2 / (1 - S.mu u v)) * (S.lam u v / S.r u v ^ 2) ≤
          (S.nu u b ^ 2 / (1 - S.mu u b)) * (S.lam u v / S.r u v ^ 2)
        exact mul_le_mul_of_nonneg_right (wm hv hb hv.2)
          (div_nonneg (hl v hv).le (sq_nonneg _)))
  change (∫ v in a..b, S.nu u v ^ 2 / (1 - S.mu u v) * (S.lam u v / S.r u v ^ 2)) ≤
    ∫ v in a..b, (S.nu u b ^ 2 / (1 - S.mu u b)) * (S.lam u v / S.r u v ^ 2) at hgg
  rw [intervalIntegral.integral_const_mul, hJ] at hgg
  have hA : 0 ≤ ∫ v in a..b, S.lam u v * (1 - S.mu u v) *
      ‖S.theta u v / S.lam u v‖ ^ 2 := by
    have hh := (annular_masses hS hua hab hs).1
    linarith only [hh]
  have htotal := (weighted_scalar_cauchy_schwarz hS hua hab hs).trans
    (mul_le_mul_of_nonneg_left hgg hA)
  convert htotal using 1
  field_simp [(hr a ha).ne', (hr b hb).ne', (hg b hb).ne']

/-- [node lem:charged-conditional-gap#annular-scalar-integral]
The scalar transport integral has the exact weighted Cauchy–Schwarz bound.
Its constant is uniform over the coupling, solution, bootstrap gap and annulus. -/
theorem annular_scalar_integral {δ : ℝ} (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u u b ⊆ D)
    (hδ : 0 < δ ∧ δ ≤ 1) (hmu : ∀ v ∈ Icc u b, 0 ≤ S.mu u v)
    (hgap : ∀ v ∈ Icc u b, δ ≤ 1 - S.mu u v)
    (hsmall : ∀ v ∈ Icc u b, |e| * S.r u v * ‖S.phi u v‖ ≤ δ / 64) :
    ‖∫ v in a..b, ((-S.nu u v / S.r u v : ℝ) : ℂ) * S.theta u v‖ ^ 2 ≤
      (∫ v in a..b, S.lam u v * (1 - S.mu u v) *
        ‖S.theta u v / S.lam u v‖ ^ 2) * S.nu u b ^ 2 * (S.r u b - S.r u a) /
        ((1 - S.mu u b) * S.r u a * S.r u b) := by
  apply scalar_integral_of_charge_bound hS hua hab
    (fun p hp => hs (outSeg_subset_outSeg hua.le le_rfl hp))
  intro v hv
  have huv : u < v := hua.trans_le hv.1
  have hmem : v ∈ Icc u b := ⟨huv.le, hv.2⟩
  have hc := (Gap.relative_charge hS huv
    (fun p hp => hs (outSeg_subset_outSeg le_rfl hv.2 hp)) hδ (hmu v hmem)
    (fun s hs => hgap s ⟨hs.1, hs.2.trans hv.2⟩)
    (fun s hs => hsmall s ⟨hs.1, hs.2.trans hv.2⟩)).1
  exact hc.trans (mul_le_of_le_one_left (hmu v hmem) (by linarith only [hδ.2]))

end EmcsfAcExtension.Global.Annulus
