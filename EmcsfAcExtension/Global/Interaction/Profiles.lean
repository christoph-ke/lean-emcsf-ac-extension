module

public import EmcsfAcExtension.Global.Defs.Interaction
public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Domains
public import EmcsfAcExtension.Local.Defs.Params
import EmcsfAcExtension.Local.Calculus.RelativeCharge
import EmcsfAcExtension.Local.Calculus.Sections
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Global.Calculus.Normalized
import EmcsfAcExtension.Infra.AC.Variation
import EmcsfAcExtension.Infra.AC.Quotient

/-! # Scalar profiles on stopped outgoing rows

The identities use the original outgoing label, so radial integrals carry
their Jacobian `λ`. All bounds supplied by the stopped construction remain
explicit. Source: `charged_SF_new_version.tex:L3284–L3324`, L3362–L3365.
-/

public section

open Set MeasureTheory Filter Complex

namespace EmcsfAcExtension.Global

/-- [def-node eq:ct-zeta]
The existing local charged scale at label length `2 R₀` is exactly the
dimensionless entry scale of charged_SF_new_version.tex:L3362–L3365. -/
theorem ct_zeta (e M₀ R₀ : ℝ) :
    Local.sigma e M₀ (2 * R₀) = e ^ 2 * M₀ ^ 2 * R₀ ^ 2 := by
  simp [Local.sigma]

namespace Interaction

/-- [internal]
Solve the frozen definition of `jOut` for the ordinary outgoing derivative.
This identity is pointwise, even where Lean's total derivative is zero. -/
theorem deriv_a_eq_weightedJ (S : Fields) (u v : ℝ)
    (hl : S.lam u v ≠ 0) (hg : 1 - S.mu u v ≠ 0) :
    deriv (S.a u) v = weightedJ S u v / (S.lam u v : ℂ) +
      (S.lam u v / S.r u v * ‖S.theta u v / S.lam u v‖ ^ 2 : ℝ) *
        (S.theta u v / S.lam u v) := by
  have hlC : (S.lam u v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl
  have hgC : (1 - S.mu u v : ℂ) ≠ 0 := by exact_mod_cast hg
  dsimp [weightedJ, jOut]
  push_cast
  field_simp
  ring

/-- [node sec:charged-terminal-interaction#row-variation-envelope]
The outgoing variation estimate at charged_SF_new_version.tex:L3298–L3303, in null labels.
The only constant is the explicit lower expansion bound `c⁻¹`. The envelope
is a bound on the frozen row density; representative agreement is discharged
by the renormalized packet before this theorem is used on generated envelopes. -/
theorem row_variation_envelope {e c : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) (hc : 0 < c)
    (hl : ∀ v ∈ Icc a b, c ≤ S.lam u v) (g : ℝ → ℝ)
    (hg : IntervalIntegrable g volume a b)
    (hmajor : ∀ᵐ v ∂volume.restrict (Icc a b), ‖weightedJ S u v‖ ≤ g v) :
    (eVariationOn (S.a u) (Icc a b)).toReal ≤ c⁻¹ * (∫ v in a..b, g v) +
      ∫ v in a..b, S.lam u v / S.r u v * ‖S.theta u v / S.lam u v‖ ^ 3 := by
  have ha := (hS.ac_out u a b hab hs).2.2.2.2
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have ct := Calculus.continuousOn_out_section hS.cont_theta hs
  have hp (v : ℝ) (hv : v ∈ Icc a b) : (u, v) ∈ D := hs ⟨rfl, hv⟩
  have hr (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.r u v :=
    hS.r_pos (u, v) (hp v hv) (hua.trans_le hv.1)
  have cy := ct.div (continuous_ofReal.comp_continuousOn cl)
    (fun v hv => Complex.ofReal_ne_zero.mpr (hS.lam_pos (u, v) (hp v hv)).ne')
  have ic : IntervalIntegrable (fun v => S.lam u v / S.r u v *
      ‖S.theta u v / S.lam u v‖ ^ 3) volume a b :=
    ((cl.div cr (fun v hv => (hr v hv).ne')).mul (cy.norm.pow 3)).intervalIntegrable_of_Icc hab
  have hineq : ∀ᵐ v ∂volume.restrict (Icc a b), ‖deriv (S.a u) v‖ ≤
      c⁻¹ * g v + S.lam u v / S.r u v * ‖S.theta u v / S.lam u v‖ ^ 3 := by
    filter_upwards [hmajor, ae_restrict_mem measurableSet_Icc] with v hv hmem
    have hlp := hS.lam_pos (u, v) (hp v hmem)
    rw [deriv_a_eq_weightedJ S u v hlp.ne' (hS.one_sub_mu_pos (u, v) (hp v hmem)).ne']
    calc
      _ ≤ ‖weightedJ S u v / (S.lam u v : ℂ)‖ +
          ‖(S.lam u v / S.r u v * ‖S.theta u v / S.lam u v‖ ^ 2 : ℝ) *
            (S.theta u v / S.lam u v)‖ := norm_add_le _ _
      _ ≤ c⁻¹ * g v + S.lam u v / S.r u v * ‖S.theta u v / S.lam u v‖ ^ 3 := by
        apply add_le_add
        · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlp]
          calc
            _ ≤ g v / S.lam u v := div_le_div_of_nonneg_right hv hlp.le
            _ ≤ g v / c := div_le_div_of_nonneg_left ((norm_nonneg _).trans hv) hc (hl v hmem)
            _ = _ := by ring
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg (div_nonneg hlp.le (hr v hmem).le) (sq_nonneg _))]
          exact le_of_eq (by ring)
  rw [ha.toReal_eVariationOn_eq_integral_norm_deriv hab]
  have hle := intervalIntegral.integral_mono_ae_restrict hab
    ha.intervalIntegrable_deriv_complex.norm ((hg.const_mul c⁻¹).add ic) hineq
  rwa [intervalIntegral.integral_add (hg.const_mul c⁻¹) ic,
    intervalIntegral.integral_const_mul] at hle

/-- [internal]
The scaled-amplitude form of relative charge at charged_SF_new_version.tex:L3284–L3291.
The exact coefficient is `e² / δ`; `A` bounds `r ‖φ‖` on the complete
core, rather than bounding `φ`. The late-gap and amplitude consumers supply
`hgap` and `hamp`; these are not original-data premises. -/
theorem relative_charge_amplitude_application_of_bound
    {e δ A : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u < v)
    (hs : outSeg u u v ⊆ D) (hδ : 0 < δ)
    (hgap : ∀ s ∈ Icc u v, δ ≤ 1 - S.mu u s)
    (hamp : ∀ s ∈ Icc u v, S.r u s * ‖S.phi u s‖ ≤ A) :
    S.Q u v ^ 2 / S.r u v ^ 2 ≤ (e ^ 2 / δ) * A ^ 2 * S.mu u v := by
  have hp (s : ℝ) (hx : s ∈ Icc u v) : (u, s) ∈ D := hs ⟨rfl, hx⟩
  have hr (s : ℝ) (hx : s ∈ Icc u v) : 0 ≤ S.r u s := by
    rcases hx.1.eq_or_lt with h | h
    · subst s
      rw [(hS.axis u (hp u ⟨le_rfl, huv.le⟩)).1]
    · exact (hS.r_pos (u, s) (hp s hx) h).le
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cp := Calculus.continuousOn_out_section hS.cont_phi hs
  have cg : ContinuousOn (fun s => 1 - S.mu u s) (Icc u v) :=
    continuousOn_const.sub (Local.continuousOn_mu_out hS huv hs)
  have iB : IntervalIntegrable (fun s => S.lam u s * S.r u s ^ 2 *
      ‖S.phi u s‖ ^ 2 / (1 - S.mu u s)) volume u v :=
    ContinuousOn.intervalIntegrable_of_Icc huv.le
      (((cl.mul (cr.pow 2)).mul (cp.norm.pow 2)).div cg
        (fun s hx => (hδ.trans_le (hgap s hx)).ne'))
  have iC : IntervalIntegrable (fun s => S.lam u s * (A ^ 2 / δ)) volume u v :=
    (cl.mul continuousOn_const).intervalIntegrable_of_Icc huv.le
  have hA : 0 ≤ A := (mul_nonneg (hr u ⟨le_rfl, huv.le⟩)
    (norm_nonneg _)).trans (hamp u ⟨le_rfl, huv.le⟩)
  have hB := intervalIntegral.integral_mono_on huv.le iB iC (fun s hx => by
    have hsq := (sq_le_sq₀ (mul_nonneg (hr s hx) (norm_nonneg _)) hA).mpr (hamp s hx)
    rw [mul_pow] at hsq
    have hb := (div_le_div_of_nonneg_right hsq
      (hδ.trans_le (hgap s hx)).le).trans
      (div_le_div_of_nonneg_left (sq_nonneg A) hδ (hgap s hx))
    calc
      _ = S.lam u s * (S.r u s ^ 2 * ‖S.phi u s‖ ^ 2 / (1 - S.mu u s)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (hS.lam_pos (u, s) (hp s hx)).le)
  have rad := Local.integralForm_of_ac_of_interior_deriv huv.le
    (hS.ac_out u u v huv.le hs).1
    (fun s hx => Local.IsSolution.hasDerivAt_radius_out hS hs hx)
  rw [intervalIntegral.integral_mul_const, ← rad.2,
    (hS.axis u (hp u ⟨le_rfl, huv.le⟩)).1, sub_zero] at hB
  have hflux : 0 ≤ ∫ s in u..v, S.lam u s * (1 - S.mu u s) *
      ‖S.theta u s / S.lam u s‖ ^ 2 :=
    intervalIntegral.integral_nonneg huv.le (fun s hx =>
      mul_nonneg (mul_nonneg (hS.lam_pos (u, s) (hp s hx)).le
        (hS.one_sub_mu_pos (u, s) (hp s hx)).le) (sq_nonneg _))
  have hm := hflux.trans (Local.RelCharge.mass_controls_radial_flux hS huv hs)
  have hrv := hS.r_pos (u, v) (hp v ⟨huv.le, le_rfl⟩) huv
  have hmu : 0 ≤ S.mu u v := div_nonneg hm hrv.le
  have htotal := (Local.lem_relative_charge hS huv hs).trans
    (mul_le_mul_of_nonneg_left hB
      (mul_nonneg (mul_nonneg (sq_nonneg e) hmu) hrv.le))
  apply (div_le_iff₀ (sq_pos_of_pos hrv)).mpr
  calc
    _ ≤ _ := htotal
    _ = _ := by ring

/-- [internal]
The stopped relative-charge and mass bounds imply the exact interval for
the radial expansion coefficient (charged_SF_new_version.tex:L3277–L3283). There is
no constant beyond the displayed stop `ε`. -/
theorem radial_expansion_coefficient_of_stops
    {S : Fields} {D : Set (ℝ × ℝ)} {δ c Λ F ε : ℝ}
    (hstop : ExteriorStops S D δ c Λ F ε) {u v : ℝ} (hp : (u, v) ∈ D)
    (hgap : 0 < 1 - S.mu u v) :
    0 ≤ (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v) ∧
      (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v) ≤ ε := by
  obtain ⟨hm, _, _, _, _, hε, hq⟩ := hstop (u, v) hp
  constructor
  · exact div_nonneg (by linarith only [hm, hq]) hgap.le
  · exact (div_le_div_of_nonneg_right (sub_le_self _
      (div_nonneg (sq_nonneg _) (sq_nonneg _))) hgap.le).trans hε

/-- [node sec:charged-terminal-interaction#radial-scalar-primitive]
The exact radial scalar primitive in null labels, charged_SF_new_version.tex:L3304–L3309.
No derivative of `λ` or `θ` is assumed; their normalized combination is AC.
There are no constants. -/
theorem radial_scalar_primitive {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) :
    (S.r u b : ℂ) * (S.theta u b / S.lam u b) =
      (S.r u a : ℂ) * (S.theta u a / S.lam u a) +
        ∫ v in a..b, (S.r u v : ℂ) * deriv (S.a u) v := by
  have hout := Local.IsSolution.out_section hS hua hab hs
  have ha := (hS.ac_out u a b hab hs).2.2.2.2
  have hy := ha.sub hout.2.2.2.2.2.1.1
  have hprod := hout.1.1.ofReal.mul_normed_ring hy
  have hd : ∀ᵐ v ∂volume.restrict (Icc a b),
      deriv (fun v => (S.r u v : ℂ) * (S.a u v - S.phi u v)) v =
        (S.r u v : ℂ) * deriv (S.a u) v := by
    have hda := ae_restrict_of_ae (μ := volume) (s := Icc a b) ha.ae_differentiableAt_of_mem_uIcc
    filter_upwards [hout.1.2, hout.2.2.2.2.2.1.2, hda,
      ae_restrict_mem measurableSet_Icc] with v hrv hpv hav hv
    have hrv0 := (hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)).ne'
    have hd := hrv.ofReal_comp.mul
      ((hav (by simpa only [uIcc_of_le hab] using hv)).hasDerivAt.sub hpv)
    have hd' : HasDerivAt (fun x => (S.r u x : ℂ) * (S.a u x - S.phi u x))
        ((S.lam u v : ℂ) * (S.a u v - S.phi u v) +
          (S.r u v : ℂ) * (deriv (S.a u) v - S.phiV u v)) v := by
      simpa only [Pi.mul_apply, Pi.sub_apply] using! hd
    rw [hd'.deriv]
    dsimp [Fields.a, Fields.phiV]
    have hrC : (S.r u v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrv0
    have hlC : (S.lam u v : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).ne'
    field_simp [hrC, hlC]
    ring
  have hi := integralForm_of_ac_of_ae_deriv_eq hprod (by
    change ∀ᵐ v ∂volume.restrict (uIcc a b), _
    rw [uIcc_of_le hab]
    exact hd)
  have heq := hi.eq_add_integral
  simpa only [Pi.sub_apply, Fields.a, add_sub_cancel_left] using heq

/-- [node sec:charged-terminal-interaction#row-variation-absorption]
The scalar radial moment is at most its boundary value plus the outgoing
variation, charged_SF_new_version.tex:L3310–L3313. The constant one is universal.
The proof uses a positive real majorant of the exact scalar primitive. -/
theorem row_scalar_integral_le {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) :
    (∫ v in a..b, S.lam u v / S.r u v * ‖S.theta u v / S.lam u v‖) ≤
      ‖S.theta u a / S.lam u a‖ + (eVariationOn (S.a u) (Icc a b)).toReal := by
  let y := fun v => S.theta u v / (S.lam u v : ℂ)
  let H := fun x => S.r u a * ‖y a‖ + ∫ v in a..x, S.r u v * ‖deriv (S.a u) v‖
  let q := fun v => H v / S.r u v
  have hout := Local.IsSolution.out_section hS hua hab hs
  have ha := (hS.ac_out u a b hab hs).2.2.2.2
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have ct := Calculus.continuousOn_out_section hS.cont_theta hs
  have hp (v : ℝ) (hv : v ∈ Icc a b) : (u, v) ∈ D := hs ⟨rfl, hv⟩
  have hr (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.r u v :=
    hS.r_pos (u, v) (hp v hv) (hua.trans_le hv.1)
  have cy : ContinuousOn y (Icc a b) :=
    ct.div (continuous_ofReal.comp_continuousOn cl)
      (fun v hv => Complex.ofReal_ne_zero.mpr (hS.lam_pos (u, v) (hp v hv)).ne')
  have id := ha.intervalIntegrable_deriv_complex.norm
  have iH := id.continuousOn_mul (by simpa only [uIcc_of_le hab] using cr)
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => S.r u a * ‖y a‖) a b :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  have hH : AbsolutelyContinuousOnInterval H a b :=
    hconst.fun_add (iH.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)
  have hq : AbsolutelyContinuousOnInterval q a b :=
    Calculus.ac_div_of_ne_zero hH hout.1.1
      (fun v hv => (hr v (by simpa only [uIcc_of_le hab] using hv)).ne')
  have Hnonneg (v : ℝ) (hv : v ∈ Icc a b) : 0 ≤ H v :=
    add_nonneg (mul_nonneg (hr a ⟨le_rfl, hab⟩).le (norm_nonneg _))
      (intervalIntegral.integral_nonneg hv.1 (fun x hx =>
        mul_nonneg (hr x ⟨hx.1, hx.2.trans hv.2⟩).le (norm_nonneg _)))
  have hbound (v : ℝ) (hv : v ∈ Icc a b) : ‖y v‖ ≤ q v := by
    have hsv : outSeg u a v ⊆ D := fun p hp => hs ⟨hp.1, hp.2.1, hp.2.2.trans hv.2⟩
    have heq := radial_scalar_primitive hS hua hv.1 hsv
    have hnorm : ‖(S.r u a : ℂ) * (S.theta u a / S.lam u a) +
        ∫ x in a..v, (S.r u x : ℂ) * deriv (S.a u) x‖ ≤
        ‖(S.r u a : ℂ) * (S.theta u a / S.lam u a)‖ +
          ∫ x in a..v, ‖(S.r u x : ℂ) * deriv (S.a u) x‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl
        (intervalIntegral.norm_integral_le_integral_norm hv.1))
    have he : (∫ x in a..v, ‖(S.r u x : ℂ) * deriv (S.a u) x‖) =
        ∫ x in a..v, S.r u x * ‖deriv (S.a u) x‖ := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [uIcc_of_le hv.1] at hx
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hr x ⟨hx.1, hx.2.trans hv.2⟩)]
    rw [← heq, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (hr v hv),
      abs_of_pos (hr a ⟨le_rfl, hab⟩), he] at hnorm
    exact (le_div_iff₀ (hr v hv)).mpr (by simpa only [y, H, mul_comm] using hnorm)
  have iq : IntervalIntegrable (fun v => S.lam u v / S.r u v * q v) volume a b :=
    ((cl.div cr (fun v hv => (hr v hv).ne')).mul
      (by simpa only [uIcc_of_le hab] using hq.continuousOn)).intervalIntegrable_of_Icc hab
  have iy : IntervalIntegrable (fun v => S.lam u v / S.r u v * ‖y v‖) volume a b :=
    ((cl.div cr (fun v hv => (hr v hv).ne')).mul cy.norm).intervalIntegrable_of_Icc hab
  have hder : ∀ᵐ v ∂volume.restrict (Icc a b),
      deriv q v = ‖deriv (S.a u) v‖ - S.lam u v / S.r u v * q v := by
    have hi := ae_restrict_of_ae (μ := volume) (s := Icc a b) iH.ae_hasDerivAt_integral
    filter_upwards [hi, hout.1.2, ae_restrict_mem measurableSet_Icc] with v hv hrv hmem
    have hdH : HasDerivAt H (S.r u v * ‖deriv (S.a u) v‖) v :=
      (hv (by simpa only [uIcc_of_le hab] using hmem) a left_mem_uIcc).const_add _
    have hdq : HasDerivAt q
        ((S.r u v * ‖deriv (S.a u) v‖ * S.r u v - H v * S.lam u v) / S.r u v ^ 2) v := by
      simpa only [q, Pi.div_apply] using! hdH.div hrv (hr v hmem).ne'
    rw [hdq.deriv]
    dsimp [q]
    field_simp [(hr v hmem).ne']
  have hftc := integralForm_of_ac_of_ae_deriv_eq hq (by
    change ∀ᵐ v ∂volume.restrict (uIcc a b), _
    rw [uIcc_of_le hab]
    exact hder)
  have heq := hftc.2
  rw [intervalIntegral.integral_sub id iq] at heq
  have hqa : q a = ‖y a‖ := by
    dsimp [q, H]
    rw [intervalIntegral.integral_same, add_zero, mul_div_cancel_left₀ _ (hr a ⟨le_rfl, hab⟩).ne']
  have hqb : 0 ≤ q b := div_nonneg (Hnonneg b ⟨hab, le_rfl⟩) (hr b ⟨hab, le_rfl⟩).le
  have hle := intervalIntegral.integral_mono_on hab iy iq (fun v hv =>
    mul_le_mul_of_nonneg_left (hbound v hv)
      (div_nonneg (hS.lam_pos (u, v) (hp v hv)).le (hr v hv).le))
  rw [ha.toReal_eVariationOn_eq_integral_norm_deriv hab]
  rw [hqa] at heq
  dsimp only [y] at heq hle
  linarith only [hle, heq, hqb]

/-- [node sec:charged-terminal-interaction#row-variation-absorption]
Absorption of the cubic correction, charged_SF_new_version.tex:L3314–L3316.
Both coefficients are explicit; the envelope and all field stops hold only
on the supplied outgoing row. -/
theorem row_variation_absorption {e c F : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) (hc : 0 < c) (hF : 0 ≤ F)
    (hl : ∀ v ∈ Icc a b, c ≤ S.lam u v)
    (hy : ∀ v ∈ Icc a b, ‖S.theta u v / S.lam u v‖ ≤ F)
    (g : ℝ → ℝ) (hg : IntervalIntegrable g volume a b)
    (hmajor : ∀ᵐ v ∂volume.restrict (Icc a b), ‖weightedJ S u v‖ ≤ g v) :
    (1 - F ^ 2) * (eVariationOn (S.a u) (Icc a b)).toReal ≤
      c⁻¹ * (∫ v in a..b, g v) + F ^ 2 * ‖S.theta u a / S.lam u a‖ := by
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have ct := Calculus.continuousOn_out_section hS.cont_theta hs
  have hr (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.r u v :=
    hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have cy := ct.div (continuous_ofReal.comp_continuousOn cl)
    (fun v hv => Complex.ofReal_ne_zero.mpr (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).ne')
  have cw := cl.div cr (fun v hv => (hr v hv).ne')
  have i3 := (cw.mul (cy.norm.pow 3)).intervalIntegrable_of_Icc hab (μ := volume)
  have i1 := (cw.mul cy.norm).intervalIntegrable_of_Icc hab (μ := volume)
  have hcube := intervalIntegral.integral_mono_on hab i3 (i1.const_mul (F ^ 2))
    (fun v hv => by
      have hw : 0 ≤ S.lam u v / S.r u v :=
        div_nonneg (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).le (hr v hv).le
      have hsq := (sq_le_sq₀ (norm_nonneg _) hF).mpr (hy v hv)
      have hmul := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hsq (norm_nonneg (S.theta u v / S.lam u v))) hw
      dsimp only [Pi.mul_apply, Pi.pow_apply, Pi.div_apply, Function.comp_def]
      convert hmul using 1 <;> ring)
  rw [intervalIntegral.integral_const_mul] at hcube
  dsimp only [Pi.mul_apply, Pi.pow_apply, Pi.div_apply, Function.comp_def] at hcube
  have hrow := row_variation_envelope hS hua hab hs hc hl g hg hmajor
  have hscalar := mul_le_mul_of_nonneg_left (row_scalar_integral_le hS hua hab hs) (sq_nonneg F)
  linarith only [hrow, hcube, hscalar]

end Interaction

/-- [internal]
The scalar bound `eq:ct-M0` (charged_SF_new_version.tex:L3317–L3324) on a stopped row,
with a supplied bound `B` for its terminal scalar. The closure consumer
supplies `B` from the terminal annulus supremum, and supplies the envelope
and `J ≤ Jstop` from its finite stopped construction. No core scalar bound
is used. All coefficients are the displayed stopping parameters. -/
theorem ct_m0_of_row_envelope {e c F Jstop B : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) (hc : 0 < c) (hF : 0 ≤ F) (hF1 : F < 1)
    (hl : ∀ v ∈ Icc a b, c ≤ S.lam u v)
    (hy : ∀ v ∈ Icc a b, ‖S.theta u v / S.lam u v‖ ≤ F)
    (hB : ‖S.phi u b‖ ≤ B) (g : ℝ → ℝ) (hg : IntervalIntegrable g volume a b)
    (hmajor : ∀ᵐ v ∂volume.restrict (Icc a b), ‖weightedJ S u v‖ ≤ g v)
    (hJ : (∫ v in a..b, g v) ≤ Jstop) :
    ∀ v ∈ Icc a b, ‖S.phi u v‖ ≤ 1 + B + (F + c⁻¹ * Jstop) / (1 - F ^ 2) := by
  have ha := (hS.ac_out u a b hab hs).2.2.2.2
  have hvar := Interaction.row_variation_absorption hS hua hab hs hc hF hl hy g hg hmajor
  have hinc := mul_le_mul_of_nonneg_left hJ (inv_nonneg.mpr hc.le)
  have hya := mul_le_mul_of_nonneg_left (hy a ⟨le_rfl, hab⟩) (sq_nonneg F)
  have hp : 0 < 1 - F ^ 2 := by nlinarith only [hF1, hF, sq_nonneg (F - 1)]
  have hvar' : (eVariationOn (S.a u) (Icc a b)).toReal ≤
      (c⁻¹ * Jstop + F ^ 3) / (1 - F ^ 2) := by
    apply (le_div_iff₀ hp).mpr
    nlinarith only [hvar, hinc, hya]
  intro v hv
  have hdist := ha.boundedVariationOn_Icc hab |>.dist_le hv (show b ∈ Icc a b from ⟨hab, le_rfl⟩)
  rw [dist_eq_norm] at hdist
  have heq : S.phi u v = S.phi u b + (S.a u v - S.a u b) +
      (S.theta u b / S.lam u b - S.theta u v / S.lam u v) := by
    dsimp [Fields.a]
    ring
  have hnorm : ‖S.phi u v‖ ≤ B + (eVariationOn (S.a u) (Icc a b)).toReal + 2 * F := by
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add hB hdist))
      ((norm_sub_le _ _).trans (by linarith only [hy b ⟨hab, le_rfl⟩, hy v hv])))
  have hlast : (c⁻¹ * Jstop + F ^ 3) / (1 - F ^ 2) + 2 * F ≤
      1 + (F + c⁻¹ * Jstop) / (1 - F ^ 2) := by
    have heq : (c⁻¹ * Jstop + F ^ 3) / (1 - F ^ 2) + 2 * F =
        (1 + (F + c⁻¹ * Jstop) / (1 - F ^ 2)) - (1 - F) := by
      field_simp
      ring
    rw [heq]
    exact sub_le_self _ (sub_nonneg.mpr hF1.le)
  linarith only [hnorm, hvar', hlast]

namespace Interaction

/-- [internal]
The literal scaled-amplitude supremum in charged_SF_new_version.tex:L3284–L3291.
The coefficient is exactly `e² / δ`, uniformly over the complete cone.
The late-gap consumer supplies the full-core gap. -/
theorem relative_charge_amplitude_application_of_gap
    {e δ : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u < v) (hs : outSeg u u v ⊆ D)
    (hδ : 0 < δ) (hgap : ∀ s ∈ Icc u v, δ ≤ 1 - S.mu u s) :
    S.Q u v ^ 2 / S.r u v ^ 2 ≤ (e ^ 2 / δ) *
      (sSup ((fun s => S.r u s * ‖S.phi u s‖) '' Ioc u v)) ^ 2 * S.mu u v := by
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cp := Calculus.continuousOn_out_section hS.cont_phi hs
  have cf : ContinuousOn (fun s => S.r u s * ‖S.phi u s‖) (Icc u v) := by
    simpa only [Pi.mul_apply] using! cr.mul cp.norm
  have hb : BddAbove ((fun s => S.r u s * ‖S.phi u s‖) '' Ioc u v) :=
    (isCompact_Icc.image_of_continuousOn cf).bddAbove.mono (Set.image_mono Ioc_subset_Icc_self)
  apply relative_charge_amplitude_application_of_bound hS huv hs hδ hgap
  intro s hx
  rcases hx.1.eq_or_lt with hsu | hsu
  · subst s
    rw [(hS.axis u (hs ⟨rfl, le_rfl, huv.le⟩)).1, zero_mul]
    exact (mul_nonneg (hS.r_pos (u, v) (hs ⟨rfl, huv.le, le_rfl⟩) huv).le
      (norm_nonneg _)).trans (le_csSup hb ⟨v, ⟨huv, le_rfl⟩, rfl⟩)
  · exact le_csSup hb ⟨s, ⟨hsu, hx.2⟩, rfl⟩

/-- [internal]
The late smallness consequence of `CTI#relative-charge-amplitude-application`,
charged_SF_new_version.tex:L3292–L3293. The late entry may depend on the fixed solution
and coupling. The consumer supplies the late global gap and the vanishing
scaled amplitude from the gap and amplitude packets; no profile is added
to the original datum. -/
theorem relative_charge_small_of_late_bounds {ui e δ a : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hδ : 0 < δ) (ha : a ∈ Ioo ui 0)
    (hgap : ∀ p ∈ origDomain ui, a ≤ p.1 → δ ≤ 1 - S.mu p.1 p.2)
    (hsmall : ∀ η : ℝ, 0 < η → ∃ b ∈ Ioo ui 0,
      ∀ p ∈ origDomain ui, b ≤ p.1 → S.r p.1 p.2 * ‖S.phi p.1 p.2‖ ≤ η) :
    ∃ u₀ ∈ Ioo ui 0, ∀ p ∈ origDomain ui, u₀ ≤ p.1 →
      S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 ≤ S.mu p.1 p.2 / 2 := by
  let η := Real.sqrt (δ / 2) / (|e| + 1)
  have he : 0 < |e| + 1 := by positivity
  have hη : 0 < η := div_pos (Real.sqrt_pos.mpr (by positivity : 0 < δ / 2)) he
  obtain ⟨b, hb, hamp⟩ := hsmall η hη
  have hcoef : e ^ 2 / δ * η ^ 2 ≤ (1 / 2 : ℝ) := by
    have hq : 0 ≤ |e| / (|e| + 1) := div_nonneg (abs_nonneg e) he.le
    have hq1 : |e| / (|e| + 1) ≤ 1 := (div_le_one he).mpr (by linarith only [abs_nonneg e])
    have hsq := pow_le_pow_left₀ hq hq1 2
    have heq : e ^ 2 / δ * η ^ 2 = (|e| / (|e| + 1)) ^ 2 / 2 := by
      dsimp [η]
      rw [div_pow, Real.sq_sqrt (by positivity : 0 ≤ δ / 2), div_pow, sq_abs]
      field_simp [hδ.ne', he.ne']
    rw [heq]
    nlinarith only [hsq]
  refine ⟨max a b, ⟨ha.1.trans_le (le_max_left _ _), max_lt ha.2 hb.2⟩, ?_⟩
  intro p hp hlate
  have hap := (le_max_left a b).trans hlate
  have hbp := (le_max_right a b).trans hlate
  rcases hp.2.2.1.eq_or_lt with heq | huv
  · have hp' : (p.1, p.1) ∈ origDomain ui := ⟨hp.1, hp.2.1, le_rfl, hp.2.1.le⟩
    have haxis := h.solution.axis p.1 hp'
    rw [← heq]
    simp [Fields.mu, haxis.1, haxis.2.2.1]
  · have hs : outSeg p.1 p.1 p.2 ⊆ origDomain ui := by
      intro q hq
      rcases q with ⟨x, y⟩
      rcases hq with ⟨rfl, hy⟩
      exact ⟨hp.1, hp.2.1, hy.1, hy.2.trans hp.2.2.2⟩
    have hc := relative_charge_amplitude_application_of_bound h.solution huv hs hδ
      (fun x hx => hgap (p.1, x) (hs ⟨rfl, hx⟩) hap)
      (fun x hx => hamp (p.1, x) (hs ⟨rfl, hx⟩) hbp)
    exact hc.trans (by
      have hm := mul_le_mul_of_nonneg_right hcoef (h.mu p hp).1
      simpa only [one_div, inv_mul_eq_div] using hm)

/-- [internal]
The scalar profile on the entire stopped exterior in the conditional form
of internal project record. The closure consumer supplies the row geometry, the
terminal annulus bound `B`, and the finite derivative envelope with its
budget. The renormalized packet identifies the generated representative
with the frozen row density before supplying `hmajor`. No scalar profile
is assumed. All coefficients are the displayed fixed stops. -/
theorem scalar_profile_of_stops {ui e u₀ u₁ v₀ δ c Λ F ε Jstop B : ℝ}
    {S : Fields} {vb g : ℝ → ℝ} (h : OriginalData ui e S) (hc : 0 < c)
    (hF : 0 ≤ F) (hF1 : F < 1)
    (hrow : ∀ u ∈ Icc u₀ u₁, ui ≤ u ∧ u < vb u ∧ vb u ≤ 0 ∧ v₀ ≤ vb u)
    (hstop : ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F ε)
    (hB : ∀ u ∈ Icc u₀ u₁, ‖S.phi u 0‖ ≤ B)
    (hg : IntegrableOn g (Icc v₀ 0))
    (hg0 : ∀ᵐ v ∂volume.restrict (Icc v₀ 0), 0 ≤ g v)
    (hmajor : ∀ u ∈ Icc u₀ u₁, ∀ᵐ v ∂volume.restrict (Icc v₀ 0),
      vb u ≤ v → ‖weightedJ S u v‖ ≤ g v)
    (hJ : (∫ v in v₀..0, g v) ≤ Jstop) :
    ∀ p ∈ exteriorDomain ui u₀ u₁ vb,
      ‖S.phi p.1 p.2‖ ≤ 1 + B + (F + c⁻¹ * Jstop) / (1 - F ^ 2) := by
  intro ⟨u, v⟩ hp
  have hu : u ∈ Icc u₀ u₁ := ⟨hp.2.1, hp.2.2.1⟩
  obtain ⟨hui, hub, hb0, hvb⟩ := hrow u hu
  have hv0 : v₀ ≤ 0 := hvb.trans hb0
  have hseg : outSeg u (vb u) 0 ⊆ origDomain ui := by
    intro p hseg
    rcases p with ⟨x, y⟩
    rcases hseg with ⟨rfl, hy⟩
    exact ⟨hui, hub.trans_le hb0, hub.le.trans hy.1, hy.2⟩
  have hmem (x : ℝ) (hx : x ∈ Icc (vb u) 0) : (u, x) ∈ exteriorDomain ui u₀ u₁ vb :=
    ⟨hseg ⟨rfl, hx⟩, hu.1, hu.2, hx.1⟩
  have ig : IntervalIntegrable g volume v₀ 0 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hv0).mpr hg
  have igr := ig.mono_set (uIcc_subset_uIcc (Icc_subset_uIcc ⟨hvb, hb0⟩) right_mem_uIcc)
  have igl := ig.mono_set (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc ⟨hvb, hb0⟩))
  have hnonneg : ∀ᵐ x ∂volume.restrict (Icc v₀ (vb u)), 0 ≤ g x := by
    have he := (ae_restrict_iff' measurableSet_Icc).mp hg0
    filter_upwards [ae_restrict_of_ae (μ := volume) (s := Icc v₀ (vb u)) he,
      ae_restrict_mem measurableSet_Icc] with x hx hmem
    exact hx ⟨hmem.1, hmem.2.trans hb0⟩
  have hleft : 0 ≤ ∫ x in v₀..vb u, g x := by
    rw [intervalIntegral.integral_of_le hvb, ← integral_Icc_eq_integral_Ioc]
    exact integral_nonneg_of_ae hnonneg
  have hsum := intervalIntegral.integral_add_adjacent_intervals igl igr
  have hJrow : (∫ x in vb u..0, g x) ≤ Jstop := by linarith only [hleft, hsum, hJ]
  have hmaj : ∀ᵐ x ∂volume.restrict (Icc (vb u) 0), ‖weightedJ S u x‖ ≤ g x := by
    have he := (ae_restrict_iff' measurableSet_Icc).mp (hmajor u hu)
    filter_upwards [ae_restrict_of_ae (μ := volume) (s := Icc (vb u) 0) he,
      ae_restrict_mem measurableSet_Icc] with x hx hmem
    exact hx ⟨hvb.trans hmem.1, hmem.2⟩ hmem.1
  exact ct_m0_of_row_envelope h.solution hub hb0 hseg hc hF hF1
    (fun x hx => (hstop (u, x) (hmem x hx)).2.2.1)
    (fun x hx => (hstop (u, x) (hmem x hx)).2.2.2.2.1)
    (hB u hu) g igr hmaj hJrow v ⟨hp.2.2.2, hp.1.2.2.2⟩

end Interaction

end EmcsfAcExtension.Global
